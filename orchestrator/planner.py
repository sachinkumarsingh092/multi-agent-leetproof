"""Small, human-reviewed planner for multi-method POC jobs."""

from __future__ import annotations

import hashlib
import heapq
import importlib
import json
import re
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Any, cast

from langchain_core.messages import AIMessage, BaseMessage, HumanMessage, SystemMessage

from .manifest import JobManifest, load_manifest


PLAN_SCHEMA_VERSION = 1
_ID_PATTERN = re.compile(r"^[A-Za-z][A-Za-z0-9_-]*$")
_SHA256_PATTERN = re.compile(r"^[0-9a-f]{64}$")
_PLANNER_PROMPT = """You decompose a small programming project into isolated,
single-method LeetProof tasks.

Return only one JSON object with this shape:
{
  "tasks": [
    {
      "id": "lowercase-kebab-id",
      "depends_on": [],
      "specification": "=== TASK_DESCRIPTION ===\\n...\\n=== METHOD_SIGNATURE ===\\nmethod ...\\n=== TEST_CASES ===\\n{...}"
    }
  ]
}

Rules:
- Produce between 2 and 8 tasks.
- Cover every requested method exactly once.
- Each specification must be self-contained and contain exactly one method.
- Use only primitive Lean-friendly values for this POC: Nat, Int, Bool, String,
  Array, List, Option and tuples of those values.
- Do not create shared mutable state, classes, networking or persistence.
- Add a dependency only when implementation order truly requires it. Prefer
  independent tasks for this POC.
- Dependencies must reference task IDs from the same response and must be acyclic.
- Include precise preconditions, edge cases, determinism and concrete test cases.
- Do not use Markdown fences around the JSON response.
"""


class PlanError(ValueError):
    """Raised when a proposed or reviewed project plan is invalid."""


def _validate_requirements(text: str) -> None:
    requirements = importlib.import_module("requirements")
    requirements.validate_requirements(text)


@dataclass(frozen=True)
class PlanTask:
    id: str
    input_file: Path
    input_relative: PurePosixPath
    output_file: PurePosixPath
    depends_on: tuple[str, ...]


@dataclass(frozen=True)
class ProjectPlan:
    schema_version: int
    project_id: str
    plan_file: Path
    source_file: Path
    source_sha256: str
    tasks: tuple[PlanTask, ...]

    def execution_order(self) -> tuple[PlanTask, ...]:
        tasks_by_id = {task.id: task for task in self.tasks}
        indegree = {task.id: len(task.depends_on) for task in self.tasks}
        dependents = {task.id: [] for task in self.tasks}
        for task in self.tasks:
            for dependency in task.depends_on:
                dependents[dependency].append(task.id)

        ready = [task_id for task_id, count in indegree.items() if count == 0]
        heapq.heapify(ready)
        ordered: list[PlanTask] = []
        while ready:
            task_id = heapq.heappop(ready)
            ordered.append(tasks_by_id[task_id])
            for dependent in sorted(dependents[task_id]):
                indegree[dependent] -= 1
                if indegree[dependent] == 0:
                    heapq.heappush(ready, dependent)
        if len(ordered) != len(self.tasks):
            cyclic = sorted(
                task_id for task_id, count in indegree.items() if count > 0
            )
            raise PlanError(
                "Plan dependency graph contains a cycle involving: "
                + ", ".join(cyclic)
            )
        return tuple(ordered)


def _identifier(value: Any, field: str) -> str:
    if not isinstance(value, str) or not _ID_PATTERN.fullmatch(value):
        raise PlanError(
            f"{field} must start with a letter and contain only letters, "
            "numbers, '_' or '-'"
        )
    return value


def _relative_path(value: Any, field: str, suffix: str) -> PurePosixPath:
    if not isinstance(value, str) or not value or "\\" in value:
        raise PlanError(f"{field} must be a non-empty POSIX path")
    path = PurePosixPath(value)
    if path.is_absolute() or ".." in path.parts:
        raise PlanError(f"{field} must stay within the plan directory")
    if path.suffix != suffix:
        raise PlanError(f"{field} must end with {suffix}")
    return path


def _exact_keys(
    value: dict[str, Any],
    *,
    required: set[str],
    context: str,
) -> None:
    missing = sorted(required - value.keys())
    unknown = sorted(value.keys() - required)
    if missing:
        raise PlanError(f"{context} is missing fields: {', '.join(missing)}")
    if unknown:
        raise PlanError(f"{context} has unknown fields: {', '.join(unknown)}")


def _resolve_file(
    plan_directory: Path,
    relative: PurePosixPath,
    field: str,
) -> Path:
    path = (plan_directory / Path(*relative.parts)).resolve()
    if not path.is_relative_to(plan_directory):
        raise PlanError(f"{field} resolves outside the plan directory")
    if not path.is_file():
        raise PlanError(f"{field} does not exist: {relative}")
    return path


def load_plan(plan_file: str | Path) -> ProjectPlan:
    """Load and validate a human-reviewed plan and its task specifications."""
    path = Path(plan_file).resolve()
    if not path.is_file():
        raise PlanError(f"Plan file does not exist: {path}")
    try:
        raw = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as error:
        raise PlanError(f"Plan is not valid JSON: {error}") from error
    if not isinstance(raw, dict):
        raise PlanError("Plan root must be an object")
    _exact_keys(
        raw,
        required={
            "schema_version",
            "project_id",
            "source_file",
            "source_sha256",
            "tasks",
        },
        context="plan",
    )
    version = raw["schema_version"]
    if (
        not isinstance(version, int)
        or isinstance(version, bool)
        or version != PLAN_SCHEMA_VERSION
    ):
        raise PlanError(f"Unsupported plan schema_version: {version}")

    project_id = _identifier(raw["project_id"], "project_id")
    directory = path.parent
    source_relative = _relative_path(raw["source_file"], "source_file", ".txt")
    source_file = _resolve_file(directory, source_relative, "source_file")
    source_sha256 = raw["source_sha256"]
    if (
        not isinstance(source_sha256, str)
        or not _SHA256_PATTERN.fullmatch(source_sha256)
    ):
        raise PlanError("source_sha256 must be a lowercase SHA-256 digest")
    if hashlib.sha256(source_file.read_bytes()).hexdigest() != source_sha256:
        raise PlanError("source_sha256 does not match source_file")

    raw_tasks = raw["tasks"]
    if not isinstance(raw_tasks, list) or not 1 <= len(raw_tasks) <= 8:
        raise PlanError("tasks must contain between 1 and 8 entries")
    tasks: list[PlanTask] = []
    for index, raw_task in enumerate(raw_tasks):
        context = f"tasks[{index}]"
        if not isinstance(raw_task, dict):
            raise PlanError(f"{context} must be an object")
        raw_task = cast(dict[str, Any], raw_task)
        _exact_keys(
            raw_task,
            required={"id", "input_file", "output_file", "depends_on"},
            context=context,
        )
        task_id = _identifier(raw_task["id"], f"{context}.id")
        input_relative = _relative_path(
            raw_task["input_file"], f"{context}.input_file", ".txt"
        )
        output_file = _relative_path(
            raw_task["output_file"], f"{context}.output_file", ".lean"
        )
        dependencies = raw_task["depends_on"]
        if not isinstance(dependencies, list):
            raise PlanError(f"{context}.depends_on must be an array")
        depends_on = tuple(
            _identifier(dependency, f"{context}.depends_on")
            for dependency in dependencies
        )
        if len(depends_on) != len(set(depends_on)):
            raise PlanError(f"{context}.depends_on contains duplicates")
        if task_id in depends_on:
            raise PlanError(f"{context} cannot depend on itself")
        input_file = _resolve_file(
            directory, input_relative, f"{context}.input_file"
        )
        try:
            _validate_requirements(input_file.read_text(encoding="utf-8"))
        except ValueError as error:
            raise PlanError(f"{context}.input_file is invalid: {error}") from error
        tasks.append(
            PlanTask(
                id=task_id,
                input_file=input_file,
                input_relative=input_relative,
                output_file=output_file,
                depends_on=depends_on,
            )
        )

    task_ids = [task.id for task in tasks]
    if len(task_ids) != len(set(task_ids)):
        raise PlanError("Task IDs must be unique")
    outputs = [str(task.output_file).casefold() for task in tasks]
    if len(outputs) != len(set(outputs)):
        raise PlanError("Task output_file values must be unique")
    known_ids = set(task_ids)
    for task in tasks:
        unknown = sorted(set(task.depends_on) - known_ids)
        if unknown:
            raise PlanError(
                f"Task {task.id} has unknown dependencies: {', '.join(unknown)}"
            )

    plan = ProjectPlan(
        schema_version=version,
        project_id=project_id,
        plan_file=path,
        source_file=source_file,
        source_sha256=source_sha256,
        tasks=tuple(tasks),
    )
    plan.execution_order()
    return plan


def compile_plan(
    plan_file: str | Path,
    *,
    manifest_name: str = "job.json",
) -> JobManifest:
    """Freeze reviewed task contents into the existing hashed job manifest."""
    plan = load_plan(plan_file)
    payload = {
        "schema_version": 1,
        "job_id": plan.project_id,
        "tasks": [
            {
                "id": task.id,
                "input_file": str(task.input_relative),
                "input_sha256": hashlib.sha256(task.input_file.read_bytes()).hexdigest(),
                "output_file": str(task.output_file),
                "depends_on": list(task.depends_on),
            }
            for task in plan.tasks
        ],
    }
    manifest_file = plan.plan_file.parent / manifest_name
    temporary = manifest_file.with_suffix(".tmp")
    temporary.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    temporary.replace(manifest_file)
    return load_manifest(manifest_file)


def _response_text(response: Any) -> str:
    if isinstance(response, AIMessage):
        content = response.content
    else:
        content = getattr(response, "content", response)
    if isinstance(content, str):
        return content
    if isinstance(content, list):
        return "\n".join(
            str(block.get("text", ""))
            for block in content
            if isinstance(block, dict) and block.get("type") == "text"
        )
    return str(content or "")


def _response_json(text: str) -> dict[str, Any]:
    fenced = re.fullmatch(r"\s*```(?:json)?\s*(.*?)```\s*", text, re.DOTALL)
    if fenced:
        text = fenced.group(1)
    try:
        value = json.loads(text)
    except json.JSONDecodeError as error:
        raise PlanError(f"Planner did not return valid JSON: {error}") from error
    if not isinstance(value, dict):
        raise PlanError("Planner response must be a JSON object")
    _exact_keys(value, required={"tasks"}, context="planner response")
    return value


def _module_name(task_id: str) -> str:
    parts = [part for part in re.split(r"[-_]+", task_id) if part]
    return "".join(part[:1].upper() + part[1:] for part in parts)


async def generate_plan(
    project_specification: str | Path,
    output_directory: str | Path,
    *,
    project_id: str,
    provider: str,
    model: str,
) -> ProjectPlan:
    """Ask one LLM to propose reviewable, single-method task files."""
    providers = importlib.import_module("providers")
    token_tracker = importlib.import_module("utils.token_tracker")

    source = Path(project_specification).resolve()
    if not source.is_file():
        raise PlanError(f"Project specification does not exist: {source}")
    project_id = _identifier(project_id, "project_id")
    source_text = source.read_text(encoding="utf-8").strip()
    if not source_text:
        raise PlanError("Project specification must not be empty")

    llm = providers.get_llm(
        providers.LLMConfig(provider=provider, model=model),
        providers.ReasoningLevel.LOW,
    )
    messages: list[BaseMessage] = [
        SystemMessage(content=_PLANNER_PROMPT),
        HumanMessage(content=source_text),
    ]
    token_tracker.check_limits_before_llm_call()
    token_tracker.set_current_agent("project_planner")
    response = await llm.ainvoke(messages)
    proposal = _response_json(_response_text(response))
    raw_tasks = proposal["tasks"]
    if not isinstance(raw_tasks, list) or not 2 <= len(raw_tasks) <= 8:
        raise PlanError("Planner must return between 2 and 8 tasks")

    normalized: list[dict[str, Any]] = []
    task_ids: list[str] = []
    for index, raw_task in enumerate(raw_tasks):
        context = f"planner tasks[{index}]"
        if not isinstance(raw_task, dict):
            raise PlanError(f"{context} must be an object")
        raw_task = cast(dict[str, Any], raw_task)
        _exact_keys(
            raw_task,
            required={"id", "depends_on", "specification"},
            context=context,
        )
        task_id = _identifier(raw_task["id"], f"{context}.id")
        dependencies = raw_task["depends_on"]
        if not isinstance(dependencies, list):
            raise PlanError(f"{context}.depends_on must be an array")
        depends_on = [
            _identifier(dependency, f"{context}.depends_on")
            for dependency in dependencies
        ]
        specification = raw_task["specification"]
        if not isinstance(specification, str):
            raise PlanError(f"{context}.specification must be a string")
        try:
            _validate_requirements(specification)
        except ValueError as error:
            raise PlanError(f"{context}.specification is invalid: {error}") from error
        task_ids.append(task_id)
        normalized.append(
            {
                "id": task_id,
                "depends_on": depends_on,
                "specification": specification.strip(),
            }
        )
    if len(task_ids) != len(set(task_ids)):
        raise PlanError("Planner returned duplicate task IDs")
    known_ids = set(task_ids)
    for task in normalized:
        unknown = sorted(set(task["depends_on"]) - known_ids)
        if unknown:
            raise PlanError(
                f"Planner task {task['id']} has unknown dependencies: "
                + ", ".join(unknown)
            )

    output = Path(output_directory).resolve()
    if output.exists() and any(output.iterdir()):
        raise PlanError(f"Output directory is not empty: {output}")
    output.mkdir(parents=True, exist_ok=True)
    specs_directory = output / "specs"
    specs_directory.mkdir()
    copied_source = output / "project.txt"
    copied_source.write_text(source_text + "\n", encoding="utf-8")

    plan_tasks = []
    for task in normalized:
        specification_file = specs_directory / f"{task['id']}.txt"
        specification_file.write_text(
            task["specification"] + "\n",
            encoding="utf-8",
        )
        plan_tasks.append(
            {
                "id": task["id"],
                "input_file": f"specs/{task['id']}.txt",
                "output_file": f"artifacts/{_module_name(task['id'])}.lean",
                "depends_on": task["depends_on"],
            }
        )
    plan_file = output / "plan.json"
    plan_file.write_text(
        json.dumps(
            {
                "schema_version": PLAN_SCHEMA_VERSION,
                "project_id": project_id,
                "source_file": "project.txt",
                "source_sha256": hashlib.sha256(copied_source.read_bytes()).hexdigest(),
                "tasks": plan_tasks,
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    return load_plan(plan_file)
