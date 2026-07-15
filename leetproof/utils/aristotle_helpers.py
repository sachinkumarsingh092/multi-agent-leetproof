"""Helpers for preparing Lean proof tasks for Aristotle."""

from __future__ import annotations
import tarfile
import re
import shutil
from pathlib import Path
from posixpath import normpath
from tempfile import TemporaryDirectory
from uuid import uuid4

from aristotlelib import Project, ProjectStatus

from logging_config import get_logger
from utils.lean.build import find_project_root
from utils.lean.constants import LOOM_SOLVE_SIMP_ALL, SET_MAX_HEARTBEATS
from utils.lean.goals import exact_goal
from utils.lean.parser import LeanFile
from utils.sorry_extraction import extract_sorry_goals, split_prologue
from utils.velvet_helpers import (
    GOAL_EXTRACTION_NOISE_SECTIONS,
    build_custom_loom_solver_prelude,
    extract_goals_after_loom_solve_with_retry,
    get_prove_correct_block,
    get_velvet_method,
    identity,
    indent,
    remove_goal_extraction_noise,
)

logger = get_logger(__name__)

DEFAULT_TARGET_SECTION = "Proof"
ARTIFACT_DIR_NAME = ".aristotle"
PROJECT_CONFIG_FILES = (
    "lean-toolchain",
    "lakefile.lean",
    "lakefile.toml",
    "lake-manifest.json",
    "lake-manifest.toml",
)
DEFAULT_LAKEFILE_TOML = """name = "AristotleSubmission"
version = "0.1.0"
defaultTargets = ["AristotleSubmission"]

[[lean_lib]]
name = "AristotleSubmission"
"""


def _resolve_artifacts_dir(
    input_file: Path,
    artifacts_dir: Path | None,
) -> Path:
    if artifacts_dir is not None:
        resolved_dir = Path(artifacts_dir)
    else:
        try:
            resolved_dir = Path(find_project_root(str(input_file))) / ARTIFACT_DIR_NAME
        except FileNotFoundError:
            resolved_dir = input_file.parent / ARTIFACT_DIR_NAME

    resolved_dir.mkdir(parents=True, exist_ok=True)
    return resolved_dir


def _build_artifact_paths(
    input_file: Path,
    *,
    artifact_kind: str,
    artifacts_dir: Path | None,
) -> tuple[Path, Path]:
    resolved_dir = _resolve_artifacts_dir(input_file, artifacts_dir)
    token = uuid4().hex[:8]
    suffix = input_file.suffix or ".lean"
    base_name = f"{input_file.stem}__{artifact_kind}__{token}"
    return resolved_dir / f"{base_name}{suffix}", resolved_dir / f"{base_name}_solution{suffix}"


def _append_solution_to_path(path: Path) -> Path:
    return path.with_name(f"{path.stem}Solution{path.suffix}")


def _build_submission_prompt(submission_file: Path, project_root: Path) -> str:
    submission_rel_path = submission_file.resolve().relative_to(project_root.resolve()).as_posix()
    return (
        "Fill in the sorries in this Lean project. "
        f"Focus on the file `{submission_rel_path}` and return the solved project archive. "
        "Preserve the project structure."
    )


def _downloadable_statuses() -> set[ProjectStatus]:
    statuses = {ProjectStatus.COMPLETE}
    for name in ("COMPLETE_WITH_ERRORS", "OUT_OF_BUDGET"):
        status = getattr(ProjectStatus, name, None)
        if status is not None:
            statuses.add(status)
    return statuses


def _copy_file_into_staging(*, source: Path, destination: Path) -> Path:
    destination.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(source, destination)
    return destination


def _stage_minimal_project(project_root: Path, submission_file: Path, staging_root: Path) -> Path:
    project_root = project_root.resolve()
    submission_file = submission_file.resolve()
    staging_root.mkdir(parents=True, exist_ok=True)

    copied_config = False
    for config_name in PROJECT_CONFIG_FILES:
        config_path = project_root / config_name
        if config_path.exists():
            _copy_file_into_staging(
                source=config_path,
                destination=staging_root / config_name,
            )
            copied_config = True

    if not copied_config:
        (staging_root / "lakefile.toml").write_text(DEFAULT_LAKEFILE_TOML)

    staged_submission_file = staging_root / submission_file.name
    _copy_file_into_staging(
        source=submission_file,
        destination=staged_submission_file,
    )
    return staged_submission_file


def _extract_member_from_tarball(
    archive_path: Path,
    *,
    member_rel_path: Path,
    destination: Path,
) -> Path:
    expected = normpath(member_rel_path.as_posix()).lstrip("./")
    with tarfile.open(archive_path, "r:*") as archive:
        selected_member = None
        lean_members: list[tarfile.TarInfo] = []
        basename_matches: list[tarfile.TarInfo] = []
        for member in archive.getmembers():
            if not member.isfile():
                continue
            member_name = normpath(member.name).lstrip("./")
            if member_name == expected or member_name.endswith("/" + expected):
                selected_member = member
                break
            if member_name.endswith(".lean"):
                lean_members.append(member)
                if Path(member_name).name == member_rel_path.name:
                    basename_matches.append(member)

        if selected_member is None:
            if len(basename_matches) == 1:
                selected_member = basename_matches[0]
            elif len(lean_members) == 1:
                selected_member = lean_members[0]
            else:
                candidates = [normpath(member.name).lstrip("./") for member in lean_members]
                raise FileNotFoundError(
                    f"Could not determine which Lean file to extract from {archive_path}. "
                    f"Expected {expected}. Lean candidates: {candidates}"
                )

        extracted = archive.extractfile(selected_member)
        if extracted is None:
            raise RuntimeError(
                f"Could not extract {selected_member.name} from {archive_path}"
            )

        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(extracted.read())
        return destination


def _render_submission_file(
    *,
    imports: list[str],
    prologue_body: str,
    preserved_sections: list[str],
    target_section: str,
    theorem_blocks: list[str],
) -> str:
    parts: list[str] = []
    parts.extend(imports)

    if prologue_body:
        parts.append(prologue_body)

    parts.extend(section for section in preserved_sections if section)

    proof_lines = [f"section {target_section}"]
    if theorem_blocks:
        proof_lines.extend(["", "\n\n".join(theorem_blocks)])
    proof_lines.extend([f"end {target_section}"])
    parts.append("\n".join(proof_lines))

    return "\n\n".join(part for part in parts if part).rstrip() + "\n"


async def _submit_prepared_file(
    *,
    submission_file: Path,
    project_root: Path,
) -> str:
    logger.info("Submitting %s to Aristotle", submission_file)
    with TemporaryDirectory() as temp_dir:
        staging_root = Path(temp_dir) / project_root.resolve().name
        staged_submission_file = _stage_minimal_project(
            project_root=project_root,
            submission_file=submission_file,
            staging_root=staging_root,
        )
        logger.info(
            "Created staged Aristotle project at %s with submission file %s",
            staging_root,
            staged_submission_file.name,
        )
        project = await Project.create_from_directory(
            prompt=_build_submission_prompt(staged_submission_file, staging_root),
            project_dir=staging_root,
        )
    logger.info("Aristotle submission created with id %s", project.project_id)
    return project.project_id


async def submit_to_aristotle(
    file_path: Path,
) -> str:
    """Submit a Lean file to Aristotle without waiting for completion.

    Requires ``ARISTOTLE_API_KEY`` to be configured in the environment.
    """

    source_file = Path(file_path).resolve()
    if not source_file.exists():
        raise FileNotFoundError(source_file)

    project_id = await _submit_prepared_file(
        submission_file=source_file,
        project_root=Path(find_project_root(str(source_file))),
    )
    return project_id


async def extract_sorries_and_submit_to_aristotle(
    input_file: Path,
    *,
    target_section: str = DEFAULT_TARGET_SECTION,
) -> tuple[str,Path]:
    """Extract sorry goals into a focused file, then submit that file to Aristotle."""

    source_file = Path(input_file).resolve()
    lean_file = LeanFile.from_path(source_file)
    extraction = extract_sorry_goals(lean_file, target_section)
    if not extraction.sorry_goals:
        raise ValueError(
            f"No sorry goals found in section '{target_section}' of {source_file}"
        )

    submission_file = source_file.parent / Path(source_file.stem + "AristotleProof" + source_file.suffix)

    theorem_blocks = [goal.statement for goal in extraction.sorry_goals]    
    preserved_sections = [
        section.full_text().strip()
        for section in lean_file.sections
        if section.name != target_section and "method" not in section.content and section.name in ["Specs", "Impl", "TestCases"]
    ]
    submission_content = _render_submission_file(
        imports=[f"import {import_name}" for import_name in extraction.imports if not (import_name.startswith("Velvet") or import_name.startswith("Extensions"))  ],
        prologue_body="\n".join([line for line in extraction.prologue_body.splitlines() if "loom" not in line.strip()]),
        preserved_sections=preserved_sections,
        target_section=target_section,
        theorem_blocks=theorem_blocks,
    )
    submission_file.write_text(submission_content)
    print(submission_content)

    project_id = await _submit_prepared_file(
        submission_file=submission_file,
        project_root=Path(find_project_root(str(submission_file))),
    )
    return (project_id,submission_file)


async def extract_sorries_after_loom_solve_and_submit_to_aristotle(
    input_file: Path,
    *,
    preferred_grind_gen_param: int | None = None,
) -> tuple[str, Path]:
    """Extract velvet VCs after `loom_solve`, then submit them to Aristotle."""

    proof_section = "TempGoalExtraction"
    lean_file = LeanFile.from_path(input_file)

    all_sections = lean_file.section_names()
    # Remove all the non specs and impl section, quite pointless
    for section in all_sections:
        if section not in ['Specs', 'Impl']:
            lean_file.remove_section(section)

    resolved_input = input_file.resolve()
    new_file_path = resolved_input.parent / Path(resolved_input.stem + "LoomSolveVCsSorried" + resolved_input.suffix)
    submission_file_path = resolved_input.parent / Path(resolved_input.stem + "LoomSolveVCsSorriedAristotleProof" + resolved_input.suffix)

    program = lean_file.reconstruct_and_write_to_file(new_file_path)

    extraction_result = await extract_goals_after_loom_solve_with_retry(
        program,
        str(new_file_path),
        preprocess=remove_goal_extraction_noise,
        postprocess=identity,
        section_name=proof_section,
        cleanup_mode="comment_out",
        preferred_grind_gen_param=preferred_grind_gen_param,
    )

    if len(extraction_result.goals) == 0:
        raise RuntimeError(
            f"The goal extraction after loom_solve yielded 0 goals"
        )

    loom_solve_snippet = f"""

{SET_MAX_HEARTBEATS}

{get_prove_correct_block(get_velvet_method(lean_file.get_section("Impl", assert_exists=True).content))}
"""
    if extraction_result.grind_gen_param:
        loom_solve_snippet = build_custom_loom_solver_prelude(extraction_result.grind_gen_param) + "\n" + loom_solve_snippet

    goal_tactics = []
    for goal in extraction_result.goals:
        goal_tactics.append(indent(exact_goal(goal), 2))
    if goal_tactics:
        tactics_block = "\n" + "\n".join(goal_tactics)
        pattern = re.escape(LOOM_SOLVE_SIMP_ALL)
        replacement = LOOM_SOLVE_SIMP_ALL + tactics_block
        loom_solve_snippet = re.sub(
            pattern,
            replacement,
            loom_solve_snippet,
            count=1,
        )
    theorem_blocks = [goal.as_sorried() for goal in extraction_result.goals]
    lean_file.add_or_replace_section(proof_section, "\n\n".join(theorem_blocks) + "\n\n" + loom_solve_snippet )
    lean_file.reconstruct_and_write_to_file(new_file_path)


    import_names, prologue_body = split_prologue(lean_file)
    imports = [f"import {import_name}" for import_name in import_names if not (import_name.startswith("Velvet") or import_name.startswith("Extensions"))  ]
    
    preserved_sections = [
        lean_file.get_section("Specs", assert_exists = True).full_text()
    ]
    


    submission_content = _render_submission_file(
        imports=imports,
        prologue_body="\n".join([line for line in prologue_body.splitlines() if "loom" not in line.strip()]),
        preserved_sections=preserved_sections,
        target_section="Proof",
        theorem_blocks=theorem_blocks,
    )
    print(submission_content)
    submission_file_path.write_text(submission_content)

    project_id = await _submit_prepared_file(
        submission_file=submission_file_path,
        project_root=Path(find_project_root(str(submission_file_path))),
    )



    return (project_id, submission_file_path)


async def get_submission_status(project_id: str) -> ProjectStatus:
    """Return the current Aristotle status for a submission id."""
    project = await Project.from_id(project_id)
    return project.status


async def get_submission(
    project_id: str,
    path: str | Path | None = None,
    project_root: str | Path | None = None,
) -> Path | None:
    """Download a solved submission. Returns None if it is not solved yet."""

    project = await Project.from_id(project_id)
    if project.status not in _downloadable_statuses():
        return None

    if path is None:
        raise RuntimeError("Pass `path=` explicitly for Aristotle 1.0 project results.")
    if project_root is None:
        raise RuntimeError(
            "Pass `project_root=` explicitly for Aristotle 1.0 project results."
        )

    destination = Path(path)
    if not destination.is_absolute():
        destination = destination.resolve()

    project_root_path = Path(project_root)
    if not project_root_path.is_absolute():
        project_root_path = project_root_path.resolve()

    member_rel_path = destination.relative_to(project_root_path)

    with TemporaryDirectory() as temp_dir:
        archive_path = Path(temp_dir) / f"{project_id}_aristotle.tar.gz"
        await project.get_solution(destination=archive_path)
        return _extract_member_from_tarball(
            archive_path,
            member_rel_path=member_rel_path,
            destination=destination,
        )


__all__ = [
    "submit_to_aristotle",
    "extract_sorries_and_submit_to_aristotle",
    "extract_sorries_after_loom_solve_and_submit_to_aristotle",
    "get_submission_status",
    "get_submission",
]
