"""Reviewed-specification implementation and verification pipeline.

The default flow formalizes reviewed natural language, then runs code
generation, loop-invariant generation, and formal verification.
"""

import atexit
import hashlib
import json
import re
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, Optional, cast
from uuid import uuid4

from dbos import DBOS

from agents.agent_state import GoalStatus, JudgeVerdict, PBTStatus, VelvetAgentState
from args import Stage, save_session_params
from config.constants import APP_VERSION, DB_DIR, SESSIONS_DIR
from logging_config import get_logger
from tools.common import set_allowed_output_files
from tools.mcp_tools import cleanup_mcp_sync
from utils.program_state import ProgramBuffer
from utils.token_tracker import log_token_usage_on_exit

logger = get_logger(__name__)

atexit.register(cleanup_mcp_sync)

RESULT_SCHEMA_VERSION = 1


class PipelineStageError(RuntimeError):
    """Raised when a pipeline stage returns a rejected state."""

    def __init__(self, stage: Stage, message: str) -> None:
        super().__init__(message)
        self.stage = stage


def create_velvet_state(
    specification: str,
    output_file: str,
    program_content: str = "",
    stable_content: str = "",
    typechecks: bool = False,
    judge_verdict: JudgeVerdict = JudgeVerdict.PENDING,
    formal_contract_file: str | None = None,
    formal_contract_sha256: str | None = None,
) -> VelvetAgentState:
    """Create the state shared by code generation and proof stages."""
    if program_content:
        buffer = ProgramBuffer.from_content(output_file, program_content)
    else:
        buffer = ProgramBuffer.empty(output_file)

    program_state = buffer.to_dict()
    if stable_content:
        if stable_content == program_content:
            program_state = buffer.promote_current()
        else:
            program_state = buffer.update_stable(stable_content)

    state: VelvetAgentState = {
        "specification": specification,
        "program_state": program_state,
        "build_log": "",
        "typechecks": typechecks,
        "attempt": 0,
        "judge_rejections": {},
        "output_file": output_file,
        "judge_verdict": judge_verdict,
        "judge_reasoning": "",
        "phase_results": {},
        "judge_context": {},
        "goals": [],
        "continuation_ctx": {},
        "pbt_status": PBTStatus.NOT_ATTEMPTED,
        "goal_extraction_grind_gen_param": None,
    }
    if formal_contract_file is not None:
        state["formal_contract_file"] = formal_contract_file
    if formal_contract_sha256 is not None:
        state["formal_contract_sha256"] = formal_contract_sha256
    return state


def get_stage_order() -> list[Stage]:
    """Return the worker stages in execution order."""
    return list(Stage)


def get_stage_index(stage: Stage) -> int:
    """Return a stage's position in the worker pipeline."""
    return get_stage_order().index(stage)


def resolve_pipeline_session_name(
    session_name: Optional[str],
    resume: bool,
) -> str:
    """Return an explicit session name or generate one for a fresh run."""
    if session_name:
        return session_name
    if resume:
        raise ValueError("--resume requires --session-name")

    timestamp = datetime.now(timezone.utc).strftime("%Y%m%d-%H%M%S")
    return f"pipeline-{timestamp}-{uuid4().hex[:8]}"


def freeze_formal_contract(
    contract: str,
    output_file: str,
    session_name: str | None,
) -> tuple[str, str]:
    """Persist one immutable formal contract for a session and output."""
    if not session_name:
        raise ValueError("A session name is required to freeze the formal contract")

    contract_hash = hashlib.sha256(contract.encode("utf-8")).hexdigest()
    artifact_dir = Path(SESSIONS_DIR) / session_name / "contracts"
    artifact_dir.mkdir(parents=True, exist_ok=True)
    artifact_path = artifact_dir / f"{Path(output_file).stem}.contract.lean"

    if artifact_path.exists():
        frozen_contract = artifact_path.read_text(encoding="utf-8")
        if frozen_contract != contract:
            raise ValueError(
                f"Formal contract is already frozen for session {session_name}: "
                f"{artifact_path}"
            )
    else:
        artifact_path.write_text(contract, encoding="utf-8")

    return str(artifact_path), contract_hash


def validate_worker_paths(
    start_stage: Stage, input_file: str, output_file: str
) -> None:
    """Validate input/output boundaries for the selected starting stage."""
    if (
        start_stage in (Stage.SPECGEN, Stage.CODEGEN)
        and Path(input_file).resolve() == Path(output_file).resolve()
    ):
        raise ValueError(
            "--input-file and --output-file must differ when starting at "
            f"{start_stage.value}"
        )
    if start_stage == Stage.SPECGEN and Path(input_file).suffix.lower() != ".txt":
        raise ValueError("specgen input must be a reviewed .txt specification")
    if start_stage == Stage.SPECGEN and Path(output_file).suffix.lower() != ".lean":
        raise ValueError("specgen output must be a .lean file")


@DBOS.step()
def load_input_for_stage(
    stage: Stage, input_file: str, output_file: str
) -> Dict[str, Any]:
    """Load reviewed text, a formal contract, or an existing implementation."""
    logger.info("Loading input for stage: %s", stage.value)
    logger.info("Input file: %s", input_file)

    input_path = Path(input_file)
    if not input_path.exists():
        raise FileNotFoundError(f"Input file not found: {input_file}")

    file_content = input_path.read_text()
    if not file_content.strip():
        raise ValueError("Input file is empty")

    if stage == Stage.SPECGEN:
        from requirements import validate_requirements

        validate_requirements(file_content)
        return {
            "problem_description": file_content,
            "output_file": output_file,
        }

    if stage == Stage.CODEGEN:
        return create_velvet_state(file_content, output_file)

    if stage in (Stage.INVGEN, Stage.VERIFY):
        state = create_velvet_state(
            specification=file_content,
            output_file=output_file if output_file != input_file else input_file,
            program_content=file_content,
            stable_content=file_content,
            typechecks=True,
            judge_verdict=JudgeVerdict.PASS,
        )
        if stage == Stage.INVGEN:
            from agents.velvet_programmer import VelvetProgrammerAgent

            state["phase_results"] = {
                VelvetProgrammerAgent.name: {"stable_content": file_content}
            }
        return state

    raise ValueError(f"Unknown stage: {stage}")


@DBOS.step()
async def run_spec_generation(
    state: Dict[str, Any],
    provider: str,
    model: str,
    session_name: str | None,
) -> VelvetAgentState:
    """Formalize reviewed natural language and Lean-type-check the contract."""
    from formalize import generate_contract
    from providers import LLMConfig

    logger.info("=" * 80)
    logger.info("STAGE 1: FORMAL CONTRACT GENERATION")
    logger.info("=" * 80)

    project_root = Path.cwd().resolve()
    output_path = Path(str(state["output_file"])).resolve()
    try:
        output_path.relative_to(project_root)
    except ValueError as exc:
        raise ValueError("Formal contract output must be inside --project") from exc
    output_path.parent.mkdir(parents=True, exist_ok=True)

    contract = await generate_contract(
        reviewed_specification=str(state["problem_description"]),
        output_path=output_path,
        project_root=project_root,
        config=LLMConfig(provider=provider, model=model),
    )
    contract_file, contract_hash = freeze_formal_contract(
        contract,
        str(state["output_file"]),
        session_name,
    )
    return create_velvet_state(
        contract,
        str(state["output_file"]),
        typechecks=True,
        formal_contract_file=contract_file,
        formal_contract_sha256=contract_hash,
    )


async def run_code_generation(state: VelvetAgentState) -> VelvetAgentState:
    """Generate an implementation for the frozen contract."""
    from container import get_container

    logger.info("=" * 80)
    logger.info("STAGE 2: CODE GENERATION")
    logger.info("=" * 80)
    result = await get_container().programmer.run_workflow(state)
    state = cast(VelvetAgentState, result)
    logger.info("Code generation completed: %s", state.get("judge_verdict", "N/A"))
    return state


async def run_invariant_generation(state: VelvetAgentState) -> VelvetAgentState:
    """Infer loop invariants for the generated implementation."""
    from container import get_container

    logger.info("=" * 80)
    logger.info("STAGE 3: INVARIANT GENERATION")
    logger.info("=" * 80)
    result = await get_container().inferrer.run_workflow(state)
    state = cast(VelvetAgentState, result)
    logger.info("Invariant generation completed: %s", state.get("judge_verdict", "N/A"))
    return state


async def run_verification(state: VelvetAgentState) -> VelvetAgentState:
    """Generate proofs and run the final independent Lean build."""
    from container import get_container
    from workflow_helpers import final_verification

    logger.info("=" * 80)
    logger.info("STAGE 4: VERIFICATION")
    logger.info("=" * 80)
    result = await get_container().orchestrator.run_workflow(state)
    state = cast(VelvetAgentState, result)
    return {**state, **final_verification(state)}


def reset_for_next_stage(state: VelvetAgentState) -> VelvetAgentState:
    """Reset transient attempt context between stages."""
    return {
        **state,
        "attempt": 0,
        "judge_context": {},
        "continuation_ctx": {},
        "judge_reasoning": "",
    }


def get_output_result_path(
    output_file: str,
    session_name: str | None = None,
) -> str:
    """Return the session-scoped result path for an output file."""
    output_path = Path(output_file)
    if session_name is None:
        from args import get_args

        session_name = getattr(get_args(), "session_name", None)
    if session_name:
        result_dir = Path(SESSIONS_DIR) / session_name
        result_dir.mkdir(parents=True, exist_ok=True)
        return str(result_dir / f"{output_path.stem}_result.json")
    return str(output_path.parent / f"{output_path.stem}_result.json")


def _file_sha256(file_path: str) -> str | None:
    path = Path(file_path)
    if not path.is_file():
        return None
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _write_result_file(result_file: Path, result: Dict[str, Any]) -> None:
    """Atomically publish a worker result for external readers."""
    result_file.parent.mkdir(parents=True, exist_ok=True)
    temp_file = result_file.with_name(
        f".{result_file.name}.{uuid4().hex}.tmp"
    )
    try:
        temp_file.write_text(json.dumps(result, indent=2) + "\n")
        temp_file.replace(result_file)
    finally:
        temp_file.unlink(missing_ok=True)


def _read_result_file(result_file: Path) -> Dict[str, Any]:
    if not result_file.is_file():
        raise RuntimeError(f"Pipeline result was not initialized: {result_file}")
    result = json.loads(result_file.read_text())
    if result.get("schema_version") != RESULT_SCHEMA_VERSION:
        raise RuntimeError(
            f"Unsupported pipeline result schema in {result_file}"
        )
    return result


@DBOS.step()
def initialize_pipeline_result(
    input_file: str,
    output_file: str,
    start_stage: Stage,
    end_stage: Stage,
    session_name: str | None,
) -> None:
    """Publish RUNNING metadata before any pipeline work starts."""
    result_file = Path(get_output_result_path(output_file, session_name))
    result = {
        "schema_version": RESULT_SCHEMA_VERSION,
        "session_name": session_name,
        "status": "RUNNING",
        "pipeline": {
            "start_stage": start_stage.value,
            "end_stage": end_stage.value,
        },
        "input": {"file": input_file},
        "contract": None,
        "implementation": {
            "file": output_file,
            "sha256": None,
        },
        "verification": {
            "testcases_passed": None,
            "pbt_status": None,
            "proof_status": None,
            "goals_proven": None,
            "goals_partial": None,
            "goals_total": None,
        },
        "stages": {},
        "error": None,
    }
    _write_result_file(result_file, result)
    logger.info("Initialized result file: %s", result_file)


@DBOS.step()
def write_stage_result(
    output_file: str,
    stage: Stage,
    state: Dict[str, Any],
    session_name: str | None,
) -> None:
    """Persist a completed stage and aggregate verification status."""
    result_file = Path(get_output_result_path(output_file, session_name))
    result = _read_result_file(result_file)

    contract_file = state.get("formal_contract_file")
    contract_hash = state.get("formal_contract_sha256")
    if contract_file and contract_hash:
        result["contract"] = {
            "file": contract_file,
            "sha256": contract_hash,
        }

    stage_failed = check_stage_failed(stage, state)
    if stage == Stage.SPECGEN:
        stage_info = {
            "status": "FAILED" if stage_failed else "SUCCESS",
            "typechecks": state.get("typechecks", False),
        }
    elif stage == Stage.CODEGEN:
        pbt_status = state.get("pbt_status", PBTStatus.NOT_ATTEMPTED)
        pbt_value = (
            pbt_status.value if isinstance(pbt_status, PBTStatus) else pbt_status
        )
        judge_verdict = state.get("judge_verdict", JudgeVerdict.PENDING)
        judge_value = (
            judge_verdict.value
            if isinstance(judge_verdict, JudgeVerdict)
            else judge_verdict
        )
        testcases_passed = state.get("typechecks", False)
        stage_info = {
            "status": "FAILED" if stage_failed else "SUCCESS",
            "testcases_passed": testcases_passed,
            "judge_verdict": judge_value,
            "pbt_status": pbt_value,
        }
        result["verification"]["testcases_passed"] = testcases_passed
        result["verification"]["pbt_status"] = pbt_value
    elif stage == Stage.INVGEN:
        judge_verdict = state.get("judge_verdict", JudgeVerdict.PENDING)
        judge_value = (
            judge_verdict.value
            if isinstance(judge_verdict, JudgeVerdict)
            else judge_verdict
        )
        stage_info = {
            "status": "FAILED" if stage_failed else "SUCCESS",
            "judge_verdict": judge_value,
        }
    else:
        goals = state.get("goals", [])
        proof_typechecks = bool(state.get("typechecks", False))
        proof_passed = _proof_passed(state)
        goals_proven = sum(
            1 for goal in goals if goal.get("status") == GoalStatus.PROVEN
        )
        goals_partial = sum(
            1 for goal in goals if goal.get("status") == GoalStatus.PARTIAL
        )
        stage_info = {
            "status": "SUCCESS" if proof_passed else "FAILED",
            "typechecks": proof_typechecks,
            "goals_proven": goals_proven,
            "goals_partial": goals_partial,
            "goals_total": len(goals),
        }
        result["verification"].update(
            {
                "proof_status": "PASSED" if proof_passed else "FAILED",
                "goals_proven": goals_proven,
                "goals_partial": goals_partial,
                "goals_total": len(goals),
            }
        )

    result["stages"][stage.value] = stage_info
    _write_result_file(result_file, result)
    logger.info("Updated result file: %s", result_file)


@DBOS.step()
def finalize_pipeline_result(
    output_file: str,
    end_stage: Stage,
    session_name: str | None,
) -> None:
    """Publish a successful terminal worker result."""
    result_file = Path(get_output_result_path(output_file, session_name))
    result = _read_result_file(result_file)
    result["status"] = "SUCCESS"
    result["error"] = None
    if end_stage != Stage.SPECGEN:
        result["implementation"]["sha256"] = _file_sha256(output_file)
    _write_result_file(result_file, result)
    logger.info("Finalized successful result file: %s", result_file)


@DBOS.step()
def fail_pipeline_result(
    output_file: str,
    session_name: str | None,
    stage: Stage | None,
    error_type: str,
    message: str,
) -> None:
    """Publish a structured terminal failure without discarding partial state."""
    result_file = Path(get_output_result_path(output_file, session_name))
    result = _read_result_file(result_file)
    result["status"] = "FAILED"
    result["implementation"]["sha256"] = (
        _file_sha256(output_file) if stage is not None else None
    )
    result["error"] = {
        "stage": stage.value if stage is not None else None,
        "type": error_type,
        "message": message,
    }
    if stage is not None:
        stage_info = result["stages"].setdefault(stage.value, {})
        stage_info["status"] = "FAILED"
    _write_result_file(result_file, result)
    logger.info("Finalized failed result file: %s", result_file)


def _proof_passed(state: Dict[str, Any]) -> bool:
    if not state.get("typechecks", False):
        return False
    goals = state.get("goals", [])
    if any(goal.get("status") != GoalStatus.PROVEN for goal in goals):
        return False
    output_file = state.get("output_file")
    if output_file and Path(output_file).is_file():
        from utils.lean.parser import _remove_comments

        program = _remove_comments(Path(output_file).read_text())
        if re.search(r"\b(?:sorry|admit)\b", program):
            return False
    return True


def _stage_failure_message(stage: Stage, state: Dict[str, Any]) -> str:
    candidates = [
        state.get("judge_reasoning"),
        state.get("build_log"),
    ]
    candidates.extend(
        goal.get("description")
        for goal in state.get("goals", [])
        if goal.get("status") != GoalStatus.PROVEN
    )
    for candidate in candidates:
        if candidate and str(candidate).strip():
            return str(candidate).strip()[:8000]
    return f"Stage {stage.value} returned a rejected result"


def check_stage_failed(stage: Stage, state: Dict[str, Any]) -> bool:
    """Return whether a generation stage produced a rejected result."""
    if stage == Stage.SPECGEN:
        return not state.get("typechecks", False)
    if stage in (Stage.CODEGEN, Stage.INVGEN):
        return (
            not state.get("typechecks", False)
            or state.get("judge_verdict") == JudgeVerdict.FAIL
        )
    return not _proof_passed(state)


@log_token_usage_on_exit
@DBOS.workflow()
async def run_pipeline(
    start_stage: Stage,
    end_stage: Stage,
    input_file: str,
    output_file: str,
    provider: str,
    model: str,
    session_name: Optional[str] = None,
) -> Dict[str, Any]:
    """Run the worker from ``start_stage`` through ``end_stage``."""
    initialize_pipeline_result(
        input_file,
        output_file,
        start_stage,
        end_stage,
        session_name,
    )
    current_stage: Stage | None = None
    try:
        validate_worker_paths(start_stage, input_file, output_file)

        start_idx = get_stage_index(start_stage)
        end_idx = get_stage_index(end_stage)
        if start_idx > end_idx:
            raise ValueError(
                f"Start stage ({start_stage.value}) must precede or equal "
                f"end stage ({end_stage.value})"
            )

        current_state = load_input_for_stage(start_stage, input_file, output_file)
        if start_stage == Stage.CODEGEN:
            contract_file, contract_hash = freeze_formal_contract(
                str(current_state["specification"]),
                output_file,
                session_name,
            )
            current_state["formal_contract_file"] = contract_file
            current_state["formal_contract_sha256"] = contract_hash
        stages = get_stage_order()[start_idx : end_idx + 1]
        runners = {
            Stage.CODEGEN: run_code_generation,
            Stage.INVGEN: run_invariant_generation,
            Stage.VERIFY: run_verification,
        }

        logger.info("Session: %s", session_name or "unnamed")
        logger.info("Stages: %s", [stage.value for stage in stages])
        set_allowed_output_files([output_file])

        for stage in stages:
            current_stage = stage
            if stage == Stage.SPECGEN:
                current_state = await run_spec_generation(
                    current_state,
                    provider,
                    model,
                    session_name,
                )
            else:
                current_state = await runners[stage](
                    cast(VelvetAgentState, current_state)
                )
            write_stage_result(
                output_file,
                stage,
                current_state,
                session_name,
            )
            if check_stage_failed(stage, current_state):
                raise PipelineStageError(
                    stage,
                    _stage_failure_message(stage, current_state),
                )
            if stage != end_stage:
                current_state = reset_for_next_stage(current_state)

        finalize_pipeline_result(output_file, end_stage, session_name)
        logger.info(
            "Pipeline completed: %s",
            current_state.get("output_file", output_file),
        )
        return current_state
    except Exception as error:
        failed_stage = (
            error.stage if isinstance(error, PipelineStageError) else current_stage
        )
        fail_pipeline_result(
            output_file,
            session_name,
            failed_stage,
            type(error).__name__,
            str(error),
        )
        raise


async def pipeline_workflow() -> Dict[str, Any]:
    """Run or resume the configured DBOS workflow."""
    from args import get_args
    from utils.dbos_utils import run_or_resume_workflow

    args = get_args()
    start_stage = Stage(args.start)
    end_stage = Stage(args.end) if args.end else Stage.VERIFY
    return await run_or_resume_workflow(
        session_name=args.session_name,
        resume=args.resume,
        coro_fn=lambda: run_pipeline(
            start_stage=start_stage,
            end_stage=end_stage,
            input_file=args.input_file,
            output_file=args.output_file,
            provider=args.provider,
            model=args.model,
            session_name=args.session_name,
        ),
    )


def init_dbos_and_container(
    provider: str,
    model: str,
    session_name: Optional[str] = None,
    max_input_tokens: Optional[int] = None,
    max_output_tokens: Optional[int] = None,
    max_total_tokens: Optional[int] = None,
    max_cost: Optional[float] = None,
    agent_context: Optional[str] = None,
    resume: bool = False,
) -> None:
    """Initialize durable workflow state and all worker agents."""
    from dbos import DBOSConfig

    from container import init_container
    from providers import LLMConfig
    from utils.agent_context import init_agent_context
    from utils.message_helpers import init_message_helpers
    from utils.token_tracker import init_token_tracker

    init_token_tracker(
        session_name=session_name,
        max_input_tokens=max_input_tokens,
        max_output_tokens=max_output_tokens,
        max_total_tokens=max_total_tokens,
        max_cost=max_cost,
        model_name=model,
        resume=resume,
    )
    init_agent_context(agent_context)
    init_message_helpers(session_name)

    Path(DB_DIR).mkdir(parents=True, exist_ok=True)
    config: DBOSConfig = {
        "name": "lloom-pipeline",
        "system_database_url": f"sqlite:///{DB_DIR}/lloom_pipeline.sqlite",
        "executor_id": f"pipeline-{session_name}",
        "application_version": APP_VERSION,
    }
    DBOS(config=config)
    init_container(LLMConfig(provider=provider, model=model))
    DBOS.launch()


def main() -> None:
    """Run the reviewed-specification worker CLI."""
    import os
    import sys

    from args import merge_session_params, parse_args
    from logging_config import setup_logging
    from runner import run

    args = parse_args()
    generated_session = not args.session_name
    try:
        args.session_name = resolve_pipeline_session_name(
            args.session_name,
            args.resume,
        )
    except ValueError as exc:
        print(f"Error: {exc}")
        sys.exit(1)
    if generated_session:
        print(f"Session: {args.session_name}")

    project_dir = os.path.abspath(args.project)
    if not os.path.isdir(project_dir):
        print(f"Error: --project directory does not exist: {project_dir}")
        sys.exit(1)
    os.chdir(project_dir)
    setup_logging(level=args.log_level, tui_mode=False)

    merge_session_params(args)
    required = ("input_file", "output_file", "provider", "model")
    missing = [name for name in required if not getattr(args, name)]
    if missing:
        formatted = ", ".join("--" + name.replace("_", "-") for name in missing)
        print(f"Error: missing required arguments: {formatted}")
        sys.exit(1)
    try:
        validate_worker_paths(Stage(args.start), args.input_file, args.output_file)
    except ValueError as exc:
        print(f"Error: {exc}")
        sys.exit(1)

    if not args.resume and args.session_name:
        save_session_params(
            session_name=args.session_name,
            provider=args.provider,
            model=args.model,
            input_file=args.input_file,
            output_file=args.output_file,
            start=args.start,
            end=args.end,
            max_input_tokens=args.max_input_tokens,
            max_output_tokens=args.max_output_tokens,
            max_total_tokens=args.max_total_tokens,
            max_cost=args.max_cost,
            agent_context=args.agent_context,
        )

    init_dbos_and_container(
        provider=args.provider,
        model=args.model,
        session_name=args.session_name,
        max_input_tokens=args.max_input_tokens,
        max_output_tokens=args.max_output_tokens,
        max_total_tokens=args.max_total_tokens,
        max_cost=args.max_cost,
        agent_context=args.agent_context,
        resume=args.resume,
    )

    try:
        run(pipeline_workflow)
    except KeyboardInterrupt:
        logger.info("Interrupted by user")
        sys.exit(130)
    except Exception as exc:
        from utils.token_tracker import CostLimitExceededError, TokenLimitExceededError

        if isinstance(exc, (TokenLimitExceededError, CostLimitExceededError)):
            logger.error("Limit exceeded: %s", exc)
            sys.exit(2)
        logger.error("Pipeline failed: %s", exc)
        sys.exit(1)


if __name__ == "__main__":
    main()
