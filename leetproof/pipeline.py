"""
Complete pipeline combining specification generation and program synthesis.

This pipeline runs four stages sequentially as a DBOS workflow:

1. specgen - Specification Generation (includes property-based testing)
2. codegen - Code Generation from specification
3. invgen - Invariant Generation for loop invariants
4. verify - Verification with formal proofs

Each stage invokes the appropriate agent's DBOS workflow.
"""

import atexit
import json
from pathlib import Path
from typing import Dict, Any, Optional, cast

from dbos import DBOS

from agents.spec_state import SpecAgentState, CoachVerdict
from agents.agent_state import VelvetAgentState, JudgeVerdict, GoalStatus, PBTStatus
from tools.mcp_tools import cleanup_mcp_sync
from tools.common import set_allowed_output_files
from logging_config import setup_logging, get_logger
from utils.lean.parser import LeanFile
from utils.token_tracker import log_token_usage_on_exit
from utils.program_state import ProgramBuffer
from args import Stage, get_parser, save_session_params
from config.constants import APP_VERSION, DB_DIR, SESSIONS_DIR
from config.limits import Limits

logger = get_logger(__name__)

# Register cleanup handler for MCP tools
atexit.register(cleanup_mcp_sync)


# =============================================================================
# Stage Names (Constants)
# =============================================================================

# Stage runner names for workflow identification
STAGE_SPEC_GENERATION = "spec_generation"
STAGE_CODE_GENERATION = "code_generation"
STAGE_INVARIANT_GENERATION = "invariant_generation"
STAGE_VERIFICATION = "verification"


# =============================================================================
# State Initialization
# =============================================================================


def create_spec_state(
    problem_description: str,
    problem_id: str,
    output_file: str,
) -> SpecAgentState:
    """Create initial SpecAgentState for specification generation."""
    return {
        "problem_description": problem_description,
        "problem_id": problem_id,
        "output_file": output_file,
        "planning_results": "",
        "current_spec": "",
        "build_log": "",
        "typechecks": False,
        "has_axiom": False,
        "sorry_count": 0,
        "extracted_goals_typecheck_passed": None,
        "specgen_attempt": 0,
        "specgen_max_attempt": Limits.SPEC_GEN_MAX_ATTEMPTS,
        "coach_verdict": CoachVerdict.PENDING,
        "coach_feedback": "",
        "coach_score": 0,
        "example_verify_file": "",
        "example_verify_content": "",
        "proof_typechecks": False,
        "proof_build_log": "",
        "proof_attempt": 0,
        "proven_count": 0,
        "proof_guide_feedback": "",
        "pbt_result": "",
        "pbt_detail": "",
        "spec_history": [],
    }


def create_velvet_state(
    specification: str,
    output_file: str,
    program_content: str = "",
    stable_content: str = "",
    typechecks: bool = False,
    judge_verdict: JudgeVerdict = JudgeVerdict.PENDING,
) -> VelvetAgentState:
    """Create initial VelvetAgentState for code/invariant/verification stages."""
    if program_content:
        buffer = ProgramBuffer.from_content(
            output_file,
            program_content,
        )
    else:
        buffer = ProgramBuffer.empty(output_file)

    # No mutation helper needed for the baseline shape; just serialize as-is.
    program_state = buffer.to_dict()
    if stable_content:
        if stable_content == program_content:
            program_state = buffer.promote_current()
        else:
            program_state = buffer.update_stable(stable_content)

    return {
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


def get_stage_order() -> list[Stage]:
    """Get ordered list of stages from the Stage enum definition order."""
    return list(Stage)


def get_stage_index(stage: Stage) -> int:
    """Get the index of a stage in the pipeline."""
    return get_stage_order().index(stage)


@DBOS.step()
def load_input_for_stage(
    stage: Stage, input_file: str, output_file: str
) -> Dict[str, Any]:
    """Load input from file based on the starting stage."""
    logger.info(f"Loading input for stage: {stage}")
    logger.info(f"Input file: {input_file}")

    input_path = Path(input_file)
    if not input_path.exists():
        raise FileNotFoundError(f"Input file not found: {input_file}")

    if stage == Stage.SPECGEN:
        problem_description = input_path.read_text().strip()
        if not problem_description:
            raise ValueError("Input file is empty")
        problem_id = input_path.stem
        return create_spec_state(problem_description, problem_id, output_file)

    elif stage == Stage.CODEGEN:
        spec_content = input_path.read_text()
        return create_velvet_state(spec_content, output_file)

    elif stage in [Stage.INVGEN, Stage.VERIFY]:
        file_content = input_path.read_text()
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

    else:
        raise ValueError(f"Unknown stage: {stage}")


def _append_history(state: SpecAgentState, coach_verdict: "CoachVerdict", coach_feedback: str) -> SpecAgentState:
    """Append the current attempt to spec_history."""
    entry = {
        "attempt": state.get("specgen_attempt", 0),
        "spec": state.get("current_spec", ""),
        "typechecks": state.get("typechecks", False),
        "build_log": state.get("build_log", ""),
        "coach_verdict": str(coach_verdict),
        "coach_feedback": coach_feedback,
    }
    history = list(state.get("spec_history", []))
    history.append(entry)
    return {**state, "spec_history": history}


def _build_pbt_feedback(pbt_result: str, pbt_detail: str) -> str:
    """Build a spec-gen-friendly coach feedback message from PBT results."""
    _hints = {
        "precond_bug": (
            "The precondition does not hold for one of the test case inputs. "
            "The precondition may be too strict, or the test case inputs may be invalid."
        ),
        "postcond_bug": (
            "The expected output in a test case does not satisfy the postcondition. "
            "The postcondition may be incorrectly formulated, or the test case expected value may be wrong."
        ),
        "bug": (
            "An alternative output was found that also satisfies the postcondition. "
            "The postcondition is underspecified — it should uniquely determine the output."
        ),
    }
    hint = _hints.get(pbt_result, "")
    parts = [f"## Property-Based Testing Bug ({pbt_result})", "", hint]
    if pbt_detail:
        parts += ["", "**Details:**", pbt_detail]
    parts += [
        "",
        "Please review and correct the specification so that all test cases pass the PBT checks.",
    ]
    return "\n".join(parts)


@DBOS.step()
def _write_fallback_spec(output_file: str, content: str) -> None:
    """Write fallback spec content to disk (DBOS step for determinism)."""
    Path(output_file).write_text(content)


@DBOS.step()
def record_spec_generation_analytics(
    state: SpecAgentState,
    pbt_enabled: bool,
    reasoning_level: str | None,
) -> None:
    """Persist one spec-generation attempt worth of analytics."""
    from utils.analytics.store import attempt as analytics_attempt
    from utils.analytics.spec_generation import (
        AttemptMeta,
        AttemptOutcome,
        CoachReview,
        PBTSummary,
        SpecPBTResult,
        TypecheckSummary,
        write_attempt_meta,
        write_coach_review,
        write_pbt_summary,
        write_typecheck_summary,
    )

    attempt_no = int(state.get("specgen_attempt", 0))
    if attempt_no <= 0:
        raise ValueError(f"Spec-generation analytics attempt must be positive, got {attempt_no}")

    spec_content = str(state.get("current_spec", ""))
    try:
        lean_file = LeanFile.from_content(spec_content)
    except Exception:
        lean_file = None

    def _section_text(name: str) -> str:
        if lean_file is None:
            return ""
        section = lean_file.get_section(name)
        return section.full_text() if section is not None else ""

    attempt_log = analytics_attempt("spec_generation", attempt_no)

    write_typecheck_summary(
        attempt_log,
        TypecheckSummary(
            build_passed=bool(state.get("typechecks", False)),
            has_axiom=bool(state.get("has_axiom", False)),
            sorry_count=int(state.get("sorry_count", 0)),
            extracted_goals_typecheck_passed=state.get("extracted_goals_typecheck_passed"),
            spec=spec_content,
            specs_section=_section_text("Specs"),
            impl_section=_section_text("Impl"),
            testcases_section=_section_text("TestCases"),
        ),
        text=str(state.get("build_log", "")),
    )

    pbt_result_raw = state.get("pbt_result", "")
    pbt_result = SpecPBTResult(pbt_result_raw) if pbt_result_raw else None
    write_pbt_summary(
        attempt_log,
        PBTSummary(
            enabled=pbt_enabled,
            result=pbt_result,
        ),
        text=str(state.get("pbt_detail", "")),
    )

    coach_verdict = state.get("coach_verdict", CoachVerdict.PENDING)
    if isinstance(coach_verdict, str):
        coach_verdict = CoachVerdict(coach_verdict)
    write_coach_review(
        attempt_log,
        CoachReview(
            verdict=coach_verdict,
            score=int(state.get("coach_score", 0)),
        ),
        text=str(state.get("coach_feedback", "")),
    )

    if not bool(state.get("typechecks", False)):
        outcome = AttemptOutcome.TYPECHECK_FAILURE
        error_message = str(state.get("build_log", ""))
    elif pbt_result in {
        SpecPBTResult.BUG,
        SpecPBTResult.PRECOND_BUG,
        SpecPBTResult.POSTCOND_BUG,
    }:
        outcome = AttemptOutcome.PBT_BUG
        error_message = str(state.get("pbt_detail", ""))
    elif coach_verdict == CoachVerdict.ACCEPT:
        outcome = AttemptOutcome.COACH_ACCEPT
        error_message = None
    elif coach_verdict == CoachVerdict.ACCEPT_WITH_MINOR_ISSUES:
        outcome = AttemptOutcome.COACH_ACCEPT_WITH_MINOR_ISSUES
        error_message = None
    else:
        outcome = AttemptOutcome.COACH_REJECT
        error_message = str(state.get("coach_feedback", ""))

    write_attempt_meta(
        attempt_log,
        AttemptMeta(
            final_outcome=outcome,
            reasoning_level=reasoning_level,
            error_message=error_message,
            file_path=state["output_file"]
        ),
    )


# =============================================================================
# Stage Runners (DBOS steps)
# =============================================================================


async def run_spec_generation(state: SpecAgentState) -> SpecAgentState:
    """Stage 1: Run specification generation workflow."""
    from container import get_container
    from stages.spec_generate import (
        typecheck_spec,
        validate_extracted_goals_typecheck,
        finalize_spec,
        save_minor_issues_spec,
    )

    logger.info("=" * 80)
    logger.info("STAGE 1: SPECIFICATION GENERATION")
    logger.info("=" * 80)

    set_allowed_output_files([state["output_file"]])

    container = get_container()

    # Read the --spec-pbt flag once (args are fixed for the session)
    from args import get_args as _get_args
    _spec_pbt_enabled = not getattr(_get_args(), "disable_spec_pbt", False)
    if _spec_pbt_enabled:
        logger.info("Spec PBT enabled: will run after coach accepts/minor-issues")
    else:
        logger.info("Spec PBT disabled")

    # Spec generation loop with coach review
    while state["specgen_attempt"] < state["specgen_max_attempt"]:
        state = {
            **state,
            "pbt_result": "",
            "pbt_detail": "",
            "extracted_goals_typecheck_passed": None,
        }

        # Generate specification
        state = cast(SpecAgentState, await container.spec_gen.run_workflow(state))

        # Typecheck
        typecheck_result = typecheck_spec(state)
        state = {**state, **typecheck_result}

        # Generic sanity check: extracted goals should typecheck as sorried theorems
        goal_check_result = await validate_extracted_goals_typecheck(state)
        state = {**state, **goal_check_result}

        # Coach review
        state = cast(SpecAgentState, await container.spec_coach.run_workflow(state))

        verdict = state.get("coach_verdict", CoachVerdict.PENDING)
        logger.info(f"Coach verdict: {verdict}, score: {state.get('coach_score', 0)}")

        if verdict in (CoachVerdict.ACCEPT, CoachVerdict.ACCEPT_WITH_MINOR_ISSUES):
            # PBT check: only run when coach is satisfied (ACCEPT or ACCEPT_WITH_MINOR_ISSUES)
            if _spec_pbt_enabled and state.get("typechecks"):
                from stages.spec_pbt import run_spec_pbt
                logger.info("Coach accepted; running spec PBT...")
                pbt_update = run_spec_pbt(state)
                state = {**state, **pbt_update}
                pbt_result = state.get("pbt_result", "")
                if pbt_result in ("bug", "precond_bug", "postcond_bug"):
                    logger.warning(f"Spec PBT found a bug ({pbt_result}), overriding verdict to REJECT")
                    pbt_detail = state.get("pbt_detail", "")
                    feedback = _build_pbt_feedback(pbt_result, pbt_detail)
                    state = _append_history(state, CoachVerdict.REJECT, feedback)
                    state = {
                        **state,
                        "coach_verdict": CoachVerdict.REJECT,
                        "coach_feedback": feedback,
                    }
                    record_spec_generation_analytics(state, _spec_pbt_enabled, container.spec_gen._current_attempt_reasoning_level(state).value)
                    continue
                # PBT passed (no_bug or synthesis_failed) — proceed with coach verdict

            if verdict == CoachVerdict.ACCEPT:
                record_spec_generation_analytics(state, _spec_pbt_enabled, container.spec_gen._current_attempt_reasoning_level(state).value)
                break
            else:
                # ACCEPT_WITH_MINOR_ISSUES and PBT passed: save as fallback, keep trying
                save_result = save_minor_issues_spec(state)
                state = {**state, **save_result}
                state = _append_history(state, verdict, state.get("coach_feedback", ""))
                record_spec_generation_analytics(state, _spec_pbt_enabled, container.spec_gen._current_attempt_reasoning_level(state).value)
        else:
            # REJECT: record history before next attempt
            state = _append_history(state, verdict, state.get("coach_feedback", ""))
            record_spec_generation_analytics(state, _spec_pbt_enabled, container.spec_gen._current_attempt_reasoning_level(state).value)

    # Use fallback if we exhausted attempts
    if state.get("coach_verdict") not in [CoachVerdict.ACCEPT, CoachVerdict.ACCEPT_WITH_MINOR_ISSUES]:
        if state.get("best_minor_issues_spec"):
            logger.info("Using fallback spec with minor issues")
            state["current_spec"] = state["best_minor_issues_spec"]
            _write_fallback_spec(state["output_file"], state["current_spec"])

    # Finalize
    finalize_result = finalize_spec(state)
    state = {**state, **finalize_result}

    logger.info("Stage 1 completed")
    return state


async def run_code_generation(state: VelvetAgentState) -> VelvetAgentState:
    """Stage 3: Run code generation workflow."""
    from container import get_container

    logger.info("")
    logger.info("=" * 80)
    logger.info("STAGE 3: CODE GENERATION")
    logger.info("=" * 80)

    container = get_container()
    state = cast(VelvetAgentState, await container.programmer.run_workflow(state))

    logger.info("Stage 3 completed")
    logger.info(f"Judge verdict: {state.get('judge_verdict', 'N/A')}")
    return state


async def run_invariant_generation(state: VelvetAgentState) -> VelvetAgentState:
    """Stage 4: Run invariant generation workflow."""
    from container import get_container

    logger.info("")
    logger.info("=" * 80)
    logger.info("STAGE 4: INVARIANT GENERATION")
    logger.info("=" * 80)

    container = get_container()
    state = cast(VelvetAgentState, await container.inferrer.run_workflow(state))

    logger.info("Stage 4 completed")
    logger.info(f"Judge verdict: {state.get('judge_verdict', 'N/A')}")
    return state


async def run_verification(state: VelvetAgentState) -> VelvetAgentState:
    """Stage 5: Run verification workflow."""
    from container import get_container
    from workflow_helpers import final_verification

    logger.info("")
    logger.info("=" * 80)
    logger.info("STAGE 5: VERIFICATION")
    logger.info("=" * 80)

    container = get_container()
    state = cast(VelvetAgentState, await container.orchestrator.run_workflow(state))

    # Final verification
    verify_result = final_verification(state)
    state = {**state, **verify_result}

    logger.info("Stage 5 completed")
    return state


# =============================================================================
# State Transitions
# =============================================================================


@DBOS.step()
def transition_spec_to_code(state: SpecAgentState) -> VelvetAgentState:
    """Transition from SpecAgentState to VelvetAgentState."""
    logger.info("")
    logger.info("=" * 80)
    logger.info("TRANSITIONING FROM SPECIFICATION TO CODE GENERATION")
    logger.info("=" * 80)

    spec_path = Path(state["output_file"])
    if not spec_path.exists():
        raise RuntimeError(f"Specification file not found: {state['output_file']}")

    specification = spec_path.read_text()

    # Determine implementation output file
    from utils.naming import derive_from_spec, OutputTarget
    impl_output_file = derive_from_spec(state["output_file"], OutputTarget.IMPL)

    logger.info(f"Implementation output file: {impl_output_file}")

    set_allowed_output_files([impl_output_file])
    return create_velvet_state(specification, impl_output_file)


def reset_for_next_stage(state: VelvetAgentState) -> VelvetAgentState:
    """Reset attempt counter and context for next stage."""
    return {
        **state,
        "attempt": 0,
        "judge_context": {},
        "continuation_ctx": {},
        "judge_reasoning": "",
    }


# =============================================================================
# Result Tracking
# =============================================================================


def get_output_result_path(output_file: str) -> str:
    """Get the path for the output_result file based on the output file."""
    from args import get_args

    output_path = Path(output_file)
    args = get_args()

    if hasattr(args, 'session_name') and args.session_name:
        sessions_dir = Path(SESSIONS_DIR) / args.session_name
        sessions_dir.mkdir(parents=True, exist_ok=True)
        result_file = sessions_dir / f"{output_path.stem}_result.json"
        result_file.parent.mkdir(parents=True, exist_ok=True)
    else:
        result_file = output_path.parent / f"{output_path.stem}_result.json"

    return str(result_file)


@DBOS.step()
def write_stage_result(output_file: str, stage: Stage, state: Dict[str, Any]) -> None:
    """Write stage result to output_result.json file."""
    result_file = get_output_result_path(output_file)

    if Path(result_file).exists():
        with open(result_file, 'r') as f:
            results = json.load(f)
    else:
        results = {}

    stage_info = {}

    if stage == Stage.SPECGEN:
        stage_info = {
            "coach_score": state.get("coach_score", 0),
            "coach_verdict": str(state.get("coach_verdict", "PENDING")),
            "passed": state.get("coach_verdict") in [CoachVerdict.ACCEPT, CoachVerdict.ACCEPT_WITH_MINOR_ISSUES],
            "typechecks": state.get("typechecks", False),
            "pbt_result": state.get("pbt_result", ""),
        }
    elif stage == Stage.CODEGEN:
        pbt_status = state.get("pbt_status", PBTStatus.NOT_ATTEMPTED)
        stage_info = {
            "testcase_passed": state.get("typechecks", False),
            "judge_verdict": str(state.get("judge_verdict", "PENDING")),
            "pbt_status": pbt_status.value if isinstance(pbt_status, PBTStatus) else pbt_status
        }
    elif stage == Stage.INVGEN:
        stage_info = {"completed": True}
    elif stage == Stage.VERIFY:
        goals = state.get("goals", [])
        stage_info = {
            "typechecks": state.get("typechecks", False),
            "goals_proven": sum(1 for g in goals if g.get("status") == GoalStatus.PROVEN),
            "goals_partial": sum(1 for g in goals if g.get("status") == GoalStatus.PARTIAL),
            "goals_total": len(goals),
        }

    results[stage.value] = stage_info

    with open(result_file, 'w') as f:
        json.dump(results, f, indent=2)

    logger.info(f"Updated result file: {result_file}")


def check_stage_failed(stage: Stage, state: Dict[str, Any]) -> bool:
    """Check if a stage has failed based on its state."""
    if stage == Stage.SPECGEN:
        verdict = state.get("coach_verdict")
        return verdict == CoachVerdict.REJECT
    elif stage in [Stage.CODEGEN, Stage.INVGEN]:
        verdict = state.get("judge_verdict")
        return verdict == JudgeVerdict.FAIL
    return False


# =============================================================================
# Main Pipeline Workflow
# =============================================================================


@log_token_usage_on_exit
@DBOS.workflow()
async def run_pipeline(
    start_stage: Stage,
    end_stage: Stage,
    input_file: str,
    output_file: str,
    session_name: Optional[str] = None,
) -> Dict[str, Any]:
    """
    Run the pipeline from start_stage to end_stage as a DBOS workflow.

    Each stage invokes the appropriate agent's workflow.

    Args:
        start_stage: Stage to start from
        end_stage: Stage to end at
        input_file: Path to input file
        output_file: Path to output file
        session_name: Optional session name for workflow identification and resumption
    """
    logger.info("=" * 80)
    logger.info("STARTING PIPELINE")
    logger.info("=" * 80)
    logger.info(f"Session: {session_name or 'unnamed'}")
    logger.info(f"Start stage: {start_stage.value}")
    logger.info(f"End stage: {end_stage.value}")
    logger.info(f"Input file: {input_file}")
    logger.info(f"Output file: {output_file}")

    # Validate stage order
    start_idx = get_stage_index(start_stage)
    end_idx = get_stage_index(end_stage)

    if start_idx > end_idx:
        raise ValueError(
            f"Start stage ({start_stage.value}) must come before or equal to end stage ({end_stage.value})"
        )

    # Load initial state
    current_state = load_input_for_stage(start_stage, input_file, output_file)

    stage_order = get_stage_order()
    stages_to_run = stage_order[start_idx:end_idx + 1]
    logger.info(f"Will execute stages: {[s.value for s in stages_to_run]}")

    # Stage runner mapping
    stage_runners = {
        Stage.SPECGEN: run_spec_generation,
        Stage.CODEGEN: run_code_generation,
        Stage.INVGEN: run_invariant_generation,
        Stage.VERIFY: run_verification,
    }

    # Stages that exit on failure
    exit_on_failure = {Stage.SPECGEN, Stage.CODEGEN, Stage.INVGEN}

    for i, stage in enumerate(stages_to_run):
        logger.info(f"Executing stage {i + 1}/{len(stages_to_run)}: {stage.value}")

        # Set output file restriction for code stages
        if stage in [Stage.CODEGEN, Stage.INVGEN, Stage.VERIFY] and stage == start_stage:
            set_allowed_output_files([output_file])

        # Run the stage
        runner = stage_runners[stage]
        current_state = await runner(current_state)

        # Write stage result
        write_stage_result(output_file, stage, current_state)

        # Check for failure
        if check_stage_failed(stage, current_state) and stage in exit_on_failure:
            logger.error(f"Stage {stage.value} failed, stopping pipeline")
            return current_state

        # Stop if this is the last stage
        if stage == end_stage:
            break

        # Transition state for next stage
        if stage == Stage.SPECGEN:
            current_state = transition_spec_to_code(current_state)
        elif stage in [Stage.CODEGEN, Stage.INVGEN]:
            current_state = reset_for_next_stage(current_state)

    logger.info("")
    logger.info("=" * 80)
    logger.info("PIPELINE COMPLETED")
    logger.info("=" * 80)
    logger.info(f"Output file: {current_state.get('output_file', output_file)}")

    return current_state


async def pipeline_workflow():
    """Async workflow for the pipeline, used by TUI runner."""
    from args import get_args

    args = get_args()

    start_stage = Stage(args.start)
    end_stage = Stage(args.end) if args.end else Stage.VERIFY
    session_name = getattr(args, 'session_name', None)
    resume = getattr(args, 'resume', False)

    from utils.dbos_utils import run_or_resume_workflow
    final_state = await run_or_resume_workflow(
        session_name=session_name,
        resume=resume,
        coro_fn=lambda: run_pipeline(
            start_stage=start_stage,
            end_stage=end_stage,
            input_file=args.input_file,
            output_file=args.output_file,
            session_name=session_name,
        ),
    )

    return final_state


async def list_workflows():
    """List all workflows in the database."""
    workflows = await DBOS.list_workflows_async()
    if not workflows:
        logger.info("No workflows found")
        return

    logger.info(f"Found {len(workflows)} workflow(s):")
    for wf in workflows:
        logger.info(f"  - ID: {wf.workflow_id}, Status: {wf.status}, Name: {wf.name}")


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
):
    """Initialize DBOS, token tracker, agent context, LLM, and the agent container.

    Must be called before running the pipeline.

    Args:
        provider: LLM provider name
        model: LLM model name
        session_name: Session name for saving results
        max_input_tokens: Token limit for input tokens
        max_output_tokens: Token limit for output tokens
        max_total_tokens: Token limit for total tokens
        max_cost: Maximum cost in USD
        agent_context: JSON string mapping agent names to context file paths
        resume: If True, load previous token counts from session
    """
    from dbos import DBOS, DBOSConfig
    from container import init_container
    from utils.token_tracker import init_token_tracker
    from utils.agent_context import init_agent_context
    from utils.message_helpers import init_message_helpers

    # Initialize token tracker first (needed by LLM callbacks)
    init_token_tracker(
        session_name=session_name,
        max_input_tokens=max_input_tokens,
        max_output_tokens=max_output_tokens,
        max_total_tokens=max_total_tokens,
        max_cost=max_cost,
        model_name=model,
        resume=resume,
    )

    # Initialize agent context
    init_agent_context(agent_context)

    # Initialize message helpers for LLM interaction logging
    init_message_helpers(session_name)

    # Initialize DBOS with SQLite.
    # Use a deterministic executor_id derived from session_name so that on
    # resume, DBOS's auto-recovery thread can find and recover pending
    # workflows (both parent and children) through the proper code path
    # (execute_workflow_by_id → start_workflow(is_recovery=True) →
    # _get_wf_invoke_func.persist() → update_workflow_outcome(SUCCESS)).
    Path(DB_DIR).mkdir(parents=True, exist_ok=True)
    config: DBOSConfig = {
        "name": "lloom-pipeline",
        "system_database_url": f"sqlite:///{DB_DIR}/lloom_pipeline.sqlite",
        "executor_id": f"pipeline-{session_name}",
        "application_version": APP_VERSION,
    }
    DBOS(config=config)

    # Initialize agent container BEFORE DBOS.launch()
    from providers import LLMConfig
    init_container(LLMConfig(provider=provider, model=model))

    # Launch DBOS
    DBOS.launch()
    logger.info("DBOS initialized and launched")


def main():
    """Entry point for the pipeline CLI command with TUI support."""
    import sys
    from args import parse_args
    from logging_config import setup_logging

    args = parse_args()

    # Handle --print-graph (no project dir needed)
    if args.print_graph:
        setup_logging(level=args.log_level, tui_mode=False)
        logger.info("Pipeline stages: specgen -> codegen -> invgen -> verify")
        logger.info("Each stage runs the corresponding agent's internal workflow graph.")
        return

    # Change to project directory early so all state (.sessions/, logs/, sqlite)
    # lives under the Lean project. This must happen before DBOS init, session
    # param loading on resume, or any relative path resolution.
    import os
    project_dir = os.path.abspath(args.project)
    if not os.path.isdir(project_dir):
        print(f"Error: --project directory does not exist: {project_dir}")
        sys.exit(1)
    os.chdir(project_dir)

    setup_logging(level=args.log_level, tui_mode=False)
    logger.info(f"Working directory: {project_dir}")

    # Handle --list-workflows (only needs DBOS, not container)
    if args.list_workflows:
        import asyncio
        from dbos import DBOS, DBOSConfig
        Path(DB_DIR).mkdir(parents=True, exist_ok=True)
        config: DBOSConfig = {
            "name": "lloom-pipeline",
            "system_database_url": f"sqlite:///{DB_DIR}/lloom_pipeline.sqlite",
            "application_version": APP_VERSION,
        }
        DBOS(config=config)
        DBOS.launch()
        asyncio.run(list_workflows())
        return

    # Validate --resume requires --session-name
    if args.resume and not args.session_name:
        print("Error: --resume requires --session-name to identify the workflow to resume")
        sys.exit(1)

    # Merge saved session params now that we're in the project dir.
    # (parse_args() doesn't do this itself since it runs before chdir.)
    from args import merge_session_params
    merge_session_params(args)

    # Validate required args (after resume merge, so saved params can provide them)
    if not args.input_file:
        print("Error: --input-file is required (not needed when using --resume)")
        sys.exit(1)
    if not args.output_file:
        print("Error: --output-file is required (not needed when using --resume)")
        sys.exit(1)
    if not args.provider:
        print("Error: --provider is required (not needed when using --resume)")
        sys.exit(1)
    if not args.model:
        print("Error: --model is required (not needed when using --resume)")
        sys.exit(1)

    # Save params for future resumption (on new workflow with session_name)
    if not args.resume and args.session_name:
        save_session_params(
            session_name=args.session_name,
            provider=args.provider,
            model=args.model,
            input_file=args.input_file,
            output_file=args.output_file,
            max_input_tokens=args.max_input_tokens,
            max_output_tokens=args.max_output_tokens,
            max_total_tokens=args.max_total_tokens,
            max_cost=args.max_cost,
            agent_context=args.agent_context,
        )

    if args.resume:
        logger.info(f"Resuming session '{args.session_name}' with provider={args.provider}, model={args.model}")

    # Initialize DBOS and container before running
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
        from tui import run
        run(pipeline_workflow)
    except KeyboardInterrupt:
        logger.info("\nInterrupted by user")
        sys.exit(130)
    except Exception as e:
        # Check for limit exceptions to provide clearer exit codes
        from utils.token_tracker import TokenLimitExceededError, CostLimitExceededError
        if isinstance(e, (TokenLimitExceededError, CostLimitExceededError)):
            logger.error(f"Limit exceeded: {e}")
            sys.exit(2)  # Different exit code for limit exceeded
        else:
            logger.error(f"Pipeline failed: {e}")
            sys.exit(1)


if __name__ == "__main__":
    main()
