"""
Stage 1: Specification Generation

This stage generates a formal specification from a problem description.
It includes generation, typechecking, coach review, and optional conciseness fixes.

NOTE: This module is deprecated for workflow creation. Use pipeline.run_spec_generation() instead,
which uses the container pattern for proper DBOS integration. Helper functions like
typecheck_spec, finalize_spec, and save_minor_issues_spec are still used.
"""

import re
from pathlib import Path

from dbos import DBOS
from langgraph.graph import StateGraph, START, END
from agents.spec_state import SpecAgentState, CoachVerdict
from logging_config import get_logger
from utils.lean.parser import LeanFile

logger = get_logger(__name__)


# Node names
CHECK_ATTEMPT = "check_attempt"
GENERATE_SPEC = "generate_spec"
TYPECHECK_SPEC = "typecheck_spec"
COACH_SPEC = "coach_spec"
SAVE_MINOR_ISSUES_SPEC = "save_minor_issues_spec"
FINALIZE_SPEC = "finalize_spec"
CLEAR_COACH_STATE = "clear_coach_state"
USE_FALLBACK_SPEC = "use_fallback_spec"
FAILURE = "spec_gen_failure"


def remove_prove_correct_sorry(file_path: str) -> bool:
    """Remove the 'prove_correct FuncName by sorry' line from the specification.

    Args:
        file_path: Path to the specification file

    Returns:
        True if the line was found and removed, False otherwise
    """
    try:
        content = Path(file_path).read_text()

        # Pattern to match: prove_correct <FuncName> by sorry (with optional whitespace)
        pattern = r"^\s*prove_correct\s+\w+\s+by\s+sorry\s*$"

        # Remove the line (multiline mode)
        new_content, count = re.subn(pattern, "", content, flags=re.MULTILINE)

        if count > 0:
            Path(file_path).write_text(new_content)
            logger.info(
                f"Removed {count} 'prove_correct ... by sorry' line(s) from {file_path}"
            )
            return True
        else:
            logger.warning(f"No 'prove_correct ... by sorry' line found in {file_path}")
            return False

    except Exception as e:
        logger.error(f"Error removing prove_correct line: {e}")
        return False


@DBOS.step()
def finalize_spec(state: SpecAgentState) -> dict:
    """Finalize the specification by removing the prove_correct sorry line."""
    logger.info("Finalizing specification: removing prove_correct sorry line")

    if not state["output_file"]:
        logger.error("No output file specified")
        return state

    remove_prove_correct_sorry(state["output_file"])

    # Update current_spec in state
    try:
        updated_spec = Path(state["output_file"]).read_text()
        return {"current_spec": updated_spec}
    except Exception as e:
        logger.error(f"Error reading finalized spec: {e}")
        return state


@DBOS.step()
def typecheck_spec(state: SpecAgentState) -> dict:
    """Typecheck the specification with strict validation."""
    logger.info("Running typecheck with strict validation")

    if not state["output_file"]:
        logger.error("No output file specified")
        return {
            "typechecks": False,
            "build_log": "No output file specified",
            "has_axiom": False,
            "sorry_count": 0,
        }

    # Validate output structure (required sections)
    from agents.spec_gen import validate_specgen_output
    from pathlib import Path

    spec_content = Path(state["output_file"]).read_text()
    validation_result = validate_specgen_output(spec_content)
    if validation_result.has_error():
        logger.warning(
            f"SpecGen output validation failed: {validation_result.get_error()}"
        )
        return {
            "typechecks": False,
            "build_log": validation_result.get_error(),
            "has_axiom": False,
            "sorry_count": 0,
        }
    logger.info("Output validation passed (required sections present)")

    from tools.spec_gen_tools import lean_build_with_validation_helper

    return lean_build_with_validation_helper(state["output_file"])


@DBOS.step()
async def validate_extracted_goals_typecheck(state: SpecAgentState) -> dict:
    """Validate that extracted loom_solve goals typecheck as sorried theorems.

    This check runs only when the generated file has an Impl section that
    contains a parseable Velvet method.
    """
    output_file = state.get("output_file", "")
    if not output_file:
        logger.warning("Skipping extracted-goal validation: missing output file")
        return {"extracted_goals_typecheck_passed": None}

    if not state.get("typechecks", False):
        logger.info("Skipping extracted-goal validation: spec does not typecheck")
        return {"extracted_goals_typecheck_passed": None}

    try:
        file_content = Path(output_file).read_text()
        lean_file = LeanFile.from_content(file_content)
    except Exception as e:
        logger.warning(f"Skipping extracted-goal validation: cannot read/parse file ({e})")
        return {"extracted_goals_typecheck_passed": None}

    if not lean_file.has_section("Impl"):
        logger.info("Skipping extracted-goal validation: missing Impl section")
        return {"extracted_goals_typecheck_passed": None}

    impl_content = lean_file.get_section("Impl", assert_exists=True).content

    # Only run when Impl has an actual Velvet method
    try:
        from utils.velvet_helpers import get_velvet_method
        _ = get_velvet_method(impl_content)
    except Exception:
        logger.info("Skipping extracted-goal validation: no parseable Velvet method in Impl")
        return {"extracted_goals_typecheck_passed": None}

    try:
        from utils.velvet_helpers import (
            extract_goals_after_loom_solve,
            remove_pbt_section,
            identity,
        )
        from utils.lean.goals import parse_lean_goals
        from utils.lean.constants import (
            PANTOGRAPH_CORE_OPTIONS,
            PANTOGRAPH_OPTIONS,
            VELVET_IMPORTS,
        )
        from tools.pantograph_client import PantographClient
        from utils.lean.build import find_project_root

        goal_result_str, _ = await extract_goals_after_loom_solve(
            file_content,
            output_file,
            preprocess=remove_pbt_section,
            postprocess=identity,
        )
        goals = parse_lean_goals(goal_result_str) if goal_result_str.strip() else []

        if not goals:
            logger.info("Extracted-goal validation: no remaining goals")
            return {"extracted_goals_typecheck_passed": True}

        project_path = find_project_root(output_file)
        client = PantographClient(
            imports=VELVET_IMPORTS,
            project_path=project_path,
            options=PANTOGRAPH_OPTIONS,
            core_options=PANTOGRAPH_CORE_OPTIONS,
        )

        failures: list[str] = []
        try:
            for goal in goals:
                build = await client.check_build(goal.as_sorried())
                if build.typechecks:
                    continue

                case = f" ({goal.case_tag})" if goal.case_tag else ""
                failures.append(
                    f"- Goal `{goal.name}`{case} does not typecheck as sorry.\n"
                    f"  Error: {build.as_string(['error'])}"
                )
        finally:
            client.close()

        if not failures:
            logger.info("Extracted-goal validation passed")
            return {"extracted_goals_typecheck_passed": True}

        feedback = (
            "## Goal Extraction Sanity Check Failed\n\n"
            "After extracting goals from `loom_solve <;> (try injections; try subst_vars; try expose_names)`, "
            "some extracted goals do not typecheck even as `sorry` placeholders. "
            "This usually means simplification produced unstable/unusable extracted goals.\n\n"
            "Please rewrite the generated specification/method in a simpler form "
            "(e.g., avoid brittle expressions and prefer explicit, stable formulations) "
            "and try again.\n\n"
            "Ill-typed extracted goals:\n"
            + "\n".join(failures)
        )
        logger.warning("Extracted-goal validation failed")
        return {
            "typechecks": False,
            "build_log": f"{state.get('build_log', '')}\n\n{feedback}".strip(),
            "extracted_goals_typecheck_passed": False,
        }
    except Exception as e:
        logger.warning(f"Extracted-goal validation failed unexpectedly; skipping check: {e}")
        return {"extracted_goals_typecheck_passed": None}


def fail(state: SpecAgentState):
    """Handle specification generation failure."""
    logger.error("SPECIFICATION GENERATION FAILED")
    return state


@DBOS.step()
def save_minor_issues_spec(state: SpecAgentState) -> dict:
    """Save the current specification as the best minor issues spec."""
    current_score = state.get("coach_score", 0)
    best_score = state.get("best_minor_issues_score", 0)

    # Only save if this is better than the previously saved one
    if current_score > best_score:
        logger.info(f"Saving current spec as best minor issues spec (score: {current_score})")
        return {
            "best_minor_issues_spec": state["current_spec"],
            "best_minor_issues_score": current_score,
            "best_minor_issues_typechecks": state.get("typechecks", False),
            "best_minor_issues_coach_verdict": state.get("coach_verdict", state.get("coach_verdict", CoachVerdict.PENDING)),
        }
    else:
        logger.info(f"Current score ({current_score}) not better than best ({best_score}), keeping previous best")
        return {}


def clear_coach_state_for_retry(state: SpecAgentState) -> dict:
    """Clear coach-related state when typecheck fails and we're retrying generation."""
    logger.info("Clearing coach state for typecheck failure retry")

    return {
        "coach_verdict": CoachVerdict.PENDING,
        "coach_feedback": "",
        "coach_score": 0,
    }


def use_fallback_spec(state: SpecAgentState) -> dict:
    """Use the best minor issues specification as the final result."""
    best_spec = state.get("best_minor_issues_spec", "")
    best_score = state.get("best_minor_issues_score", 0)

    if best_spec:
        logger.info(f"Using fallback spec with score {best_score} as final specification")
        # Write the best spec to the output file
        if state["output_file"]:
            try:
                Path(state["output_file"]).write_text(best_spec)
                logger.info(f"Wrote fallback spec to {state['output_file']}")
            except Exception as e:
                logger.error(f"Error writing fallback spec: {e}")

        return {
            "current_spec": best_spec,
            "typechecks": state.get("best_minor_issues_typechecks", False),
            "coach_verdict": state.get("best_minor_issues_coach_verdict", CoachVerdict.PENDING),
        }
    else:
        logger.warning("No fallback spec available, keeping current spec")
        return {}


def check_attempt_node(state: SpecAgentState) -> dict:
    """Node that just passes through state - routing handled separately."""
    return {}


def route_attempt_check(state: SpecAgentState) -> str:
    """Check if we should continue generating or use fallback."""
    current_attempt = state.get("specgen_attempt", 0)
    max_attempt = state.get("specgen_max_attempt", 10)

    logger.info(f"Checking attempt: {current_attempt}/{max_attempt}")

    if current_attempt >= max_attempt:
        logger.info("Reached maximal attempt before generation.")
        # Check if we have a fallback spec to use
        if state.get("best_minor_issues_spec"):
            logger.info("Using fallback spec with minor issues")
            return "USE_FALLBACK"
        else:
            logger.info("No fallback spec available. Fail to generate a good specification.")
            return "FAIL"
    else:
        logger.info("Continue with generation")
        return "CONTINUE_GENERATE"


def check_typecheck_result(state: SpecAgentState) -> str:
    """Check typecheck result and route accordingly."""
    typechecks = state.get("typechecks", False)
    logger.info(f"Typecheck result: {typechecks}")

    if typechecks:
        return "TYPECHECK_PASSED"
    else:
        logger.info("Typecheck failed, retrying generation")
        return "TYPECHECK_FAILED_RETRY"


def check_coach_verdict(state: SpecAgentState) -> str:
    """Check if coach verdict is ACCEPT, ACCEPT_WITH_MINOR_ISSUES, or REJECT_AND_RETRY."""
    verdict = state.get("coach_verdict", CoachVerdict.PENDING)
    logger.info(f"Coach verdict check: {verdict}")

    if verdict == CoachVerdict.ACCEPT:
        return "ACCEPT"
    elif verdict == CoachVerdict.ACCEPT_WITH_MINOR_ISSUES:
        logger.info("ACCEPT_WITH_MINOR_ISSUES - saving spec and continuing to retry")
        return "ACCEPT_WITH_MINOR_ISSUES"
    else:
        logger.info("REJECT - will retry generation")
        return "REJECT_AND_RETRY"




def create_spec_generate_workflow():
    """
    Create the specification generation workflow.

    Returns a compiled StateGraph that:
    1. Generates a specification from problem description
    2. Typechecks the specification
    3. Gets coach review
    4. Saves specs with minor issues as fallback
    5. Removes the prove_correct sorry line
    6. Retries if needed, uses fallback if no perfect spec found

    NOTE: Prefer using pipeline.run_spec_generation() which uses the container.
    """
    from container import get_container

    workflow = StateGraph(SpecAgentState)

    container = get_container()

    # Add nodes
    workflow.add_node(CHECK_ATTEMPT, check_attempt_node)
    workflow.add_node(GENERATE_SPEC, container.spec_gen.as_node())
    workflow.add_node(TYPECHECK_SPEC, typecheck_spec)
    workflow.add_node(COACH_SPEC, container.spec_coach.as_node())
    workflow.add_node(SAVE_MINOR_ISSUES_SPEC, save_minor_issues_spec)
    workflow.add_node(FINALIZE_SPEC, finalize_spec)
    workflow.add_node(CLEAR_COACH_STATE, clear_coach_state_for_retry)
    workflow.add_node(USE_FALLBACK_SPEC, use_fallback_spec)
    workflow.add_node(FAILURE, fail)

    # Define edges
    workflow.add_edge(START, CHECK_ATTEMPT)

    # Attempt check routing
    workflow.add_conditional_edges(
        CHECK_ATTEMPT,
        route_attempt_check,
        {
            "CONTINUE_GENERATE": GENERATE_SPEC,
            "USE_FALLBACK": USE_FALLBACK_SPEC,
            "FAIL": FAILURE,
        },
    )

    workflow.add_edge(GENERATE_SPEC, TYPECHECK_SPEC)

    workflow.add_edge(TYPECHECK_SPEC, COACH_SPEC)

    # # Typecheck result routing
    # workflow.add_conditional_edges(
    #     TYPECHECK_SPEC,
    #     check_typecheck_result,
    #     {
    #         "TYPECHECK_PASSED": COACH_SPEC,
    #         "TYPECHECK_FAILED_RETRY": CLEAR_COACH_STATE,
    #     },
    # )

    # # After clearing coach state, go to attempt check
    # workflow.add_edge(CLEAR_COACH_STATE, CHECK_ATTEMPT)

    # Coach verdict routing
    workflow.add_conditional_edges(
        COACH_SPEC,
        check_coach_verdict,
        {
            "ACCEPT": FINALIZE_SPEC,
            "ACCEPT_WITH_MINOR_ISSUES": SAVE_MINOR_ISSUES_SPEC,
            "REJECT_AND_RETRY": CHECK_ATTEMPT,
        },
    )

    # After saving minor issues spec, continue trying to generate
    workflow.add_edge(SAVE_MINOR_ISSUES_SPEC, CHECK_ATTEMPT)

    # After using fallback spec, finalize it
    workflow.add_edge(USE_FALLBACK_SPEC, FINALIZE_SPEC)

    # After finalization, we're done
    workflow.add_edge(FINALIZE_SPEC, END)
    workflow.add_edge(FAILURE, END)

    return workflow.compile()
