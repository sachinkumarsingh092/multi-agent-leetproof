"""
Stage 2: Specification Validation

This stage validates the specification by generating and proving concrete examples.
It generates example verification file and proves the examples using ProverAgent.
"""

from pathlib import Path

from dbos import DBOS
from langgraph.graph import StateGraph, START, END
from agents.spec_state import SpecAgentState
from logging_config import get_logger
from config.limits import Limits
from utils.lean.parser import parse_theorem
from utils.proof_types import ProvingContext
from utils.lean.build import find_project_root
from utils.lean.constants import (
    PANTOGRAPH_CORE_OPTIONS,
    PANTOGRAPH_OPTIONS,
    SPEC_VALIDATE_IMPORTS,
)
from tools.pantograph_client import PantographClient, PantographFactory
from utils.example_verify import generate_verification_file
from utils.shutdown import shutdown_boundary, shutdown_hook, ShutdownHookMode

logger = get_logger(__name__)


# Node names
GENERATE_EXAMPLE_VERIFY = "generate_example_verify"
PROVE_EXAMPLES = "prove_examples"


@shutdown_boundary("before spec validation generate-verify step")
@DBOS.step()
def generate_example_verify_file(state: SpecAgentState) -> dict:
    """Generate the example verification file from the specification."""
    logger.info("Generating example verification file")

    from utils.naming import derive_from_spec, OutputTarget
    spec_file = state["output_file"]
    verify_file = derive_from_spec(spec_file, OutputTarget.EXAMPLE_VERIFY)

    try:
        generate_verification_file(spec_file, verify_file)
        logger.info(f"Successfully generated {verify_file}")

        # Read the generated file
        if Path(verify_file).exists():
            verify_content = Path(verify_file).read_text()
            if not verify_content.strip():
                error_msg = f"Verification file generated but is empty: {verify_file}"
                logger.error(error_msg)
                raise RuntimeError(error_msg)
        else:
            error_msg = f"Verification file not found at {verify_file}"
            logger.error(error_msg)
            raise RuntimeError(error_msg)

        return {
            "example_verify_file": verify_file,
            "example_verify_content": verify_content
        }
    except RuntimeError:
        raise
    except Exception as e:
        error_msg = f"Failed to generate verification file: {e}"
        logger.error(error_msg)
        raise RuntimeError(error_msg) from e


def extract_test_case_theorems(lean_content: str) -> list[str]:
    """Extract test case lemmas/theorems that need proving from verification file.

    Uses extract_theorems_with_sorry to find all theorems with 'by sorry' proofs.

    Returns:
        List of theorem statements (including 'by sorry' for ProverAgent)
    """
    from utils.lean.parser import extract_theorems_with_sorry

    theorems = extract_theorems_with_sorry(lean_content)

    logger.info(f"Extracted {len(theorems)} test case theorems to prove")
    for i, thm in enumerate(theorems, 1):
        # Log first 80 chars of each theorem
        preview = thm.replace('\n', ' ')[:80]
        logger.info(f"  [{i}] {preview}...")

    return theorems


@shutdown_boundary("before spec validation prepare-verify step")
@DBOS.step()
def _prepare_verify_file(verify_file: str, verify_content: str) -> str:
    """Clear the Proof section in verify file, leaving base content for ProverAgent."""
    from utils.lean.parser import LeanFile
    lean_file = LeanFile.from_content(verify_content)
    lean_file.clear_section("Proof")
    content = lean_file.reconstruct()
    Path(verify_file).write_text(content)
    logger.info(f"Prepared verify file: {verify_file}")
    logger.info(f"Base content has {len(content.split(chr(10)))} lines")
    return content


@DBOS.step()
def _write_proof_result(verify_file: str, content: str) -> None:
    """Write proof result content to verify file (DBOS replay-safe)."""
    Path(verify_file).write_text(content)


def _write_remaining_theorems_as_sorries(
    verify_file: str,
    remaining_theorems: list[str],
) -> None:
    """Write the remaining example theorems back as sorried proofs on shutdown."""
    if not remaining_theorems:
        return

    from utils.lean.parser import LeanFile

    current_content = Path(verify_file).read_text() if Path(verify_file).exists() else ""
    lean_file = LeanFile.from_content(current_content)
    lean_file.append_in_section(
        "Proof",
        "\n\n" + "\n\n".join(remaining_theorems),
        assert_section_present=True,
    )
    lean_file.reconstruct_and_write_to_file(Path(verify_file))
    logger.info(
        f"Shutdown snapshot wrote {len(remaining_theorems)} remaining theorem(s) as sorry to {verify_file}"
    )


@shutdown_boundary("before spec validation final-typecheck step")
@DBOS.step()
def _final_typecheck(verify_file: str):
    """Run final typecheck on the complete verify file."""
    from tools.common import lean_build_file_helper
    return lean_build_file_helper(verify_file)


@DBOS.workflow()
async def run_example_prover_workflow(state: SpecAgentState) -> SpecAgentState:
    """Run ProverAgent to prove test case lemmas.

    This is a @DBOS.workflow() so that inner steps (_prepare_verify_file,
    _write_proof_result, _final_typecheck) have proper workflow context.
    Workflow-calling-workflow (prove()) is supported by DBOS.
    """
    from container import get_container

    logger.info("")
    logger.info("=" * 80)
    logger.info("PROVING TEST CASES WITH ProverAgent")
    logger.info("=" * 80)

    verify_file = state["example_verify_file"]
    verify_content = state.get("example_verify_content", "")

    if not verify_content:
        verify_content = Path(verify_file).read_text()

    # Extract all test case theorems (lemmas with 'by sorry')
    test_theorems = extract_test_case_theorems(verify_content)

    if not test_theorems:
        logger.warning("No test case theorems found to prove")
        return {
            "example_verify_content": verify_content,
            "proof_typechecks": False,
            "proof_build_log": "No theorems found to prove",
            "proof_attempt": 0,
        }

    # Get ProverAgent from container
    container = get_container()
    prover = container.prover

    # Strip sorry theorems, write base content to verify file
    _prepare_verify_file(verify_file, verify_content)

    from utils.proof_types import (
        PantographParams,
        AttemptBudgetConfigBundle,
        AttemptBudgetConfig,
        AttemptBudgetMode,
    )
    from utils.lean.constants import VELVET_AUTOMATION
    from utils.context_utils import DefsAndTheoremsExtractor
    project_path = find_project_root(verify_file)

    # Prove each theorem sequentially, working on verify_file directly
    total_failures = []
    proven_count = 0

    attempt_budgets = AttemptBudgetConfigBundle(
        shallow=AttemptBudgetConfig(
            mode=AttemptBudgetMode.UP,
            base=10,
            slope=0,
            min_attempts=10,
            max_attempts=10,
        ),
        decomposition=AttemptBudgetConfig(
            mode=AttemptBudgetMode.DOWN,
            base=10,
            slope=2,
            min_attempts=5,
            max_attempts=10,
        ),
    )

    from utils.shutdown import handle_shutdown_if_requested

    for i, theorem_stmt in enumerate(test_theorems, 1):
        handle_shutdown_if_requested(f"before proving example theorem {i}/{len(test_theorems)}")

        logger.info("")
        logger.info(f"--- Proving theorem {i}/{len(test_theorems)} ---")
        logger.info(f"Theorem: {theorem_stmt[:100]}...")

        # Parse theorem into Goal object for ProverAgent
        goal = parse_theorem(theorem_stmt)

        ctx = ProvingContext(
            file_path=verify_file,
            goal=goal,
            sections=["Specs", "TestCases", "Proof"],
            pantograph=PantographParams(
                key=goal.name,
                project_path=project_path,
                imports=SPEC_VALIDATE_IMPORTS,
                options=PANTOGRAPH_OPTIONS,
                core_options=PANTOGRAPH_CORE_OPTIONS,
            ),
            automation_tactics=VELVET_AUTOMATION,
            informal_reasoning="",
            context_extractor=DefsAndTheoremsExtractor(),
            attempt_budgets=attempt_budgets,
            hint_sections=["Specs"],
        )

        # prove works directly on verify_file using temp sections
        remaining_theorems = test_theorems[i - 1:]
        try:
            with shutdown_hook(
                ShutdownHookMode.CLEAR_AND_PUSH,
                lambda: _write_remaining_theorems_as_sorries(
                    verify_file=verify_file,
                    remaining_theorems=remaining_theorems,
                ),
            ):
                result = await prover.prove(
                    ctx=ctx,
                    max_depth=1,
                )
        finally:
            PantographFactory.cleanup(ctx.pantograph.key)

        # Write result.content back for DBOS replay safety — prove_goal's
        # @DBOS.step() side effects are skipped on replay.
        _write_proof_result(verify_file, result.content)

        if result.success and not result.has_sorry:
            logger.info(f"✓ Theorem {i} proved successfully")
            proven_count += 1
        else:
            logger.warning(f"✗ Theorem {i} failed or has sorry")
            logger.warning(f"  Error: {result.error}")
            total_failures.extend(result.failures)

            if result.failures:
                logger.info(f"  Failure summary:\n{result.get_failure_summary()}")

            # Stop proving on first failure
            logger.warning(f"Stopping proof attempts due to failure at theorem {i}/{len(test_theorems)}")
            break

    # Final typecheck
    logger.info("")
    logger.info("=" * 80)
    logger.info("FINAL TYPECHECK OF ALL TEST CASES")
    logger.info("=" * 80)

    tc = _final_typecheck(verify_file)

    if tc.typechecks:
        logger.info("✓ All test cases typecheck successfully!")
    else:
        logger.error("✗ Final typecheck failed")
        logger.error(f"Build log:\n{tc.build_log}")

    logger.info("")
    logger.info("=" * 80)
    logger.info("TEST CASE PROVING COMPLETE")
    logger.info("=" * 80)
    logger.info(f"Proven theorems: {proven_count}/{len(test_theorems)}")
    logger.info(f"Typechecks: {tc.typechecks}")
    logger.info("=" * 80)

    final_content = Path(verify_file).read_text()

    # Update state with proof results
    updated_state = state.copy()
    updated_state["example_verify_content"] = final_content
    updated_state["proof_typechecks"] = tc.typechecks
    updated_state["proof_build_log"] = tc.build_log
    updated_state["proof_attempt"] = len(test_theorems)
    updated_state["proven_count"] = proven_count

    return updated_state


def create_spec_validate_workflow():
    """
    Create the specification validation workflow.

    Returns a compiled StateGraph that:
    1. Generates example verification file from specification
    2. Proves the test case lemmas using ProverAgent with recursive decomposition
    """
    workflow = StateGraph(SpecAgentState)

    # Add nodes
    workflow.add_node(GENERATE_EXAMPLE_VERIFY, generate_example_verify_file)
    workflow.add_node(PROVE_EXAMPLES, run_example_prover_workflow)

    # Define edges
    workflow.add_edge(START, GENERATE_EXAMPLE_VERIFY)
    workflow.add_edge(GENERATE_EXAMPLE_VERIFY, PROVE_EXAMPLES)
    workflow.add_edge(PROVE_EXAMPLES, END)

    return workflow.compile()
