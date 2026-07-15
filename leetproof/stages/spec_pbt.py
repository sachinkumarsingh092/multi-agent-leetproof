"""
Stage: Specification Property-Based Testing (spec_pbt)

This stage validates the specification by running property-based tests on the
test cases using `plausible'` / `decide` tactics. It checks:
  1. Preconditions hold for all test-case inputs
  2. Postconditions hold (expected outputs satisfy the spec)
  3. Uniqueness: no alternative output satisfies the spec

Result values stored in state["pbt_result"]:
  "no_bug"          – all checks passed
  "bug"             – uniqueness counter-example found
  "precond_bug"     – a test-case input violates the precondition
  "postcond_bug"    – a test-case expected output violates the postcondition
  "synthesis_failed"– property-based testing was inconclusive
"""

from dbos import DBOS
from agents.spec_state import SpecAgentState
from logging_config import get_logger

logger = get_logger(__name__)


def _derive_pbt_file(spec_file: str) -> str:
    """Return the path for the temporary PBT verification-def file."""
    if spec_file.endswith("Spec.lean"):
        return spec_file.replace("Spec.lean", "SpecPbt.lean")
    if spec_file.endswith("_spec.lean"):
        return spec_file.replace("_spec.lean", "_spec_pbt.lean")
    if spec_file.endswith(".lean"):
        return spec_file[:-5] + "_pbt.lean"
    return spec_file + "_pbt.lean"


@DBOS.step()
def run_spec_pbt(state: SpecAgentState) -> dict:
    """Run property-based testing on the specification.

    Returns a dict with a single key ``pbt_result`` whose value is one of:
    ``"no_bug"``, ``"bug"``, ``"precond_bug"``, ``"postcond_bug"``,
    ``"synthesis_failed"``.
    """
    from utils.spec_bug_finder import generate_and_check
    from utils.lean.build import find_project_root

    spec_file = state["output_file"]
    pbt_file = _derive_pbt_file(spec_file)
    build_dir = find_project_root(spec_file)

    logger.info("")
    logger.info("=" * 80)
    logger.info("SPEC PBT: PROPERTY-BASED TESTING OF SPECIFICATION")
    logger.info("=" * 80)
    logger.info(f"Spec file : {spec_file}")
    logger.info(f"PBT file  : {pbt_file}")
    logger.info(f"Build dir : {build_dir}")

    result, detail = generate_and_check(spec_file, pbt_file, build_dir)

    logger.info("")
    logger.info("=" * 80)
    logger.info(f"SPEC PBT RESULT: {result}")
    if detail:
        logger.info(f"DETAIL:\n{detail}")
    logger.info("=" * 80)

    return {"pbt_result": result, "pbt_detail": detail}
