"""Shared helper functions for workflow nodes."""

from dbos import DBOS

from agents.agent_state import VelvetAgentState
from tools.common import lean_build_file_helper
from utils.validation import validate_output_file
from logging_config import get_logger

logger = get_logger(__name__)


@DBOS.step()
def final_verification(state: VelvetAgentState) -> dict:
    """Run final lake build to verify the complete proof."""
    logger.info("Running final verification")

    is_valid, error_state = validate_output_file(state)
    if not is_valid:
        return error_state

    file_path = state.get("output_file", "")

    result = lean_build_file_helper(file_path)

    if result.typechecks:
        logger.info("="*80)
        logger.info("SUCCESS! Complete proof verified!")
        logger.info("="*80)
    else:
        logger.error("="*80)
        logger.error("Final verification failed")
        logger.error("="*80)

    # Serialize diagnostics for DBOS persistence
    return {
        "typechecks": result.typechecks,
        "build_log": result.as_string(["error"]),
        "diagnostics": [d.to_dict() for d in result.diagnostics]
    }
