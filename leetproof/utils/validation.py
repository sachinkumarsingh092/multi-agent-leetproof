"""Validation utilities for agent states and workflows."""

from logging_config import get_logger

logger = get_logger(__name__)


def validate_output_file(state: dict, extra_fields: dict | None = None) -> tuple[bool, dict]:
    """
    Validate that output_file is specified in state.
    
    This eliminates duplicated validation checks across agents.
    
    Args:
        state: Agent state dict containing 'output_file' key
        extra_fields: Optional dict of additional fields to include in error state
                     (e.g., for spec validation: {"has_axiom": False, "sorry_count": 0})
        
    Returns:
        Tuple of (is_valid: bool, error_state: dict)
        - If valid: (True, {})
        - If invalid: (False, {"typechecks": False, "build_log": "error message", ...extra_fields})
        
    Example:
        is_valid, error_state = validate_output_file(state)
        if not is_valid:
            return error_state
            
        # With extra fields for spec validation:
        is_valid, error_state = validate_output_file(
            state, 
            extra_fields={"has_axiom": False, "sorry_count": 0}
        )
        if not is_valid:
            return error_state
    """
    file_path = state.get("output_file", "")
    if not file_path:
        logger.error("No output file specified")
        error_state = {
            "typechecks": False,
            "build_log": "No output file specified"
        }
        # Merge in any extra fields
        if extra_fields:
            error_state.update(extra_fields)
        return False, error_state
    
    return True, {}
