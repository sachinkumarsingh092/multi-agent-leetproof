"""Timeout configurations for all external services and processes.

Centralizes all timeout values that were previously scattered throughout the codebase.
"""


class Timeouts:
    """Timeout values (in seconds) for various operations."""

    # Lean toolchain timeouts
    LEAN_BUILD = 180                 # Lean lake build process
    LEAN_EXPLORE = 30                # Lean exploration queries (if used)
    PROOF_SEARCH = 5                # Global wall-clock budget for Pantograph proof search
    
    # Script execution timeouts
    EXAMPLE_VERIFY = 60              # Example verify script execution
    SPEC_VALIDATE = 60               # Spec validation script execution
    
    # Async/TUI timeouts
    ASYNC_WAIT = 2.0                 # Generic async wait operations
    WORKFLOW_THREAD_JOIN = 120.0     # Workflow thread join timeout (wait for current LLM call to finish)
    PROCESS_WAIT = 5                 # Generic process wait timeout
