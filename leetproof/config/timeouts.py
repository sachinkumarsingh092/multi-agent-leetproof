"""Timeout configurations for all external services and processes.

Centralizes all timeout values that were previously scattered throughout the codebase.
"""


class Timeouts:
    """Timeout values (in seconds) for various operations."""

    # Lean toolchain timeouts
    LEAN_BUILD = 180                 # Lean lake build process
    PROOF_SEARCH = 5                # Global wall-clock budget for Pantograph proof search
    LEAN_EXPLORE_INIT = 120          # Embedding model and local index initialization
    LEAN_EXPLORE_SEARCH = 60         # One semantic-search request
