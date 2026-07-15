"""Configuration module for LLoom Agent.

This module centralizes all configuration constants including timeouts, retry limits,
and other magic numbers that were previously scattered throughout the codebase.
"""

from config.timeouts import Timeouts
from config.limits import Limits

__all__ = ["Timeouts", "Limits"]
