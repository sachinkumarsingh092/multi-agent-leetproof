"""Validation result type for agent validators."""

from dataclasses import dataclass
from typing import Optional


@dataclass
class ValidationResult:
    """Result of a validation check."""
    error_message: Optional[str] = None

    def has_error(self) -> bool:
        """Check if validation failed."""
        return self.error_message is not None

    def is_ok(self) -> bool:
        """Check if validation passed."""
        return self.error_message is None

    def get_error(self) -> str:
        """Get error message. Raises if no error."""
        if self.error_message is None:
            raise RuntimeError("No error - validation passed")
        return self.error_message

    @staticmethod
    def ok() -> "ValidationResult":
        """Create a successful validation result."""
        return ValidationResult(error_message=None)

    @staticmethod
    def error(message: str) -> "ValidationResult":
        """Create a failed validation result."""
        return ValidationResult(error_message=message)
