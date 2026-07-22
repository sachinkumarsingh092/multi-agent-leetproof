"""File naming utilities for LLoom output files."""

from enum import Enum


class OutputTarget(Enum):
    """Target output file type derived from a spec file."""

    LEAN_IMPL = "lean_impl"

    @property
    def pascal_suffix(self) -> str:
        return {
            OutputTarget.LEAN_IMPL: "LeanImpl.lean",
        }[self]

    @property
    def snake_suffix(self) -> str:
        return {
            OutputTarget.LEAN_IMPL: "_lean_impl.lean",
        }[self]


def derive_from_spec(input_file: str, target: OutputTarget) -> str:
    """Derive an output file path from a spec input file.

    Handles both PascalCase and snake_case specification names.

    Args:
        input_file: Path to the input file.
        target: The output target type.

    Returns:
        Derived output file path.
    """
    if input_file.endswith("Spec.lean"):
        return input_file.replace("Spec.lean", target.pascal_suffix)
    elif input_file.endswith("_spec.lean"):
        return input_file.replace("_spec.lean", target.snake_suffix)
    elif input_file.endswith(".lean"):
        return input_file[:-5] + target.snake_suffix
    else:
        return input_file + target.snake_suffix
