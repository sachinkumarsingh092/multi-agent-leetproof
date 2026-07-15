"""Normalization helpers for externally extracted Lean text."""


def _find_atomic_expr_start(text: str, end_idx: int) -> int:
    """Find the start of the atomic expression ending at ``end_idx``."""
    depth_round = 0
    depth_square = 0
    depth_brace = 0
    separators = set(" \t\n\r,;:+-*/<>=|&")

    i = end_idx
    while i >= 0:
        ch = text[i]

        if ch == ')':
            depth_round += 1
        elif ch == ']':
            depth_square += 1
        elif ch == '}':
            depth_brace += 1
        elif ch == '(':
            if depth_round > 0:
                depth_round -= 1
            else:
                return i
        elif ch == '[':
            if depth_square > 0:
                depth_square -= 1
            else:
                return i + 1
        elif ch == '{':
            if depth_brace > 0:
                depth_brace -= 1
            else:
                return i + 1
        elif depth_round == 0 and depth_square == 0 and depth_brace == 0 and ch in separators:
            return i + 1

        i -= 1

    return 0


def _repair_nested_getelem_syntax(text: str) -> str:
    """Repair malformed nested ``[]!`` chains from extracted Lean text."""
    repaired = text

    while True:
        changed = False
        i = 1
        while i + 1 < len(repaired):
            if repaired[i] == '!' and repaired[i + 1] == '[' and repaired[i - 1] == ']':
                start = _find_atomic_expr_start(repaired, i)
                repaired = repaired[:start] + "(" + repaired[start:i + 1] + ")" + repaired[i + 1:]
                changed = True
                i = start + 1
            else:
                i += 1
        if not changed:
            return repaired

def normalize_extracted_expr(text: str) -> str:
    """Normalize externally extracted Lean expression text.

    This is the single shared entrypoint for text repairs applied at extraction
    boundaries. Additional normalization passes should be chained here.
    """
    return _repair_nested_getelem_syntax(text)


def _annotate_array_shape_uses(text: str) -> str:
    if not text or "#[]" not in text:
        return text
    return text.replace("#[].size", "(#[] : Array a_dummy).size")


def _annotate_list_shape_uses(text: str) -> str:
    if not text or "[]" not in text:
        return text
    return text.replace("[].length", "([] : List a_dummy).length")


def normalize_extracted_goal_fields(
    param_types: list[str],
    final_goal: str,
    case_tag: str | None,
) -> tuple[list[str], str, str | None]:
    """Normalize extracted goal fields with shared contextual information."""
    normalized_param_types = [normalize_extracted_expr(param_type) for param_type in param_types]
    normalized_final_goal = normalize_extracted_expr(final_goal)
    normalized_case_tag = normalize_extracted_expr(case_tag) if case_tag else None

    normalized_param_types = [
        _annotate_list_shape_uses(_annotate_array_shape_uses(param_type))
        for param_type in normalized_param_types
    ]
    normalized_final_goal = _annotate_list_shape_uses(
        _annotate_array_shape_uses(normalized_final_goal),
    )
    if normalized_case_tag is not None:
        normalized_case_tag = _annotate_list_shape_uses(
            _annotate_array_shape_uses(normalized_case_tag),
        )

    return normalized_param_types, normalized_final_goal, normalized_case_tag
