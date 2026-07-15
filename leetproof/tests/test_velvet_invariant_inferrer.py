from agents.velvet_invariant_inferrer import (
    _extract_annotation_lines,
    validate_inferrer_output,
)


def _build_program(impl_body: str) -> str:
    return f"""section Specs
def precondition (n : Nat) := True
def postcondition (n : Nat) (result : Nat) := True
end Specs

section Impl
method CountUp (n : Nat)
  return (result : Nat)
  require precondition n
  ensures postcondition n result
  do
{impl_body}

prove_correct CountUp by
  sorry
end Impl

section TestCases
-- none
end TestCases

section Assertions
-- none
end Assertions

section Pbt
-- none
end Pbt
"""


def test_validate_inferrer_output_rejects_comment_only_annotation_retry():
    baseline = _build_program(
        """    let mut i := 0
    while i < n
        invariant i <= n
    do
        i := i + 1
    return i"""
    )
    new_content = _build_program(
        """    let mut i := 0
    while i < n
        -- checking loop bound
        invariant i <= n
    do
        i := i + 1
    return i"""
    )
    previous_impl = """method CountUp (n : Nat)
  return (result : Nat)
  require precondition n
  ensures postcondition n result
  do
    let mut i := 0
    while i < n
        invariant i <= n
    do
        i := i + 1
    return i

prove_correct CountUp by
  sorry"""

    result = validate_inferrer_output(
        baseline,
        new_content,
        previous_impl=previous_impl,
    )

    assert result.has_error()
    assert "only comment/whitespace changes" in result.get_error()


def test_extract_annotation_lines_skips_full_line_comments():
    body = """let mut i := 0
while i < n
    -- checking loop bound
    invariant i <= n
    -- another comment
    done_with i = n
do
    i := i + 1
return i"""

    assert _extract_annotation_lines(body) == [
        ("invariant i <= n", "done_with i = n")
    ]


def test_validate_inferrer_output_accepts_real_annotation_change_after_comment():
    baseline = _build_program(
        """    let mut i := 0
    while i < n
        invariant i <= n
    do
        i := i + 1
    return i"""
    )
    new_content = _build_program(
        """    let mut i := 0
    while i < n
        -- strengthened bound
        invariant i <= n + 1
    do
        i := i + 1
    return i"""
    )
    previous_impl = """method CountUp (n : Nat)
  return (result : Nat)
  require precondition n
  ensures postcondition n result
  do
    let mut i := 0
    while i < n
        invariant i <= n
    do
        i := i + 1
    return i

prove_correct CountUp by
  sorry"""

    result = validate_inferrer_output(
        baseline,
        new_content,
        previous_impl=previous_impl,
    )

    assert not result.has_error()
