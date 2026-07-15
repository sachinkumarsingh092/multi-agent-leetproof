"""Tests for replace_sorry_with_placeholder function."""

import pytest
from utils.lean.transform import (
    replace_first_sorry_with_multiline_tactic,
    replace_sorry_with_placeholder,
)
from utils.lean.constants import SUBGOAL_PLACEHOLDER


class TestReplaceSorryWithPlaceholder:
    """Tests for the replace_sorry_with_placeholder function."""

    def test_term_mode_sorry(self):
        """Test replacing term-mode sorry (:= sorry)."""
        input_text = "have h : T := sorry"
        expected = f"have h : T := by {SUBGOAL_PLACEHOLDER}"
        assert replace_sorry_with_placeholder(input_text) == expected

    def test_tactic_mode_sorry_same_line(self):
        """Test replacing tactic-mode sorry (by sorry) on same line."""
        input_text = "have h : T := by sorry"
        expected = f"have h : T := by {SUBGOAL_PLACEHOLDER}"
        assert replace_sorry_with_placeholder(input_text) == expected

    def test_tactic_mode_sorry_different_line(self):
        """Test replacing tactic-mode sorry with 'by' on different line."""
        input_text = "have h : T := by\n  sorry"
        expected = f"have h : T := by\n  {SUBGOAL_PLACEHOLDER}"
        assert replace_sorry_with_placeholder(input_text) == expected

    def test_tactic_mode_sorry_with_extra_indentation(self):
        """Test preserving indentation when sorry is on different line."""
        input_text = "have h : T := by\n    sorry"
        expected = f"have h : T := by\n    {SUBGOAL_PLACEHOLDER}"
        assert replace_sorry_with_placeholder(input_text) == expected

    def test_does_not_touch_valid_term_proof(self):
        """Test that valid term proofs are not modified."""
        input_text = "have h : T := rfl"
        assert replace_sorry_with_placeholder(input_text) == input_text

    def test_does_not_touch_valid_tactic_proof(self):
        """Test that valid tactic proofs are not modified."""
        input_text = "have h : T := by simp"
        assert replace_sorry_with_placeholder(input_text) == input_text

    def test_does_not_touch_sorry_in_identifier(self):
        """Test that sorry inside identifiers is not modified."""
        input_text = "let x := sorry_helper y"
        assert replace_sorry_with_placeholder(input_text) == input_text

    def test_does_not_touch_sorry_prefix(self):
        """Test that identifiers starting with sorry are not modified."""
        input_text = "have h : T := sorryAbc"
        assert replace_sorry_with_placeholder(input_text) == input_text

    def test_multiple_have_statements(self):
        """Test replacing multiple have statements with sorry."""
        input_text = """have h1 : T1 := sorry
have h2 : T2 := by sorry
have h3 : T3 := by
  sorry"""
        expected = f"""have h1 : T1 := by {SUBGOAL_PLACEHOLDER}
have h2 : T2 := by {SUBGOAL_PLACEHOLDER}
have h3 : T3 := by
  {SUBGOAL_PLACEHOLDER}"""
        assert replace_sorry_with_placeholder(input_text) == expected

    def test_mixed_sorry_and_valid_proofs(self):
        """Test that only sorry-based proofs are replaced."""
        input_text = """have h1 : T1 := sorry
have h2 : T2 := rfl
have h3 : T3 := by sorry
have h4 : T4 := by simp"""
        expected = f"""have h1 : T1 := by {SUBGOAL_PLACEHOLDER}
have h2 : T2 := rfl
have h3 : T3 := by {SUBGOAL_PLACEHOLDER}
have h4 : T4 := by simp"""
        assert replace_sorry_with_placeholder(input_text) == expected

    def test_real_sketch_example(self):
        """Test with a real sketch example from the codebase."""
        input_text = """theorem goal_0
    : T := by
    have h_n_pos : gas.length > 0 := sorry
    have h_cost_len : gas.length = cost.length := sorry
    cases h_step_cases with
    | inl h_zero => exact h_case_zero h_zero
    | inr h_pos => exact h_case_pos h_pos"""
        expected = f"""theorem goal_0
    : T := by
    have h_n_pos : gas.length > 0 := by {SUBGOAL_PLACEHOLDER}
    have h_cost_len : gas.length = cost.length := by {SUBGOAL_PLACEHOLDER}
    cases h_step_cases with
    | inl h_zero => exact h_case_zero h_zero
    | inr h_pos => exact h_case_pos h_pos"""
        assert replace_sorry_with_placeholder(input_text) == expected

    def test_custom_placeholder(self):
        """Test using a custom placeholder."""
        input_text = "have h : T := sorry"
        custom_placeholder = "custom_tactic"
        expected = f"have h : T := by {custom_placeholder}"
        assert replace_sorry_with_placeholder(input_text, custom_placeholder) == expected

    def test_top_level_sorry(self):
        """Test replacing sorry at the top level of a proof."""
        input_text = "theorem foo : T := by sorry"
        expected = f"theorem foo : T := by {SUBGOAL_PLACEHOLDER}"
        assert replace_sorry_with_placeholder(input_text) == expected

    def test_term_mode_sorry_with_whitespace(self):
        """Test term-mode sorry with whitespace before sorry (whitespace preserved)."""
        input_text = "have h : T :=   sorry"
        # Whitespace before sorry is preserved when inserting 'by '
        expected = f"have h : T :=   by {SUBGOAL_PLACEHOLDER}"
        assert replace_sorry_with_placeholder(input_text) == expected

    def test_by_on_separate_line_after_assignment(self):
        """Test case where 'by' is on a separate line after ':='."""
        input_text = "have h : T :=\nby\n  sorry"
        expected = f"have h : T :=\nby\n  {SUBGOAL_PLACEHOLDER}"
        assert replace_sorry_with_placeholder(input_text) == expected

    def test_by_on_separate_line_with_indentation(self):
        """Test case where 'by' is on a separate line with indentation."""
        input_text = "have h : T :=\n  by\n    sorry"
        expected = f"have h : T :=\n  by\n    {SUBGOAL_PLACEHOLDER}"
        assert replace_sorry_with_placeholder(input_text) == expected

    def test_by_and_sorry_both_on_separate_lines(self):
        """Test case with both 'by' and 'sorry' on their own lines."""
        input_text = """have h : T :=
    by
      sorry"""
        expected = f"""have h : T :=
    by
      {SUBGOAL_PLACEHOLDER}"""
        assert replace_sorry_with_placeholder(input_text) == expected

    def test_triple_sorry_typo_not_replaced(self):
        """Test that 'sorrry' (typo with triple r) is not replaced."""
        # This is a word boundary test - 'sorrry' should not match 'sorry'
        input_text = "have h : T := sorrry"
        # Since 'sorrry' is not 'sorry', it shouldn't be replaced as term-mode sorry
        # However, the regex will still try to match it since it starts with 'sorry'
        # Let's verify the actual behavior
        result = replace_sorry_with_placeholder(input_text)
        # The regex uses \b for word boundary, so 'sorrry' should not match 'sorry\b'
        assert result == input_text  # Should remain unchanged

    def test_all_cases_combined(self):
        """Test all four cases together in one text."""
        input_text = """-- Case 1: term-mode
have h1 : T1 := sorry
-- Case 2: by sorry same line
have h2 : T2 := by sorry
-- Case 3: by on same line, sorry on next
have h3 : T3 := by
  sorry
-- Case 4: by on separate line after :=
have h4 : T4 :=
by
  sorry
-- Valid proof (should not change)
have h5 : T5 := rfl"""
        expected = f"""-- Case 1: term-mode
have h1 : T1 := by {SUBGOAL_PLACEHOLDER}
-- Case 2: by sorry same line
have h2 : T2 := by {SUBGOAL_PLACEHOLDER}
-- Case 3: by on same line, sorry on next
have h3 : T3 := by
  {SUBGOAL_PLACEHOLDER}
-- Case 4: by on separate line after :=
have h4 : T4 :=
by
  {SUBGOAL_PLACEHOLDER}
-- Valid proof (should not change)
have h5 : T5 := rfl"""
        assert replace_sorry_with_placeholder(input_text) == expected

    def test_nested_have_with_sorry(self):
        """Test nested have statements with sorry."""
        input_text = """have .. :=
by
    have .. := by
        sorry
    sorry"""
        expected = f"""have .. :=
by
    have .. := by
        {SUBGOAL_PLACEHOLDER}
    {SUBGOAL_PLACEHOLDER}"""
        assert replace_sorry_with_placeholder(input_text) == expected

    def test_deeply_nested_by_blocks(self):
        """Test deeply nested by blocks with multiple sorries."""
        input_text = """have .. := by
    have .. := by
        sorry
    sorry"""
        expected = f"""have .. := by
    have .. := by
        {SUBGOAL_PLACEHOLDER}
    {SUBGOAL_PLACEHOLDER}"""
        assert replace_sorry_with_placeholder(input_text) == expected

    def test_by_on_separate_line_same_indent_as_sorry(self):
        """Test case: by and sorry at same indentation (valid tactic mode)."""
        # In Lean, same indentation is valid for tactic mode
        input_text = """have .. :=
by
sorry"""
        # sorry is at same indent as 'by', which is valid tactic mode
        expected = f"""have .. :=
by
{SUBGOAL_PLACEHOLDER}"""
        assert replace_sorry_with_placeholder(input_text) == expected

    def test_various_by_positions(self):
        """Test various positions of 'by' keyword."""
        input_text = """have h1 :=
by sorry
have h2 :=
    by sorry
have h3 :=
    by
    sorry"""
        expected = f"""have h1 :=
by {SUBGOAL_PLACEHOLDER}
have h2 :=
    by {SUBGOAL_PLACEHOLDER}
have h3 :=
    by
    {SUBGOAL_PLACEHOLDER}"""
        assert replace_sorry_with_placeholder(input_text) == expected

    def test_complex_nested_structure(self):
        """Test complex nested structure from user's examples."""
        input_text = """have .. :=
    by
    have .. :=
    by
        sorry
    sorry"""
        expected = f"""have .. :=
    by
    have .. :=
    by
        {SUBGOAL_PLACEHOLDER}
    {SUBGOAL_PLACEHOLDER}"""
        assert replace_sorry_with_placeholder(input_text) == expected

    def test_multiline_comments_ignored(self):
        """Test that sorry inside multi-line comments is ignored."""
        input_text = """def foo : T := sorry
/-
This is a comment with sorry in it
-/
def bar : T := by sorry"""
        expected = f"""def foo : T := by {SUBGOAL_PLACEHOLDER}
/-
This is a comment with sorry in it
-/
def bar : T := by {SUBGOAL_PLACEHOLDER}"""
        assert replace_sorry_with_placeholder(input_text) == expected

    def test_nested_multiline_comments_ignored(self):
        """Test that sorry inside nested multi-line comments is ignored."""
        input_text = """def foo : T := sorry
/-
Outer comment
/- Inner comment with sorry -/
End outer comment
-/
def bar : T := by sorry"""
        expected = f"""def foo : T := by {SUBGOAL_PLACEHOLDER}
/-
Outer comment
/- Inner comment with sorry -/
End outer comment
-/
def bar : T := by {SUBGOAL_PLACEHOLDER}"""
        assert replace_sorry_with_placeholder(input_text) == expected

    def test_inline_block_comment(self):
        """Test block comments used inline."""
        input_text = "def foo : T := /- sorry -/ sorry"
        expected = f"def foo : T := /- sorry -/ by {SUBGOAL_PLACEHOLDER}"
        assert replace_sorry_with_placeholder(input_text) == expected


class TestReplaceFirstSorryWithMultilineTactic:
    """Tests for indentation-safe first-sorry replacement used in prover assembly."""

    def test_real_failure_shape_keeps_block_indent(self):
        input_text = """theorem uniqueness_0 := by
    intro a b ha hb
    by_contra hne
    have hsum_gt : lst.count a + lst.count b > lst.length := by
      expose_names; sorry
    have hsum_le : lst.count a + lst.count b ≤ lst.length := by
      expose_names; exact (uniqueness_0_0 ...)
"""
        tactic = "simp_all [IsMajority, HasMajority, precondition, postcondition]\ngrind"

        got = replace_first_sorry_with_multiline_tactic(input_text, tactic)

        assert "      expose_names; simp_all [IsMajority, HasMajority, precondition, postcondition]" in got
        assert "\n      grind\n" in got
        assert "\n    have hsum_le" in got

    def test_replaces_only_first_sorry_per_call(self):
        input_text = """by
  have h1 : True := by
    sorry
  have h2 : True := by
    sorry
"""
        got = replace_first_sorry_with_multiline_tactic(input_text, "trivial")
        assert got.count("sorry") == 1

    def test_supports_single_line_exact_goal_replacement(self):
        input_text = """by
  have h : True := by
    sorry
"""
        got = replace_first_sorry_with_multiline_tactic(input_text, "exact (uniqueness_0_0 lst a b)")
        assert "    exact (uniqueness_0_0 lst a b)" in got

    def test_supports_recovered_tactic_list_input(self):
        input_text = """by
  have h : True := by
    sorry
"""
        got = replace_first_sorry_with_multiline_tactic(input_text, ["simp", "grind"])
        assert "\n    simp\n" in got
        assert "\n    grind\n" in got

