"""Tests for Lean goal parsing and manipulation functions."""

import pytest
from utils.lean.goals import (
    parse_lean_goals, find_lines_matching, replace_on_lines,
    find_sorry_lines, replace_sorries_by_line,
    extract_try_this_suggestion, apply_try_this_suggestion, refine_suggestions,
)
from utils.lean.normalization import normalize_extracted_goal_fields
from utils.lean.types import LakeBuildResult, LeanDiagnostic


class TestLineMatchingHelpers:
    """Tests for generic line matching helpers."""

    def test_find_lines_matching_with_pattern(self):
        """Test finding lines with regex pattern."""
        code = """line one
MATCH here
line three
another MATCH
end"""

        lines = find_lines_matching(code, r'MATCH')
        assert lines == [2, 4]

    def test_find_lines_matching_with_callable(self):
        """Test finding lines with callable predicate."""
        code = """short
this is a longer line
x
another long line here"""

        # Find lines with more than 10 characters
        lines = find_lines_matching(code, lambda line: len(line) > 10)
        assert lines == [2, 4]

    def test_replace_on_lines(self):
        """Test generic replace_on_lines."""
        code = """foo bar
foo bar
foo bar"""

        replacement_map = {1: "X", 3: "Y"}
        result = replace_on_lines(code, replacement_map, r'foo')

        lines = result.splitlines()
        assert lines[0] == "X bar"
        assert lines[1] == "foo bar"  # Line 2 not in map
        assert lines[2] == "Y bar"


class TestSorryLineHelpers:
    """Tests for find_sorry_lines and replace_sorries_by_line."""

    def test_find_sorry_lines_basic(self):
        """Test finding sorry lines in code."""
        code = """theorem foo : True := by
  have h1 : 1 = 1 := by sorry
  have h2 : 2 = 2 := by rfl
  have h3 : 3 = 3 := by sorry
  sorry"""

        lines = find_sorry_lines(code)
        assert lines == [2, 4, 5]

    def test_find_sorry_lines_no_sorry(self):
        """Test with no sorries."""
        code = """theorem foo : True := by
  rfl"""

        lines = find_sorry_lines(code)
        assert lines == []

    def test_find_sorry_lines_word_boundary(self):
        """Test that 'sorry' only matches as a word."""
        code = """-- not_sorry is different
sorry_helper is different
actual sorry here"""

        lines = find_sorry_lines(code)
        assert lines == [3]  # Only the actual 'sorry' on line 3

    def test_replace_sorries_by_line_basic(self):
        """Test replacing sorries by line number."""
        code = """line1 sorry
line2 sorry
line3 sorry"""

        replacement_map = {
            1: "REPLACED_1",
            3: "REPLACED_3",
        }

        result = replace_sorries_by_line(code, replacement_map)
        lines = result.splitlines()
        assert lines[0] == "line1 REPLACED_1"
        assert lines[1] == "line2 sorry"  # Not in map, unchanged
        assert lines[2] == "line3 REPLACED_3"

    def test_replace_sorries_by_line_empty_map(self):
        """Test with empty replacement map - should not change anything."""
        code = """sorry
sorry"""

        result = replace_sorries_by_line(code, {})
        assert result == code

    def test_replace_sorries_preserves_structure(self):
        """Test that replacement preserves code structure."""
        code = """theorem foo : True := by
  have h1 : 1 = 1 := by sorry
  have h2 : 2 = 2 := by sorry
  exact h1"""

        replacement_map = {
            2: "exact rfl",
            3: "exact (my_lemma x y)",
        }

        result = replace_sorries_by_line(code, replacement_map)
        assert "have h1 : 1 = 1 := by exact rfl" in result
        assert "have h2 : 2 = 2 := by exact (my_lemma x y)" in result
        assert "exact h1" in result  # Untouched


class TestParseLeanGoals:
    """Tests for parse_lean_goals function."""

    def test_single_line_params(self):
        """Test parsing single-line parameters."""
        content = """h_a : a = 5
h_b : b = 10
⊢ a + b = 15"""
        goals = parse_lean_goals(content)

        assert len(goals) == 1
        assert goals[0].final_goal == "a + b = 15"
        assert len(goals[0].params) == 2
        assert goals[0].params[0].name == "h_a"
        assert goals[0].params[0].ty == "a = 5"
        assert goals[0].params[1].name == "h_b"
        assert goals[0].params[1].ty == "b = 10"

    def test_multiline_param(self):
        """Test parsing multi-line parameter (type spans multiple lines)."""
        content = """h_simple : x = 1
h_complex :
  (a < b ∧ a < c) ∧
    (b < c)
h_other : y = 2
⊢ some_goal"""
        goals = parse_lean_goals(content)

        assert len(goals) == 1
        assert len(goals[0].params) == 3
        assert goals[0].params[0].name == "h_simple"
        assert goals[0].params[0].ty == "x = 1"
        assert goals[0].params[1].name == "h_complex"
        assert goals[0].params[1].ty == "(a < b ∧ a < c) ∧ (b < c)"
        assert goals[0].params[2].name == "h_other"
        assert goals[0].params[2].ty == "y = 2"

    def test_multiline_param_at_end(self):
        """Test multi-line param right before turnstile."""
        content = """h_pairwise :
  (test1_a[1]! < test1_a[4]!) ∧
    (test1_a[4]! < test1_a[5]!)
⊢ ∀ (idxs : List ℕ), isIncSubseq test1_a idxs → idxs.length ≤ 4"""
        goals = parse_lean_goals(content)

        assert len(goals) == 1
        assert len(goals[0].params) == 1
        assert goals[0].params[0].name == "h_pairwise"
        assert "(test1_a[1]! < test1_a[4]!)" in goals[0].params[0].ty
        assert "(test1_a[4]! < test1_a[5]!)" in goals[0].params[0].ty

    @pytest.mark.parametrize(
        ("original", "expected"),
        [
            ("grid[r]![c]!", "(grid[r]!)[c]!"),
            ("a[x]![y]![z]!", "((a[x]!)[y]!)[z]!"),
            ("a[b[i]]![c[j]]!", "(a[b[i]]!)[c[j]]!"),
            ("(f xs)[i]![j]!", "((f xs)[i]!)[j]!"),
            ("arr[i]!", "arr[i]!"),
            ("text[i]?.getD 'A'", "text[i]?.getD 'A'"),
            ("(grid[r]!)[c]!", "(grid[r]!)[c]!"),
            ("(foo (bar x))[i + 1]![j - 1]!", "((foo (bar x))[i + 1]!)[j - 1]!"),
        ],
    )
    def test_nested_getelem_syntax_is_repaired_in_params(self, original, expected):
        """Nested `[]!` chains in param types should be normalized."""
        content = f"""h_bad : {original}
⊢ True"""
        goals = parse_lean_goals(content)

        assert len(goals) == 1
        assert goals[0].params[0].ty == expected

    @pytest.mark.parametrize(
        ("original", "expected"),
        [
            (
                "∀ r < i, ∀ c < j, (0 : Nat.zero) ≤ grid[r]![c]!",
                "∀ r < i, ∀ c < j, (0 : Nat.zero) ≤ (grid[r]!)[c]!",
            ),
            (
                "(count = 0) ∧ arr[i]![j]! < 0",
                "(count = 0) ∧ (arr[i]!)[j]! < 0",
            ),
        ],
    )
    def test_nested_getelem_syntax_is_repaired_in_goals(self, original, expected):
        """Nested `[]!` chains in goal targets should be normalized."""
        content = f"""h : True
⊢ {original}"""
        goals = parse_lean_goals(content)

        assert len(goals) == 1
        assert goals[0].final_goal == expected

    def test_nested_getelem_syntax_is_repaired_in_case_tags(self):
        """Case tags carrying extracted expressions should be normalized too."""
        content = """case «invariant_left: ∀ r < i, ∀ c < j, (0 : Nat.zero) ≤ grid[r]![c]!»
h : True
⊢ True"""
        goals = parse_lean_goals(content)

        assert len(goals) == 1
        assert goals[0].case_tag == "«invariant_left: ∀ r < i, ∀ c < j, (0 : Nat.zero) ≤ (grid[r]!)[c]!»"

    def test_empty_array_size_is_annotated_from_context(self):
        """Bare empty arrays in `.size` contexts should be minimally annotated."""
        content = """nums : Array ℤ
require_1 : True
if_neg : OfNat.ofNat 1 < nums.size
⊢ ∀ t < #[].size, #[][t]! < nums.size"""
        goals = parse_lean_goals(content)

        assert len(goals) == 1
        assert goals[0].final_goal == "∀ t < (#[] : Array Int).size, #[][t]! < nums.size"

    def test_empty_array_equality_is_left_unchanged(self):
        """Bare empty arrays outside `.size` should stay unchanged."""
        content = """nums : Array ℤ
⊢ #[] = nums.extract 0 0"""
        goals = parse_lean_goals(content)

        assert len(goals) == 1
        assert goals[0].final_goal == "#[] = nums.extract 0 0"

    def test_empty_list_length_is_annotated_from_context(self):
        """Bare empty lists in `.length` contexts should be minimally annotated."""
        content = """xs : List ℕ
⊢ [].length = 0"""
        goals = parse_lean_goals(content)

        assert len(goals) == 1
        assert goals[0].final_goal == "([] : List Nat).length = 0"

    def test_empty_container_annotation_skips_ambiguous_contexts(self):
        """Ambiguous element-type contexts should not be guessed."""
        param_types, final_goal, case_tag = normalize_extracted_goal_fields(
            ["xs : Array Nat", "ys : Array Int"],
            "#[].size = 0",
            None,
        )

        assert param_types == ["xs : Array Nat", "ys : Array Int"]
        assert final_goal == "#[].size = 0"
        assert case_tag is None

    def test_empty_array_equality_normalization_skips_constrained_context(self):
        """Equality with a typed local should not be rewritten."""
        param_types, final_goal, case_tag = normalize_extracted_goal_fields(
            ["stack = #[]", "stack : Array Nat"],
            "True",
            None,
        )

        assert param_types == ["stack = #[]", "stack : Array Nat"]
        assert final_goal == "True"
        assert case_tag is None

    def test_case_tag_does_not_drive_empty_container_annotation(self):
        """Case tags should not be used to infer empty-container element types."""
        param_types, final_goal, case_tag = normalize_extracted_goal_fields(
            [],
            "#[].size = 0",
            "«invariant_inv_build_stack_size_le_n: ((@Array.size Nat stack) ≤ n)»",
        )

        assert param_types == []
        assert final_goal == "#[].size = 0"
        assert case_tag == "«invariant_inv_build_stack_size_le_n: ((@Array.size Nat stack) ≤ n)»"

    def test_multiple_names_same_type(self):
        """Test multiple param names with same type."""
        content = """h1 h2 h3 : True
⊢ goal"""
        goals = parse_lean_goals(content)

        assert len(goals) == 1
        assert len(goals[0].params) == 3
        assert goals[0].params[0].name == "h1"
        assert goals[0].params[1].name == "h2"
        assert goals[0].params[2].name == "h3"
        for p in goals[0].params:
            assert p.ty == "True"

    def test_multiline_param_multiple_names(self):
        """Test multi-line param with multiple names sharing type on next line."""
        content = """h_simple : x = 1
h_a h_b h_c h_d :
  True
h_other : y = 2
⊢ some_goal"""
        goals = parse_lean_goals(content)

        assert len(goals) == 1
        assert goals[0].final_goal == "some_goal"
        assert len(goals[0].params) == 6

        assert goals[0].params[0].name == "h_simple"
        assert goals[0].params[0].ty == "x = 1"

        # h_a, h_b, h_c, h_d all have type True
        assert goals[0].params[1].name == "h_a"
        assert goals[0].params[1].ty == "True"
        assert goals[0].params[2].name == "h_b"
        assert goals[0].params[2].ty == "True"
        assert goals[0].params[3].name == "h_c"
        assert goals[0].params[3].ty == "True"
        assert goals[0].params[4].name == "h_d"
        assert goals[0].params[4].ty == "True"

        assert goals[0].params[5].name == "h_other"
        assert goals[0].params[5].ty == "y = 2"

    def test_multiline_param_with_forall_type(self):
        """Test multi-line param where type is a forall expression with continuations.
        
        This is a regression test for the issue where params ending with symbols like
        ',' or '→' would cause parsing errors because the parser didn't recognize
        that the type spans multiple indented lines.
        """
        content = """unsolved goals
h_indices_valid : isValidIncreasingSubseq #[5, 2, 8, 6, 3, 6, 9, 7] [1, 4, 5, 6]
h_tonat_four h_witness_indices : True
h_indices_ordered : ∀ (i j : ℕ),
  i < j →
    j < 4 →
      [1, 4, 5, 6][i]?.getD 0 < [1, 4, 5, 6][j]?.getD 0
h_indices_inbounds : ∀ i < 4, [1, 4, 5, 6][i]?.getD 0 < 8
⊢ ∀ (i j : ℕ), i < j → j < 4 → result"""
        
        goals = parse_lean_goals(content)
        
        assert len(goals) == 1
        assert len(goals[0].params) == 5
        
        # Check the parameter with forall type
        h_indices_ordered = goals[0].params[3]
        assert h_indices_ordered.name == "h_indices_ordered"
        assert "∀ (i j : ℕ)," in h_indices_ordered.ty
        assert "i < j →" in h_indices_ordered.ty
        assert "j < 4 →" in h_indices_ordered.ty
        
        # Check the final goal
        assert goals[0].final_goal == "∀ (i j : ℕ), i < j → j < 4 → result"

    def test_multiline_type_with_colon_inside(self):
        """Test multiline param where continuation lines contain colons.

        This is the key test - continuation lines like "∀ (subseq : List ℤ)"
        should NOT be treated as new params because they're indented.
        """
        content = """h_maximality :
  ∀ (subseq : List ℤ), isSubsequenceOf subseq test3_a.toList → isStrictlyIncreasing subseq → subseq.length ≤ 6
h_nonneg : 0 ≤ test3_Expected
⊢ isLISLength test3_a test3_Expected.toNat"""

        goals = parse_lean_goals(content)

        assert len(goals) == 1
        assert len(goals[0].params) == 2

        # h_maximality should have the full multiline type
        assert goals[0].params[0].name == "h_maximality"
        assert goals[0].params[0].ty == "∀ (subseq : List ℤ), isSubsequenceOf subseq test3_a.toList → isStrictlyIncreasing subseq → subseq.length ≤ 6"

        assert goals[0].params[1].name == "h_nonneg"
        assert goals[0].params[1].ty == "0 ≤ test3_Expected"

        assert goals[0].final_goal == "isLISLength test3_a test3_Expected.toNat"

    def test_full_lis_example(self):
        """Test the full LIS example that was failing.

        This is a regression test for the exact input that exposed the bug.
        """
        content = """unsolved goals
h_expected_val : test3_Expected = 6
h_toNat : test3_Expected.toNat = 6
h_witness_subseq : isSubsequenceOf [-2, -1, 3, 6, 9, 10] test3_a.toList
h_witness_increasing : isStrictlyIncreasing [-2, -1, 3, 6, 9, 10]
h_existence : ∃ subseq, isSubsequenceOf subseq test3_a.toList ∧ isStrictlyIncreasing subseq ∧ subseq.length = 6
h_maximality :
  ∀ (subseq : List ℤ), isSubsequenceOf subseq test3_a.toList → isStrictlyIncreasing subseq → subseq.length ≤ 6
h_nonneg : 0 ≤ test3_Expected
h_witness_def : True
⊢ isLISLength test3_a test3_Expected.toNat"""

        goals = parse_lean_goals(content)

        assert len(goals) == 1
        assert len(goals[0].params) == 8

        # Check all params by name
        param_names = [p.name for p in goals[0].params]
        assert param_names == [
            "h_expected_val",
            "h_toNat",
            "h_witness_subseq",
            "h_witness_increasing",
            "h_existence",
            "h_maximality",
            "h_nonneg",
            "h_witness_def",
        ]

        # Check the multiline param specifically
        h_maximality = goals[0].params[5]
        assert h_maximality.ty == "∀ (subseq : List ℤ), isSubsequenceOf subseq test3_a.toList → isStrictlyIncreasing subseq → subseq.length ≤ 6"

        # Check final goal
        assert goals[0].final_goal == "isLISLength test3_a test3_Expected.toNat"

    def test_multiple_indented_continuation_lines(self):
        """Test param with type spanning many indented lines."""
        content = """h_complex :
  first_line ∧
    second_line ∧
      third_line
⊢ goal"""

        goals = parse_lean_goals(content)

        assert len(goals) == 1
        assert len(goals[0].params) == 1
        assert goals[0].params[0].name == "h_complex"
        assert goals[0].params[0].ty == "first_line ∧ second_line ∧ third_line"

    def test_unindented_line_starts_new_param(self):
        """Test that an unindented line after multiline param starts new param."""
        content = """h_first :
  some_type
h_second : another_type
⊢ goal"""

        goals = parse_lean_goals(content)

        assert len(goals) == 1
        assert len(goals[0].params) == 2
        assert goals[0].params[0].name == "h_first"
        assert goals[0].params[0].ty == "some_type"
        assert goals[0].params[1].name == "h_second"
        assert goals[0].params[1].ty == "another_type"

    def test_multiline_goal(self):
        """Test goal that spans multiple indented lines."""
        content = """h : True
⊢ ∀ (x : Nat),
    x > 0 →
      result"""

        goals = parse_lean_goals(content)

        assert len(goals) == 1
        assert goals[0].final_goal == "∀ (x : Nat), x > 0 → result"

    def test_ignores_unsolved_goals_prefix(self):
        """Test that 'unsolved goals' prefix line is ignored."""
        content = """unsolved goals
h : True
⊢ goal"""

        goals = parse_lean_goals(content)

        assert len(goals) == 1
        assert len(goals[0].params) == 1
        assert goals[0].params[0].name == "h"
        assert goals[0].final_goal == "goal"

    def test_multiline_goal_with_colon_inside(self):
        """Test goal with continuation lines containing colons.

        Goal continuation lines containing ':' should not be mistaken for params.
        """
        content = """h : True
⊢ ∀ (x : Nat) (y : Nat),
    x + y = y + x"""

        goals = parse_lean_goals(content)

        assert len(goals) == 1
        assert goals[0].final_goal == "∀ (x : Nat) (y : Nat), x + y = y + x"

    def test_multiple_goals(self):
        """Test parsing multiple goals (multiple turnstiles)."""
        content = """case left
h : True
⊢ first_goal

case right
h2 : False
⊢ second_goal"""

        goals = parse_lean_goals(content)

        assert len(goals) == 2
        assert goals[0].final_goal == "first_goal"
        assert goals[0].case_tag == "left"
        assert goals[1].final_goal == "second_goal"
        assert goals[1].case_tag == "right"

    def test_case_tag_with_special_chars(self):
        """Test parsing case tags with special characters like guillemets."""
        content = """case «ensures_1: postcondition a b result»
a b : Array ℤ
require_1 : precondition a b
if_pos : a = #[]
⊢ postcondition a b 0"""

        goals = parse_lean_goals(content)

        assert len(goals) == 1
        assert goals[0].case_tag == "«ensures_1: postcondition a b result»"
        assert goals[0].final_goal == "postcondition a b 0"
        assert len(goals[0].params) == 4

    def test_multiple_goals_with_complex_case_tags(self):
        """Test parsing multiple goals with complex case tags from actual error output."""
        content = """case «ensures_1: postcondition a b result»
a b : Array ℤ
require_1 : precondition a b
if_pos : a = #[]
⊢ postcondition a b 0

case «ensures_1: postcondition a b result»
a b : Array ℤ
require_1 : precondition a b
if_neg : ¬a = #[]
if_pos : b = #[]
⊢ postcondition a b 0

case «invariant_9: ∀ k, k < dp.size → dp[k]! ≤ m ∧ dp[k]! ≤ n»
a b : Array ℤ
require_1 : precondition a b
dp : Array ℕ
⊢ ∀ k < dp_1.size, (dp_1.setIfInBounds idx val)[k]! ≤ a.size"""

        goals = parse_lean_goals(content)

        assert len(goals) == 3
        assert goals[0].case_tag == "«ensures_1: postcondition a b result»"
        assert goals[1].case_tag == "«ensures_1: postcondition a b result»"
        assert goals[2].case_tag == "«invariant_9: ∀ k, k < dp.size → dp[k]! ≤ m ∧ dp[k]! ≤ n»"

    def test_goal_without_case_tag(self):
        """Test that goals without case tags have None as case_tag."""
        content = """h : True
⊢ some_goal"""

        goals = parse_lean_goals(content)

        assert len(goals) == 1
        assert goals[0].case_tag is None
        assert goals[0].final_goal == "some_goal"

    def test_mixed_goals_with_and_without_case_tags(self):
        """Test parsing goals where some have case tags and some don't."""
        content = """⊢ first_goal_no_case

case tagged
h : True
⊢ second_goal_with_case

h2 : False
⊢ third_goal_no_case"""

        goals = parse_lean_goals(content)

        assert len(goals) == 3
        assert goals[0].case_tag is None
        assert goals[0].final_goal == "first_goal_no_case"
        assert goals[1].case_tag == "tagged"
        assert goals[1].final_goal == "second_goal_with_case"
        assert goals[2].case_tag is None
        assert goals[2].final_goal == "third_goal_no_case"

    def test_goal_with_no_params(self):
        """Test goal with empty context (no params)."""
        content = """⊢ 1 + 1 = 2"""

        goals = parse_lean_goals(content)

        assert len(goals) == 1
        assert len(goals[0].params) == 0
        assert goals[0].final_goal == "1 + 1 = 2"

    def test_multiline_goal_with_no_params(self):
        """Test multiline goal with empty context."""
        content = """⊢ ∀ (x : Nat),
    x = x"""

        goals = parse_lean_goals(content)

        assert len(goals) == 1
        assert len(goals[0].params) == 0
        assert goals[0].final_goal == "∀ (x : Nat), x = x"

    def test_multiple_goals_first_no_params(self):
        """Test multiple goals where first has no params."""
        content = """⊢ first_goal
h : True
⊢ second_goal"""

        goals = parse_lean_goals(content)

        assert len(goals) == 2
        assert len(goals[0].params) == 0
        assert goals[0].final_goal == "first_goal"
        assert len(goals[1].params) == 1
        assert goals[1].final_goal == "second_goal"


class TestExtractTryThisSuggestion:
    """Tests for extract_try_this_suggestion function."""

    def test_simple_inline_suggestion(self):
        message = "Try this: exact if_pos"
        result = extract_try_this_suggestion(message)
        assert result == "exact if_pos"

    def test_simple_trivial(self):
        message = "Try this: trivial"
        result = extract_try_this_suggestion(message)
        assert result == "trivial"

    def test_suggestion_with_extra_whitespace(self):
        message = "Try this:   simp only [Nat.add_comm]  "
        result = extract_try_this_suggestion(message)
        assert result == "simp only [Nat.add_comm]"

    def test_no_suggestion_returns_none(self):
        message = """Some proof state
⊢ n = n"""
        result = extract_try_this_suggestion(message)
        assert result is None

    def test_try_this_not_at_start_returns_none(self):
        message = """if_pos: ∀ {a : Prop}
Try this: exact if_pos"""
        result = extract_try_this_suggestion(message)
        assert result is None

    def test_multiline_suggestion_keeps_all_content(self):
        message = "Try this: subst if_pos\n    rfl"
        result = extract_try_this_suggestion(message)
        assert result == "subst if_pos\n    rfl"

    def test_empty_after_try_this(self):
        message = "Try this:"
        result = extract_try_this_suggestion(message)
        assert result == ""


class TestApplyTryThisSuggestion:
    """Tests for apply_try_this_suggestion function."""

    def test_replace_exact_question(self):
        code = "theorem foo : True := by\n    exact?"
        result = apply_try_this_suggestion(code, diag_line=2, diag_column=4, suggestion="trivial")
        assert result == "theorem foo : True := by\n    trivial"

    def test_replace_aesop_question(self):
        code = "theorem foo : True := by\n    aesop?"
        result = apply_try_this_suggestion(code, diag_line=2, diag_column=4, suggestion="simp_all")
        assert result == "theorem foo : True := by\n    simp_all"

    def test_replace_simp_question(self):
        code = "theorem foo : n = n := by\n    simp?"
        result = apply_try_this_suggestion(code, diag_line=2, diag_column=4, suggestion="simp only [eq_self_iff_true]")
        assert result == "theorem foo : n = n := by\n    simp only [eq_self_iff_true]"

    def test_replace_with_trailing_content(self):
        code = "theorem foo : True := by\n    aesop?;done"
        result = apply_try_this_suggestion(code, diag_line=2, diag_column=4, suggestion="trivial")
        assert result == "theorem foo : True := by\n    trivial;done"

    def test_out_of_bounds_line_returns_none(self):
        code = "theorem foo : True := by\n    exact?"
        result = apply_try_this_suggestion(code, diag_line=5, diag_column=4, suggestion="trivial")
        assert result is None

    def test_replace_grind_question(self):
        code = "theorem foo : True := by\n    grind?"
        result = apply_try_this_suggestion(code, diag_line=2, diag_column=4, suggestion="omega")
        assert result == "theorem foo : True := by\n    omega"

    def test_multiline_code_targets_correct_line(self):
        code = "line1\n    exact?\n    aesop?\nline4"
        result = apply_try_this_suggestion(code, diag_line=3, diag_column=4, suggestion="simp")
        assert result == "line1\n    exact?\n    simp\nline4"


class TestRefineSuggestions:
    """Tests for refine_suggestions async function."""

    @pytest.mark.asyncio
    async def test_single_suggestion_applied(self):
        code = "theorem foo : True := by\n    exact?"
        diagnostics = [
            LeanDiagnostic(severity="info", message="Try this: trivial", line=2, column=4),
        ]

        async def mock_check_build(c):
            return LakeBuildResult(typechecks=True, diagnostics=[])

        refined, build = await refine_suggestions(code, diagnostics, mock_check_build)
        assert "trivial" in refined
        assert "exact?" not in refined
        assert build is not None
        assert build.typechecks

    @pytest.mark.asyncio
    async def test_suggestion_that_fails_typecheck_is_skipped(self):
        code = "theorem foo : True := by\n    exact?"
        diagnostics = [
            LeanDiagnostic(severity="info", message="Try this: bad_tactic", line=2, column=4),
        ]

        async def mock_check_build(c):
            return LakeBuildResult(typechecks=False, diagnostics=[])

        refined, build = await refine_suggestions(code, diagnostics, mock_check_build)
        assert refined == code
        assert build is None

    @pytest.mark.asyncio
    async def test_multiple_suggestions_applied_incrementally(self):
        code = "theorem foo := by\n    simp?\n    aesop?"
        diagnostics = [
            LeanDiagnostic(severity="info", message="Try this: simp only [Nat.add_comm]", line=2, column=4),
            LeanDiagnostic(severity="info", message="Try this: trivial", line=3, column=4),
        ]

        async def mock_check_build(c):
            return LakeBuildResult(typechecks=True, diagnostics=[])

        refined, build = await refine_suggestions(code, diagnostics, mock_check_build)
        assert "simp only [Nat.add_comm]" in refined
        assert "trivial" in refined
        assert "simp?" not in refined
        assert "aesop?" not in refined

    @pytest.mark.asyncio
    async def test_no_suggestions_returns_original(self):
        code = "theorem foo : True := by\n    trivial"
        diagnostics = [
            LeanDiagnostic(severity="error", message="some error", line=2, column=4),
        ]

        async def mock_check_build(c):
            return LakeBuildResult(typechecks=True, diagnostics=[])

        refined, build = await refine_suggestions(code, diagnostics, mock_check_build)
        assert refined == code
        assert build is None

    @pytest.mark.asyncio
    async def test_partial_success_keeps_good_suggestions(self):
        code = "theorem foo := by\n    simp?\n    aesop?"
        diagnostics = [
            LeanDiagnostic(severity="info", message="Try this: simp only [Nat.add_comm]", line=2, column=4),
            LeanDiagnostic(severity="info", message="Try this: bad_tactic", line=3, column=4),
        ]

        call_count = 0
        async def mock_check_build(c):
            nonlocal call_count
            call_count += 1
            if call_count == 1:
                return LakeBuildResult(typechecks=True, diagnostics=[])
            return LakeBuildResult(typechecks=False, diagnostics=[])

        refined, build = await refine_suggestions(code, diagnostics, mock_check_build)
        assert "simp only [Nat.add_comm]" in refined
        assert "aesop?" in refined
