"""Tests for Lean proof-related helper functions."""

import pytest
from utils.lean_helpers import extract_and_move_proof_blocks, add_grind_attributes, parse_theorem


class TestExtractAndMoveProofBlocks:
    """Tests for extract_and_move_proof_blocks function."""

    def test_extract_multiline_proof_block(self):
        """Test extracting multi-line prove_correct + loom_solve block."""
        content = """some code
--prove_correct FindMissingNumber by
--  loom_solve
more code"""

        result, blocks = extract_and_move_proof_blocks(content)
        assert len(blocks) == 1
        assert "prove_correct FindMissingNumber by" in blocks[0]
        assert "loom_solve" in blocks[0]
        assert "prove_correct" not in result
        assert "loom_solve" not in result
        assert "some code" in result
        assert "more code" in result

    def test_extract_multiline_with_spaces(self):
        """Test extracting multi-line block with varying whitespace."""
        content = """  -- prove_correct Foo by
   --   loom_solve
other"""

        result, blocks = extract_and_move_proof_blocks(content)
        assert len(blocks) == 1
        assert "prove_correct Foo by" in blocks[0]
        assert "loom_solve" in blocks[0]

    def test_extract_single_line_proof_block(self):
        """Test extracting single-line prove_correct with loom_solve."""
        content = """some code
-- prove_correct Foo by loom_solve
more code"""

        result, blocks = extract_and_move_proof_blocks(content)
        assert len(blocks) == 1
        assert "prove_correct Foo by loom_solve" in blocks[0]
        assert "prove_correct" not in result
        assert "some code" in result
        assert "more code" in result

    def test_extract_multiple_proof_blocks(self):
        """Test extracting multiple proof blocks."""
        content = """code1
--prove_correct Foo by
--  loom_solve
code2
--prove_correct Bar by
--  loom_solve
code3"""

        result, blocks = extract_and_move_proof_blocks(content)
        assert len(blocks) == 2
        assert "prove_correct Foo by" in blocks[0]
        assert "prove_correct Bar by" in blocks[1]
        assert "prove_correct" not in result
        assert "code1" in result
        assert "code2" in result
        assert "code3" in result

    def test_preserve_prove_correct_without_loom_solve(self):
        """Test that prove_correct without loom_solve is still extracted."""
        content = """some code
--prove_correct Foo by
--  auto
more code"""

        result, blocks = extract_and_move_proof_blocks(content)
        assert len(blocks) == 1
        assert "prove_correct Foo by" in blocks[0]
        assert "auto" in blocks[0]

    def test_no_blocks_to_extract(self):
        """Test when there are no proof blocks."""
        content = """some code
more code"""

        result, blocks = extract_and_move_proof_blocks(content)
        assert len(blocks) == 0
        assert result == content

    def test_uncommented_blocks_not_extracted(self):
        """Test that uncommented prove_correct blocks are not extracted."""
        content = """some code
prove_correct Foo by
  loom_solve
more code"""

        result, blocks = extract_and_move_proof_blocks(content)
        assert len(blocks) == 0
        assert "prove_correct Foo by" in result  # Should remain in content


class TestAddGrindAttributes:
    """Tests for add_grind_attributes function."""

    def test_add_attributes_for_lemmas(self):
        """Test adding grind attributes for lemmas."""
        content = "existing code\n"
        lemma_names = ["lemma1", "lemma2"]

        result = add_grind_attributes(content, lemma_names)
        assert "attribute [solverHint] lemma1 lemma2" in result
        assert "attribute [grind] lemma1 lemma2" in result

    def test_add_attributes_empty_list(self):
        """Test with empty lemma list."""
        content = "existing code"
        result = add_grind_attributes(content, [])
        assert result == content


class TestParseTheorem:
    """Tests for parse_theorem function."""

    def test_simple_theorem(self):
        """Test parsing a simple theorem with one parameter."""
        theorem = "theorem foo (n : Nat) : n = n := by sorry"
        result = parse_theorem(theorem)

        assert result.name == "foo"
        assert len(result.params) == 1
        assert result.params[0].name == "n"
        assert result.params[0].ty == "Nat"
        assert result.final_goal == "n = n"

    def test_multiline_theorem_with_many_params(self):
        """Test parsing the exact multi-line theorem from the user's issue."""
        theorem = """theorem goal_1_h_inv_kminus2_pair_h_invariant_at_kminus2
    (n : ℕ) (if_neg_1 : ¬n = 0) (if_neg_2 : ¬n = 2)
    (curr : ℕ) (f0 : ℕ) (f2 : ℕ)
    (k : ℕ) (a : k % 2 = 0)
    (a_1 : 4 ≤ k) (a_2 : k ≤ n + 2)
    (i : ℕ) (i_1 : ℕ) (i_2 : ℕ) (k_1 : ℕ)
    (if_neg : n % 2 = 0)
    (invariant_2 : 4 ≤ k →
      f0 = dominoTilingRecurrence (k - 4) ∧
      f2 = dominoTilingRecurrence (k - 2))
    (done_1 : n < k)
    (i_3 : curr = i ∧ f0 = i_1 ∧ f2 = i_2 ∧ k = k_1) :
    f0 = dominoTilingRecurrence ((k - 2) - 4) ∧
    f2 = dominoTilingRecurrence ((k - 2) - 2) := by
  sorry"""

        result = parse_theorem(theorem)

        assert result.name == "goal_1_h_inv_kminus2_pair_h_invariant_at_kminus2"

        expected_param_names = [
            "n", "if_neg_1", "if_neg_2", "curr", "f0", "f2",
            "k", "a", "a_1", "a_2", "i", "i_1", "i_2", "k_1",
            "if_neg", "invariant_2", "done_1", "i_3",
        ]

        assert len(result.params) == len(expected_param_names), (
            f"Expected {len(expected_param_names)} params, got {len(result.params)}: {[p.name for p in result.params]}"
        )

        for i, expected_name in enumerate(expected_param_names):
            assert result.params[i].name == expected_name, (
                f"Param {i}: expected '{expected_name}', got '{result.params[i].name}'"
            )

    def test_params_string_multiline(self):
        """Test that params_string() returns all params correctly."""
        theorem = """theorem goal_1_h_inv_kminus2_pair_h_invariant_at_kminus2
    (n : ℕ) (if_neg_1 : ¬n = 0) (if_neg_2 : ¬n = 2)
    (curr : ℕ) (f0 : ℕ) (f2 : ℕ)
    (k : ℕ) (a : k % 2 = 0)
    (a_1 : 4 ≤ k) (a_2 : k ≤ n + 2)
    (i : ℕ) (i_1 : ℕ) (i_2 : ℕ) (k_1 : ℕ)
    (if_neg : n % 2 = 0)
    (invariant_2 : 4 ≤ k →
      f0 = dominoTilingRecurrence (k - 4) ∧
      f2 = dominoTilingRecurrence (k - 2))
    (done_1 : n < k)
    (i_3 : curr = i ∧ f0 = i_1 ∧ f2 = i_2 ∧ k = k_1) :
    f0 = dominoTilingRecurrence ((k - 2) - 4) ∧
    f2 = dominoTilingRecurrence ((k - 2) - 2) := by
  sorry"""

        result = parse_theorem(theorem)
        params_str = result.params_string()

        assert "(n : ℕ)" in params_str
        assert "(k : ℕ)" in params_str
        assert "(f0 : ℕ)" in params_str
        assert "(f2 : ℕ)" in params_str
        assert len(params_str) > 0

    def test_theorem_with_complex_nested_type(self):
        """Test theorem with deeply nested types in parameters."""
        theorem = """theorem test_nested
    (f : (a : Nat) → (b : Nat) → a + b = b + a)
    (g : ∀ x : Nat, x = x) :
    True := by sorry"""

        result = parse_theorem(theorem)

        assert result.name == "test_nested"
        assert len(result.params) == 2
        assert result.params[0].name == "f"
        assert result.params[1].name == "g"

    def test_theorem_with_unicode_chars(self):
        """Test theorem with various Unicode characters."""
        theorem = "theorem unicode_test (α : Type) (β : α → Prop) (x : α) (h : β x) : β x := by sorry"

        result = parse_theorem(theorem)

        assert result.name == "unicode_test"
        assert len(result.params) == 4
        assert result.params[0].name == "α"
        assert result.params[1].name == "β"


class TestParamNames:
    """Tests for param_names() method."""

    def test_param_names_simple(self):
        """Test param_names returns just the names."""
        theorem = "theorem foo (n : Nat) (m : Nat) : n = m := by sorry"
        result = parse_theorem(theorem)

        names = result.param_names()
        assert names == "n m"

    def test_param_names_multiline(self):
        """Test param_names with multiline theorem."""
        theorem = """theorem bar
    (a : Nat) (b : Nat)
    (c : Nat) :
    a + b = c := by sorry"""

        result = parse_theorem(theorem)
        names = result.param_names()

        assert "a" in names
        assert "b" in names
        assert "c" in names
