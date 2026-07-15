"""Tests for unused variable removal utilities."""

import pytest
from utils.lean.types import Goal, Param, LeanDiagnostic
from utils.lean.parser import LeanFile
from utils.lean.unused_var_removal import (
    extract_unused_vars,
    filter_goal_params,
    replace_theorem_signature,
    temp_section_name_for_goal,
)


class TestExtractUnusedVars:
    """Tests for extract_unused_vars function."""

    def test_extracts_single_unused_var(self):
        diagnostics = [
            LeanDiagnostic(
                severity="warning",
                line=10,
                column=5,
                message="unused variable `arr`\n\nNote: This linter can be disabled...",
            )
        ]
        result = extract_unused_vars(diagnostics)
        assert result == {"arr"}

    def test_extracts_multiple_unused_vars(self):
        diagnostics = [
            LeanDiagnostic(severity="warning", line=10, column=5, message="unused variable `arr`"),
            LeanDiagnostic(severity="warning", line=12, column=5, message="unused variable `idx`"),
            LeanDiagnostic(severity="warning", line=15, column=5, message="unused variable `h`"),
        ]
        result = extract_unused_vars(diagnostics)
        assert result == {"arr", "idx", "h"}

    def test_ignores_non_warning_diagnostics(self):
        diagnostics = [
            LeanDiagnostic(severity="error", line=10, column=5, message="unused variable `arr`"),
            LeanDiagnostic(severity="info", line=12, column=5, message="unused variable `idx`"),
        ]
        result = extract_unused_vars(diagnostics)
        assert result == set()

    def test_ignores_non_unused_var_warnings(self):
        diagnostics = [
            LeanDiagnostic(severity="warning", line=10, column=5, message="declaration uses sorry"),
            LeanDiagnostic(severity="warning", line=12, column=5, message="some other warning"),
        ]
        result = extract_unused_vars(diagnostics)
        assert result == set()

    def test_respects_line_filter(self):
        diagnostics = [
            LeanDiagnostic(severity="warning", line=5, column=5, message="unused variable `a`"),
            LeanDiagnostic(severity="warning", line=15, column=5, message="unused variable `b`"),
            LeanDiagnostic(severity="warning", line=25, column=5, message="unused variable `c`"),
        ]
        # Only include lines 10-20
        result = extract_unused_vars(diagnostics, line_filter=lambda line: 10 <= line <= 20)
        assert result == {"b"}

    def test_empty_diagnostics(self):
        result = extract_unused_vars([])
        assert result == set()


class TestFilterGoalParams:
    """Tests for filter_goal_params function."""

    def test_filters_unused_params(self):
        goal = Goal(
            name="test_goal",
            params=[
                Param(name="arr", ty="List Int"),
                Param(name="h", ty="arr.length > 0"),
                Param(name="unused", ty="Nat"),
            ],
            final_goal="1 > 0",
        )
        result = filter_goal_params(goal, {"unused"})

        assert result.name == "test_goal"
        assert len(result.params) == 2
        assert result.params[0].name == "arr"
        assert result.params[1].name == "h"
        assert result.final_goal == "1 > 0"

    def test_filters_multiple_params(self):
        goal = Goal(
            name="test_goal",
            params=[
                Param(name="a", ty="Nat"),
                Param(name="b", ty="Nat"),
                Param(name="c", ty="Nat"),
                Param(name="d", ty="Nat"),
            ],
            final_goal="True",
        )
        result = filter_goal_params(goal, {"a", "c"})

        assert len(result.params) == 2
        assert [p.name for p in result.params] == ["b", "d"]

    def test_no_unused_vars_returns_same_goal(self):
        goal = Goal(
            name="test_goal",
            params=[Param(name="x", ty="Nat")],
            final_goal="x > 0",
        )
        result = filter_goal_params(goal, set())
        assert result is goal  # Should return the same object

    def test_unused_vars_not_in_params(self):
        goal = Goal(
            name="test_goal",
            params=[Param(name="x", ty="Nat")],
            final_goal="x > 0",
        )
        result = filter_goal_params(goal, {"nonexistent"})
        assert result is goal  # No change, returns same object

    def test_preserves_case_tag(self):
        goal = Goal(
            name="test_goal",
            params=[
                Param(name="x", ty="Nat"),
                Param(name="y", ty="Nat"),
            ],
            final_goal="True",
            case_tag="case_1",
        )
        result = filter_goal_params(goal, {"y"})
        assert result.case_tag == "case_1"

    def test_preserves_param_order(self):
        goal = Goal(
            name="test_goal",
            params=[
                Param(name="T", ty="Type"),
                Param(name="x", ty="T"),
                Param(name="unused", ty="Nat"),
            ],
            final_goal="True",
        )
        result = filter_goal_params(goal, {"unused"})

        assert len(result.params) == 2
        assert result.params[0].name == "T"
        assert result.params[1].name == "x"


class TestReplaceTheoremSignature:
    """Tests for replace_theorem_signature function."""

    def test_replaces_simple_signature(self):
        theorem = "theorem goal_0 (x : Nat) (y : Nat) : x + y = y + x := by omega"
        filtered_goal = Goal(
            name="goal_0",
            params=[Param(name="x", ty="Nat")],
            final_goal="x + y = y + x",
        )
        result = replace_theorem_signature(theorem, filtered_goal)

        assert "theorem goal_0" in result
        assert "(x : Nat)" in result
        assert ": x + y = y + x" in result
        assert ":= by omega" in result
        # Verify y is not in the result params
        assert "(y : Nat)" not in result

    def test_preserves_multiline_proof(self):
        theorem = """theorem goal_0 (x : Nat) (y : Nat) : True := by
  simp
  trivial"""
        filtered_goal = Goal(
            name="goal_0",
            params=[Param(name="x", ty="Nat")],
            final_goal="True",
        )
        result = replace_theorem_signature(theorem, filtered_goal)

        assert "simp" in result
        assert "trivial" in result

    def test_raises_on_missing_by_proof(self):
        """Test that theorems without ':= by' raise ValueError."""
        theorem = "theorem goal_0 (x : Nat) : True"  # No := by
        filtered_goal = Goal(
            name="goal_0",
            params=[],
            final_goal="True",
        )

        with pytest.raises(ValueError, match="Could not find ':= by'"):
            replace_theorem_signature(theorem, filtered_goal)

    # Note: term mode proofs (e.g., := rfl) are not supported.
    # We only handle tactic mode proofs (:= by ...).


class TestTempSectionNameForGoal:
    """Tests for temp_section_name_for_goal function."""

    def test_generates_correct_name(self):
        assert temp_section_name_for_goal("goal_0") == "Proof_goal_0"
        assert temp_section_name_for_goal("my_theorem") == "Proof_my_theorem"
        assert temp_section_name_for_goal("parent_0_1") == "Proof_parent_0_1"


