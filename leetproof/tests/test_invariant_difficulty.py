"""Tests for invariant goal extraction utilities."""

from utils.velvet_helpers import (
    _parse_invariant_case_tag,
    extract_invariant_goals,
)
from utils.lean.types import Param


class TestParseInvariantCaseTag:
    def test_parse_name_and_statement(self):
        name, stmt = _parse_invariant_case_tag("invariant_loop_bounds: some property")
        assert name == "loop_bounds"
        assert stmt == "some property"

    def test_parse_unicode_case_tag(self):
        name, stmt = _parse_invariant_case_tag("«invariant_9: ∀ k, k < dp.size → dp[k]! ≤ m ∧ dp[k]! ≤ n»")
        assert name == "9"
        assert stmt == "∀ k, k < dp.size → dp[k]! ≤ m ∧ dp[k]! ≤ n"

    def test_skip_ensures_goals(self):
        name, stmt = _parse_invariant_case_tag("«ensures_1: postcondition»")
        assert name is None
        assert stmt is None

    def test_handle_none_case_tag(self):
        name, stmt = _parse_invariant_case_tag(None)
        assert name is None
        assert stmt is None


class TestExtractInvariantGoals:
    def test_extract_multiple_invariant_goals(self):
        diagnostic = """unsolved goals
case «invariant_1: test property»
a b : Int
⊢ a + b = b + a

case «invariant_2: other property»
x : Int
⊢ x > 0

case «ensures_1: postcondition»
result : Int
⊢ result = 42
"""
        inv_goals, non_inv_goals = extract_invariant_goals(diagnostic)

        assert len(inv_goals) == 2
        assert inv_goals[0].invariant_name == "1"
        assert inv_goals[0].invariant_statement == "test property"
        assert inv_goals[0].goal.final_goal == "a + b = b + a"
        assert inv_goals[1].invariant_name == "2"
        assert inv_goals[1].invariant_statement == "other property"
        assert inv_goals[1].goal.final_goal == "x > 0"
        
        assert len(non_inv_goals) == 1
        assert non_inv_goals[0].goal_type == "ensures"
        assert non_inv_goals[0].goal.final_goal == "result = 42"

    def test_exclude_postconditions(self):
        diagnostic = """unsolved goals
case «invariant_1: a > 0»
a : Int
⊢ a > 0

case «ensures_1: postcond»
b : Int
⊢ b = 5
"""
        inv_goals, non_inv_goals = extract_invariant_goals(diagnostic)

        assert len(inv_goals) == 1
        assert inv_goals[0].invariant_name == "1"
        assert inv_goals[0].invariant_statement == "a > 0"
        
        assert len(non_inv_goals) == 1
        assert non_inv_goals[0].goal_type == "ensures"
        assert non_inv_goals[0].goal.final_goal == "b = 5"

    def test_preserves_hypotheses_and_statement(self):
        diagnostic = """unsolved goals
case «invariant_bounds: 0 ≤ i ∧ i ≤ n»
i n : Nat
h : i < n
⊢ i + 1 ≤ n
"""
        inv_goals, non_inv_goals = extract_invariant_goals(diagnostic)

        assert len(inv_goals) == 1
        assert inv_goals[0].invariant_name == "bounds"
        assert inv_goals[0].invariant_statement == "0 ≤ i ∧ i ≤ n"
        assert inv_goals[0].goal.final_goal == "i + 1 ≤ n"
        assert inv_goals[0].goal.params == [
            Param("i", "Nat"),
            Param("n", "Nat"),
            Param("h", "i < n"),
        ]
        
        assert len(non_inv_goals) == 0
