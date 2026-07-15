#!/usr/bin/env python3
"""Test parse_lean_goals function with multi-line goals."""

import unittest
from utils.lean.goals import parse_lean_goals
from utils.lean.types import Goal, Param


class TestParseLeanGoalsMultiline(unittest.TestCase):
    """Test cases for parse_lean_goals with multi-line goal statements."""

    def test_single_line_goal(self):
        """Test parsing a simple single-line goal."""
        content = """firstStr secondStr : String
⊢ firstStr = secondStr"""

        goals = parse_lean_goals(content)

        self.assertEqual(len(goals), 1)
        goal = goals[0]
        self.assertEqual(goal.name, "goal_0")
        self.assertEqual(len(goal.params), 2)
        self.assertEqual(goal.params[0].name, "firstStr")
        self.assertEqual(goal.params[0].ty, "String")
        self.assertEqual(goal.params[1].name, "secondStr")
        self.assertEqual(goal.params[1].ty, "String")
        self.assertEqual(goal.final_goal, "firstStr = secondStr")

    def test_multiline_goal_with_indentation(self):
        """Test parsing a multi-line goal with proper indentation."""
        content = """firstStr secondStr : String
require_1 : precondition firstStr secondStr
i : ℕ
result : String
a_1 : i ≤ firstStr.data.length
invariant_2 : result.data = List.filter (fun c ↦ !charInString c secondStr) (List.take i firstStr.data)
if_pos : i < firstStr.data.length
a : True
if_pos_1 : charInString (firstStr.data[i]?.getD 'A') secondStr = false
⊢ result.data ++ [firstStr.data[i]?.getD 'A'] =
    List.filter (fun c ↦ !charInString c secondStr) (List.take (i + 1) firstStr.data)"""

        goals = parse_lean_goals(content)

        self.assertEqual(len(goals), 1)
        goal = goals[0]
        self.assertEqual(goal.name, "goal_0")

        # Check parameters
        self.assertEqual(len(goal.params), 10)
        param_names = [p.name for p in goal.params]
        expected_names = ["firstStr", "secondStr", "require_1", "i", "result", "a_1", "invariant_2", "if_pos", "a", "if_pos_1"]
        self.assertEqual(param_names, expected_names)

        # Check that the goal includes both lines
        expected_goal = "result.data ++ [firstStr.data[i]?.getD 'A'] = List.filter (fun c ↦ !charInString c secondStr) (List.take (i + 1) firstStr.data)"
        self.assertEqual(goal.final_goal, expected_goal)

    def test_multiline_goal_with_deep_indentation(self):
        """Test parsing a goal with multiple levels of indentation."""
        content = """x y : Nat
⊢ x + y =
    match x with
    | 0 => y
    | n + 1 => (n + y) + 1"""

        goals = parse_lean_goals(content)

        self.assertEqual(len(goals), 1)
        goal = goals[0]
        expected_goal = "x + y = match x with | 0 => y | n + 1 => (n + y) + 1"
        self.assertEqual(goal.final_goal, expected_goal)

    def test_multiple_multiline_goals(self):
        """Test parsing multiple goals where some are multi-line."""
        content = """x : Nat
⊢ x = x

y z : Nat
⊢ y + z =
    z + y

a b : String
⊢ a ++ b = b ++ a"""

        goals = parse_lean_goals(content)

        self.assertEqual(len(goals), 3)

        # First goal (single line)
        self.assertEqual(goals[0].final_goal, "x = x")

        # Second goal (multi-line)
        self.assertEqual(goals[1].final_goal, "y + z = z + y")

        # Third goal (single line)
        self.assertEqual(goals[2].final_goal, "a ++ b = b ++ a")

    def test_goal_with_empty_lines_and_indentation(self):
        """Test parsing goal with empty lines and various indentation."""
        content = """x : Nat
⊢ x + 0 =
    x

y : Nat
⊢ y = y"""

        goals = parse_lean_goals(content)

        self.assertEqual(len(goals), 2)
        self.assertEqual(goals[0].final_goal, "x + 0 = x")
        self.assertEqual(goals[1].final_goal, "y = y")

    def test_complex_multiline_with_special_chars(self):
        """Test parsing complex multi-line goal with special mathematical characters."""
        content = """α : Type
f g : α → α
⊢ ∀ x : α,
    f (g x) = g (f x) →
    f ∘ g = g ∘ f"""

        goals = parse_lean_goals(content)

        self.assertEqual(len(goals), 1)
        goal = goals[0]
        expected_goal = "∀ x : α, f (g x) = g (f x) → f ∘ g = g ∘ f"
        self.assertEqual(goal.final_goal, expected_goal)

    def test_goal_with_case_statement(self):
        """Test parsing goals with case statements."""
        content = """x : Nat
⊢ x + 0 = x

case zero
y : Nat
⊢ y = 0"""

        goals = parse_lean_goals(content)

        # Should parse both goals - the parser doesn't stop at case statements
        self.assertEqual(len(goals), 2)
        self.assertEqual(goals[0].final_goal, "x + 0 = x")
        self.assertEqual(goals[1].final_goal, "y = 0")

    def test_from_prepare_goals_node_example(self):
        """Test based on the actual output from _prepare_goals_node in test_prepare_goals_node.py."""
        # This is the actual output that was showing truncation issues
        content = """case «result.data = (firstChars.take i).filter (fun c ↦ !charInString c secondStr)»
firstStr secondStr : String
require_1 : precondition firstStr secondStr
i : ℕ
result : String
a_1 : i ≤ firstStr.data.length
invariant_2 : result.data = List.filter (fun c ↦ !charInString c secondStr) (List.take i firstStr.data)
if_pos : i < firstStr.data.length
a : True
if_pos_1 : charInString (firstStr.data[i]?.getD 'A') secondStr = false
⊢ result.data ++ [firstStr.data[i]?.getD 'A'] =
    List.filter (fun c ↦ !charInString c secondStr) (List.take (i + 1) firstStr.data)"""

        goals = parse_lean_goals(content)

        self.assertEqual(len(goals), 1)
        goal = goals[0]

        # Before the fix, this would be truncated to just "result.data ++ [firstStr.data[i]?.getD 'A'] ="
        # After the fix, it should include the complete goal
        self.assertIn("List.filter (fun c ↦ !charInString c secondStr) (List.take (i + 1) firstStr.data)", goal.final_goal)

        # Ensure the goal doesn't end with just "=" (which was the bug)
        self.assertFalse(goal.final_goal.endswith("="))

        # Verify the complete expected goal
        expected_goal = "result.data ++ [firstStr.data[i]?.getD 'A'] = List.filter (fun c ↦ !charInString c secondStr) (List.take (i + 1) firstStr.data)"
        self.assertEqual(goal.final_goal, expected_goal)

        # Test the bug scenario: ensure goal name and params are correct
        self.assertEqual(goal.name, "goal_0")
        self.assertEqual(len(goal.params), 10)

        # Check specific parameters from the removeChars function
        param_dict = {p.name: p.ty for p in goal.params}
        self.assertEqual(param_dict["firstStr"], "String")
        self.assertEqual(param_dict["secondStr"], "String")
        self.assertEqual(param_dict["i"], "ℕ")
        self.assertEqual(param_dict["result"], "String")
        self.assertIn("precondition firstStr secondStr", param_dict["require_1"])

    def test_goal_as_sorried_with_multiline(self):
        """Test that as_sorried() works correctly with multi-line goals."""
        content = """x : Nat
⊢ x + 0 =
    0 + x"""

        goals = parse_lean_goals(content)
        goal = goals[0]

        sorried_theorem = goal.as_sorried()

        # Should contain the complete goal in theorem format
        self.assertIn("x + 0 = 0 + x", sorried_theorem)
        self.assertIn("theorem goal_0", sorried_theorem)
        self.assertIn("(x : Nat)", sorried_theorem)
        self.assertIn("sorry", sorried_theorem)  # Just "sorry", not "by sorry"


if __name__ == "__main__":
    unittest.main()