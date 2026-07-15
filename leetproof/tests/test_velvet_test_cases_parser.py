"""Tests for parse_test_cases and construct_assertion_snippet functions."""

import pytest
from utils.lean.parser import parse_test_cases, VelvetTestCase
from utils.velvet_types import VelvetMethod, NameInfo
from utils.velvet_helpers import construct_assertion_snippet, construct_assertion_snippet_v2


class TestParseVelvetTestCases:
    """Tests for parse_test_cases function."""

    def test_simple_test_case(self):
        """Test parsing simple test cases with non-mutable params."""
        content = """
def test1_a := 5
def test1_b := 10
def test1_Expected := 15

def test2_a := 0
def test2_b := 0
def test2_Expected := 0
"""
        method = VelvetMethod(
            name="Add",
            params=[
                NameInfo(name="a", ty="Int", is_mut=False),
                NameInfo(name="b", ty="Int", is_mut=False),
            ],
            returns=NameInfo(name="result", ty="Int", is_mut=False),
            requires=[],
            ensures=[],
        )

        test_cases = parse_test_cases(content, method)

        assert len(test_cases) == 2

        assert test_cases[0].id == 1
        assert test_cases[0].name == "test1"
        assert test_cases[0].inputs == {"a": "5", "b": "10"}
        assert test_cases[0].expected_return == "15"
        assert test_cases[0].expected_mutations == {}

        assert test_cases[1].id == 2
        assert test_cases[1].name == "test2"
        assert test_cases[1].inputs == {"a": "0", "b": "0"}
        assert test_cases[1].expected_return == "0"

    def test_mutable_params(self):
        """Test parsing test cases with mutable params."""
        content = """
def test1_arr := #[1, 2, 3]
def test1_Expected := ()
def test1_Expected_arr := #[3, 2, 1]
"""
        method = VelvetMethod(
            name="ReverseInPlace",
            params=[
                NameInfo(name="arr", ty="Array Int", is_mut=True),
            ],
            returns=NameInfo(name="result", ty="Unit", is_mut=False),
            requires=[],
            ensures=[],
        )

        test_cases = parse_test_cases(content, method)

        assert len(test_cases) == 1
        assert test_cases[0].id == 1
        assert test_cases[0].inputs == {"arr": "#[1, 2, 3]"}
        assert test_cases[0].expected_return == "()"
        assert test_cases[0].expected_mutations == {"arr": "#[3, 2, 1]"}

    def test_multiple_mutable_params(self):
        """Test parsing test cases with multiple mutable params."""
        content = """
def test1_a := #[1, 2]
def test1_b := #[3, 4]
def test1_Expected := ()
def test1_Expected_a := #[3, 4]
def test1_Expected_b := #[1, 2]
"""
        method = VelvetMethod(
            name="Swap",
            params=[
                NameInfo(name="a", ty="Array Int", is_mut=True),
                NameInfo(name="b", ty="Array Int", is_mut=True),
            ],
            returns=NameInfo(name="result", ty="Unit", is_mut=False),
            requires=[],
            ensures=[],
        )

        test_cases = parse_test_cases(content, method)

        assert len(test_cases) == 1
        assert test_cases[0].inputs == {"a": "#[1, 2]", "b": "#[3, 4]"}
        assert test_cases[0].expected_return == "()"
        assert test_cases[0].expected_mutations == {"a": "#[3, 4]", "b": "#[1, 2]"}

    def test_ordering_by_id(self):
        """Test that test cases are ordered by id."""
        content = """
def test3_x := 3
def test3_Expected := 9

def test1_x := 1
def test1_Expected := 1

def test2_x := 2
def test2_Expected := 4
"""
        method = VelvetMethod(
            name="Square",
            params=[NameInfo(name="x", ty="Int", is_mut=False)],
            returns=NameInfo(name="result", ty="Int", is_mut=False),
            requires=[],
            ensures=[],
        )

        test_cases = parse_test_cases(content, method)

        assert len(test_cases) == 3
        assert test_cases[0].id == 1
        assert test_cases[1].id == 2
        assert test_cases[2].id == 3

    def test_str_method(self):
        """Test __str__ method returns test name."""
        content = """
def test1_x := 1
def test1_Expected := 1
"""
        method = VelvetMethod(
            name="Identity",
            params=[NameInfo(name="x", ty="Int", is_mut=False)],
            returns=NameInfo(name="result", ty="Int", is_mut=False),
            requires=[],
            ensures=[],
        )

        test_cases = parse_test_cases(content, method)

        assert str(test_cases[0]) == "test1"

    def test_empty_content(self):
        """Test parsing empty content returns empty list."""
        method = VelvetMethod(
            name="Foo",
            params=[NameInfo(name="x", ty="Int", is_mut=False)],
            returns=NameInfo(name="result", ty="Int", is_mut=False),
            requires=[],
            ensures=[],
        )

        test_cases = parse_test_cases("", method)
        assert test_cases == []


class TestConstructAssertionSnippet:
    """Tests for construct_assertion_snippet function."""

    def test_simple_method(self):
        """Test assertion for simple non-mutable method."""
        method = VelvetMethod(
            name="Add",
            params=[
                NameInfo(name="a", ty="Int", is_mut=False),
                NameInfo(name="b", ty="Int", is_mut=False),
            ],
            returns=NameInfo(name="result", ty="Int", is_mut=False),
            requires=[],
            ensures=[],
        )
        test_case = VelvetTestCase(
            id=1,
            inputs={"a": "5", "b": "10"},
            expected_return="15",
            expected_mutations={},
        )

        snippet = construct_assertion_snippet(method, test_case)

        assert "/--" in snippet
        assert "info: DivM.res 15" in snippet
        assert "#guard_msgs in" in snippet
        # Uses def names, not inlined values
        assert "#eval (Add test1_a test1_b).run" in snippet

    def test_mutable_param(self):
        """Test assertion for method with mutable param."""
        method = VelvetMethod(
            name="ReverseInPlace",
            params=[
                NameInfo(name="arr", ty="Array Int", is_mut=True),
            ],
            returns=NameInfo(name="result", ty="Unit", is_mut=False),
            requires=[],
            ensures=[],
        )
        test_case = VelvetTestCase(
            id=1,
            inputs={"arr": "#[1, 2, 3]"},
            expected_return="()",
            expected_mutations={"arr": "#[3, 2, 1]"},
        )

        snippet = construct_assertion_snippet(method, test_case)

        # Expected result has inlined values
        assert "info: DivM.res ((), #[3, 2, 1])" in snippet
        # Method call uses def names
        assert "#eval (ReverseInPlace test1_arr).run" in snippet

    def test_multiple_mutable_params(self):
        """Test assertion for method with multiple mutable params."""
        method = VelvetMethod(
            name="Swap",
            params=[
                NameInfo(name="a", ty="Array Int", is_mut=True),
                NameInfo(name="b", ty="Array Int", is_mut=True),
            ],
            returns=NameInfo(name="result", ty="Unit", is_mut=False),
            requires=[],
            ensures=[],
        )
        test_case = VelvetTestCase(
            id=2,
            inputs={"a": "#[1]", "b": "#[2]"},
            expected_return="()",
            expected_mutations={"a": "#[2]", "b": "#[1]"},
        )

        snippet = construct_assertion_snippet(method, test_case)

        # Expected result has inlined values
        assert "info: DivM.res ((), #[2], #[1])" in snippet
        # Method call uses def names with test2 prefix
        assert "#eval (Swap test2_a test2_b).run" in snippet

    def test_swap_stuff_end_to_end(self):
        """End-to-end test: parse method, parse test cases, construct assertion."""
        from utils.velvet_helpers import get_velvet_method

        method_content = """
method SwapStuff (mut a: Array Int) (mut b: Array Int) return (c: Unit)
  ensures True
  ensures aOld = b
  ensures bOld = a
  do
    let c := a
    a := b
    b := c
    return ()
"""

        test_cases_content = """
def test1_a : Array Int:= #[1, 2, 3]
def test1_b : Array Int := #[4, 5, 6]
def test1_Expected := ()
def test1_Expected_a : Array Int := #[4, 5, 6]
def test1_Expected_b : Array Int:= #[1, 2, 3]
"""

        # Parse method
        method = get_velvet_method(method_content)
        assert method.name == "SwapStuff"
        assert len(method.params) == 2
        assert method.params[0].is_mut
        assert method.params[1].is_mut

        # Parse test cases
        test_cases = parse_test_cases(test_cases_content, method)
        assert len(test_cases) == 1

        tc = test_cases[0]
        assert tc.id == 1
        assert tc.inputs == {"a": "#[1, 2, 3]", "b": "#[4, 5, 6]"}
        assert tc.expected_return == "()"
        assert tc.expected_mutations == {"a": "#[4, 5, 6]", "b": "#[1, 2, 3]"}

        # Construct assertion
        snippet = construct_assertion_snippet(method, tc)
        assert "info: DivM.res ((), #[4, 5, 6], #[1, 2, 3])" in snippet
        assert "#eval (SwapStuff test1_a test1_b).run" in snippet


class TestConstructAssertionSnippetV2:
    """Tests for construct_assertion_snippet_v2 function.

    v2 uses #assert_same_evaluation with def references instead of inlined values.
    """

    def test_simple_method(self):
        """Test assertion for simple non-mutable method."""
        method = VelvetMethod(
            name="Add",
            params=[
                NameInfo(name="a", ty="Int", is_mut=False),
                NameInfo(name="b", ty="Int", is_mut=False),
            ],
            returns=NameInfo(name="result", ty="Int", is_mut=False),
            requires=[],
            ensures=[],
        )
        test_case = VelvetTestCase(
            id=1,
            inputs={"a": "5", "b": "10"},
            expected_return="15",
            expected_mutations={},
        )

        snippet = construct_assertion_snippet_v2(method, test_case)

        expected = """
#assert_same_evaluation #[((Add test1_a test1_b).run), DivM.res test1_Expected ]"""
        assert snippet == expected

    def test_mutable_param(self):
        """Test assertion for method with mutable param."""
        method = VelvetMethod(
            name="ReverseInPlace",
            params=[
                NameInfo(name="arr", ty="Array Int", is_mut=True),
            ],
            returns=NameInfo(name="result", ty="Unit", is_mut=False),
            requires=[],
            ensures=[],
        )
        test_case = VelvetTestCase(
            id=1,
            inputs={"arr": "#[1, 2, 3]"},
            expected_return="()",
            expected_mutations={"arr": "#[3, 2, 1]"},
        )

        snippet = construct_assertion_snippet_v2(method, test_case)

        expected = """
#assert_same_evaluation #[((ReverseInPlace test1_arr).run), DivM.res (test1_Expected, test1_Expected_arr) ]"""
        assert snippet == expected

    def test_multiple_mutable_params(self):
        """Test assertion for method with multiple mutable params."""
        method = VelvetMethod(
            name="Swap",
            params=[
                NameInfo(name="a", ty="Array Int", is_mut=True),
                NameInfo(name="b", ty="Array Int", is_mut=True),
            ],
            returns=NameInfo(name="result", ty="Unit", is_mut=False),
            requires=[],
            ensures=[],
        )
        test_case = VelvetTestCase(
            id=2,
            inputs={"a": "#[1]", "b": "#[2]"},
            expected_return="()",
            expected_mutations={"a": "#[2]", "b": "#[1]"},
        )

        snippet = construct_assertion_snippet_v2(method, test_case)

        expected = """
#assert_same_evaluation #[((Swap test2_a test2_b).run), DivM.res (test2_Expected, test2_Expected_a, test2_Expected_b) ]"""
        assert snippet == expected

    def test_unit_return_no_mutations_no_params(self):
        """Test method returning Unit with no mutations and no params."""
        method = VelvetMethod(
            name="PrintHello",
            params=[],
            returns=NameInfo(name="result", ty="Unit", is_mut=False),
            requires=[],
            ensures=[],
        )
        test_case = VelvetTestCase(
            id=1,
            inputs={},
            expected_return="()",
            expected_mutations={},
        )

        snippet = construct_assertion_snippet_v2(method, test_case)

        expected = """
#assert_same_evaluation #[((PrintHello ).run), DivM.res test1_Expected ]"""
        assert snippet == expected

    def test_single_param(self):
        """Test with single parameter."""
        method = VelvetMethod(
            name="Double",
            params=[NameInfo(name="x", ty="Int", is_mut=False)],
            returns=NameInfo(name="result", ty="Int", is_mut=False),
            requires=[],
            ensures=[],
        )
        test_case = VelvetTestCase(
            id=3,
            inputs={"x": "5"},
            expected_return="10",
            expected_mutations={},
        )

        snippet = construct_assertion_snippet_v2(method, test_case)

        expected = """
#assert_same_evaluation #[((Double test3_x).run), DivM.res test3_Expected ]"""
        assert snippet == expected

    def test_complex_return_type(self):
        """Test with complex return type like tuple."""
        method = VelvetMethod(
            name="DivMod",
            params=[
                NameInfo(name="a", ty="Nat", is_mut=False),
                NameInfo(name="b", ty="Nat", is_mut=False),
            ],
            returns=NameInfo(name="result", ty="Nat × Nat", is_mut=False),
            requires=[],
            ensures=[],
        )
        test_case = VelvetTestCase(
            id=1,
            inputs={"a": "10", "b": "3"},
            expected_return="(3, 1)",
            expected_mutations={},
        )

        snippet = construct_assertion_snippet_v2(method, test_case)

        expected = """
#assert_same_evaluation #[((DivMod test1_a test1_b).run), DivM.res test1_Expected ]"""
        assert snippet == expected
