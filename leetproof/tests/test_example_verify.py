"""Tests for utils/example_verify.py"""

import pytest
from utils.example_verify import extract_specs_section, parse_specs_content


class TestExtractSpecsSection:
    def test_basic_extraction(self):
        content = """
section Specs

def precondition (x : Nat) : Prop := True

def postcondition (x : Nat) (result : Nat) : Prop := result = x

end Specs
"""
        result = extract_specs_section(content)
        assert "def precondition" in result
        assert "def postcondition" in result

    def test_missing_section_specs(self):
        content = "def foo := 1"
        with pytest.raises(ValueError, match="Cannot find 'section Specs'"):
            extract_specs_section(content)

    def test_missing_end_specs(self):
        content = "section Specs\ndef foo := 1"
        with pytest.raises(ValueError, match="Cannot find 'end Specs'"):
            extract_specs_section(content)


class TestParseSpecsContent:
    def test_single_line_params(self):
        """Test parsing with all parameters on single lines."""
        specs_content = """
def precondition (x : Nat) (y : Nat) : Prop := True

def postcondition (x : Nat) (y : Nat) (result : Nat) : Prop := result = x + y
"""
        result = parse_specs_content(specs_content)

        assert result['precond_params_list'] == [('x', 'Nat'), ('y', 'Nat')]
        assert result['postcond_params_list'] == [('x', 'Nat'), ('y', 'Nat'), ('result', 'Nat')]
        assert result['return_param'] == ('result', 'Nat')

    def test_multi_line_postcondition_params(self):
        """Test parsing when postcondition parameters span multiple lines."""
        specs_content = """
def precondition (src : Array Int) (sStart : Nat) (dest : Array Int) (dStart : Nat) (len : Nat) : Prop :=
  sStart + len <= src.size

def postcondition (src : Array Int) (sStart : Nat) (dest : Array Int) (dStart : Nat) (len : Nat)
    (result : Array Int) : Prop :=
  result.size = dest.size
"""
        result = parse_specs_content(specs_content)

        assert result['precond_params_list'] == [
            ('src', 'Array Int'),
            ('sStart', 'Nat'),
            ('dest', 'Array Int'),
            ('dStart', 'Nat'),
            ('len', 'Nat'),
        ]
        assert result['postcond_params_list'] == [
            ('src', 'Array Int'),
            ('sStart', 'Nat'),
            ('dest', 'Array Int'),
            ('dStart', 'Nat'),
            ('len', 'Nat'),
            ('result', 'Array Int'),
        ]
        assert result['return_param'] == ('result', 'Array Int')

    def test_complex_types(self):
        """Test parsing with complex nested types."""
        specs_content = """
def precondition (arr : Array (List Int)) (f : Int -> Bool) : Prop := True

def postcondition (arr : Array (List Int)) (f : Int -> Bool) (result : Option Int) : Prop := True
"""
        result = parse_specs_content(specs_content)

        assert result['precond_params_list'] == [
            ('arr', 'Array (List Int)'),
            ('f', 'Int -> Bool'),
        ]
        assert result['postcond_params_list'] == [
            ('arr', 'Array (List Int)'),
            ('f', 'Int -> Bool'),
            ('result', 'Option Int'),
        ]

    def test_with_helpers(self):
        """Test that helpers before precondition are extracted."""
        specs_content = """
def isSorted (arr : Array Int) : Prop :=
  forall i j, i < j -> arr[i]! <= arr[j]!

def precondition (arr : Array Int) : Prop := isSorted arr

def postcondition (arr : Array Int) (result : Int) : Prop := True
"""
        result = parse_specs_content(specs_content)

        assert "def isSorted" in result['helpers_and_requires']
        assert result['precond_params_list'] == [('arr', 'Array Int')]

    def test_missing_precondition(self):
        """Test error when precondition is missing."""
        specs_content = """
def postcondition (x : Nat) (result : Nat) : Prop := True
"""
        with pytest.raises(ValueError, match="Cannot find 'def precondition'"):
            parse_specs_content(specs_content)

    def test_missing_postcondition(self):
        """Test error when postcondition is missing."""
        specs_content = """
def precondition (x : Nat) : Prop := True
"""
        with pytest.raises(ValueError, match="Cannot find 'def postcondition'"):
            parse_specs_content(specs_content)

    def test_postcondition_must_have_more_params(self):
        """Test error when postcondition doesn't have more params than precondition."""
        specs_content = """
def precondition (x : Nat) (y : Nat) : Prop := True

def postcondition (x : Nat) : Prop := True
"""
        with pytest.raises(ValueError, match="postcondition must have more parameters"):
            parse_specs_content(specs_content)

    def test_multi_line_body(self):
        """Test parsing when definition body spans multiple lines."""
        specs_content = """
def precondition (x : Nat) (y : Nat) : Prop :=
  x > 0 ∧
  y > 0

def postcondition (x : Nat) (y : Nat) (result : Nat) : Prop :=
  result = x + y ∧
  result > x ∧
  result > y
"""
        result = parse_specs_content(specs_content)

        assert result['precond_params_list'] == [('x', 'Nat'), ('y', 'Nat')]
        assert result['postcond_params_list'] == [('x', 'Nat'), ('y', 'Nat'), ('result', 'Nat')]
        assert "x > 0" in result['precond_def']
        assert "result = x + y" in result['postcond_def']
