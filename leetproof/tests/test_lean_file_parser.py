"""Tests for LeanFile parsing, section management, and round-trip preservation."""

import pytest
from utils.lean.parser import parse_lean_file_sections, LeanFile


def _verify_roundtrip(content: str):
    """Helper to verify parse -> reconstruct -> parse yields same result."""
    result1 = parse_lean_file_sections(content)
    reconstructed = result1.reconstruct()
    result2 = parse_lean_file_sections(reconstructed)

    assert result1.prologue.strip() == result2.prologue.strip()
    assert len(result1.sections) == len(result2.sections)
    for s1, s2 in zip(result1.sections, result2.sections):
        assert s1.name == s2.name
        assert s1.content.strip() == s2.content.strip()


def _verify_exact_roundtrip(content: str):
    """Verify that reconstruct output is stable (idempotent)."""
    result1 = parse_lean_file_sections(content)
    reconstructed1 = result1.reconstruct()
    result2 = parse_lean_file_sections(reconstructed1)
    reconstructed2 = result2.reconstruct()

    assert reconstructed1 == reconstructed2, (
        f"Reconstruct is not idempotent.\n"
        f"First reconstruct:\n{reconstructed1!r}\n"
        f"Second reconstruct:\n{reconstructed2!r}"
    )


class TestParseLeanFileSections:
    """Tests for basic parsing of LeanFile sections."""

    def test_parsing_basic_structures(self):
        """Test parsing files with various structures: prologue, sections, comments, empty sections."""
        # Basic file with prologue and sections
        content1 = """import Mathlib.Data.Nat.Basic
set_option maxRecDepth 1000

section Foo
theorem foo : 1 = 1 := rfl
end Foo

section Bar
def bar := 42
end Bar
"""
        result = parse_lean_file_sections(content1)
        assert "import Mathlib.Data.Nat.Basic" in result.prologue
        assert "set_option maxRecDepth 1000" in result.prologue
        assert len(result.sections) == 2
        assert result.sections[0].name == "Foo"
        assert result.sections[1].name == "Bar"
        _verify_roundtrip(content1)

        # File starting directly with section (no prologue)
        content2 = """section Main
def main := 1
end Main
"""
        result = parse_lean_file_sections(content2)
        assert result.prologue == ""
        assert len(result.sections) == 1
        assert result.sections[0].name == "Main"
        _verify_roundtrip(content2)

        # File with no sections (all prologue)
        content3 = """import Foo
def bar := 1
theorem baz : True := trivial
"""
        result = parse_lean_file_sections(content3)
        assert "import Foo" in result.prologue
        assert "def bar := 1" in result.prologue
        assert len(result.sections) == 0
        _verify_roundtrip(content3)

        # File with whitespace and comments between sections
        content4 = """import Foo

section A
def a := 1
end A


-- Multiple blank lines and comments


section B
def b := 2
end B
-- Trailing comment
section C
def c := 3
end C
"""
        result = parse_lean_file_sections(content4)
        assert result.section_names() == ["A", "B", "C"]
        assert "-- Multiple blank lines and comments" in result.reconstruct()
        _verify_roundtrip(content4)

    def test_section_queries_and_mutations(self):
        """Test get_section, has_section, section_names, and basic mutations."""
        content = """section Foo
foo content
end Foo

section Bar
bar content
end Bar

section Baz
baz content
end Baz
"""
        result = parse_lean_file_sections(content)

        # Query operations
        assert result.get_section("Foo") is not None
        assert result.get_section("Missing") is None
        assert result.has_section("Bar") is True
        assert result.has_section("Missing") is False
        assert result.section_names() == ["Foo", "Bar", "Baz"]

        # Mutations
        lf = LeanFile.from_content(content)
        assert lf.remove_section("Bar") is True
        assert not lf.has_section("Bar")
        assert lf.section_names() == ["Foo", "Baz"]

        assert lf.clear_section("Foo") is True
        assert lf.get_section("Foo", assert_exists=True).content == ""

        lf.add_or_replace_section("New", "new content")
        assert lf.section_names() == ["Foo", "Baz", "New"]
        assert lf.get_section("New", assert_exists=True).content == "new content"

        lf.add_or_replace_section("Foo", "modified foo")
        assert lf.get_section("Foo", assert_exists=True).content == "modified foo"

        lf.append_in_section("Baz", "appended", assert_section_present=True)
        assert "baz content" in lf.get_section("Baz", assert_exists=True).content
        assert "appended" in lf.get_section("Baz", assert_exists=True).content

    def test_comment_out_section(self):
        """Test commenting out section content."""
        content = """section A
theorem foo : True := trivial
def bar := 42
end A
"""
        lf = LeanFile.from_content(content)
        result = lf.comment_out_section("A", reason="Disabled for testing")

        assert result is True
        section_content = lf.get_section("A", assert_exists=True).content
        assert "-- Disabled for testing" in section_content
        assert "-- theorem foo" in section_content
        assert "-- def bar" in section_content
        
        # Test with non-existent section
        lf2 = LeanFile.from_content(content)
        result = lf2.comment_out_section("NonExistent")
        assert result is False

    def test_line_numbers_and_content_spans(self):
        """Test line number tracking and content span queries."""
        content = """import A
import B

section First
line1
line2
end First
-- trailing
section Second
single line
end Second

section Third
a
b
c
d
end Third
"""
        lf = LeanFile.from_content(content)

        # First section
        first = lf.get_section("First", assert_exists=True)
        assert first.start_line == 4
        assert first.content_start_line == 5
        assert first.end_line == 7
        assert first.is_line_in_content(5)
        assert first.is_line_in_content(6)
        assert not first.is_line_in_content(4)  # section line
        assert not first.is_line_in_content(7)  # end line

        # Second section
        second = lf.get_section("Second", assert_exists=True)
        assert second.start_line == 9
        assert second.content_start_line == 10
        assert second.end_line == 11

        # Third section
        third = lf.get_section("Third", assert_exists=True)
        assert third.start_line == 13
        assert third.end_line == 18
        start, end = third.content_line_span()
        assert start == 14
        assert end == 17

    def test_error_conditions(self):
        """Test error handling: stray code, unclosed sections, missing sections."""
        # Stray code between sections raises error
        with pytest.raises(ValueError, match="Unexpected content outside section"):
            parse_lean_file_sections("""section A
a
end A
def stray := 1
section B
b
end B
""")

        # Unclosed section raises error
        with pytest.raises(ValueError, match="no matching 'end"):
            parse_lean_file_sections("""section Unclosed
some content
""")

        # Appending to missing section raises error
        lf = LeanFile.from_content("section A\na\nend A\n")
        with pytest.raises(ValueError, match="Section NonExistent not found"):
            lf.append_in_section("NonExistent", "content", assert_section_present=True)


class TestRoundTripPreservation:
    """Comprehensive tests for exact round-trip preservation across multiple cycles."""

    def test_exact_roundtrip_simple_cases(self):
        """Test exact reconstruction for simple structures."""
        cases = [
            # No prologue
            """section Utils
def add (x y : Nat) : Nat := x + y

def mul (x y : Nat) : Nat := x * y
end Utils
""",
            # Multiple sections no prologue
            """section Defs
def f : Nat := 1
def g : Nat := 2
end Defs

section Lemmas
lemma simple : 1 = 1 := rfl
end Lemmas

section Theorems
theorem main : True := trivial
end Theorems
""",
            # With prologue
            """import Foo

section Main
theorem t1 : True := trivial
theorem t2 : True := trivial
end Main

section Aux
def helper := 42
end Aux
""",
        ]

        for content in cases:
            lf1 = LeanFile.from_content(content)
            recon1 = lf1.reconstruct()
            assert content == recon1, f"First round-trip failed for:\n{content}"
            
            lf2 = LeanFile.from_content(recon1)
            recon2 = lf2.reconstruct()
            assert recon1 == recon2, f"Second round-trip not idempotent"

    def test_roundtrip_with_complex_content(self):
        """Test round-trip with indentation, blank lines, and special characters."""
        content = """import Mathlib.Data.Nat.Basic

section Proofs
theorem add_assoc (a b c : Nat) : (a + b) + c = a + (b + c) := by
  induction c with
  | zero =>
    simp
  | succ c ih =>
    rw [Nat.add_succ, Nat.add_succ, ih]

lemma helper (x y : Nat) : x + y = y + x := by
  induction x with
  | zero =>
    simp [Nat.add_comm]
  | succ x ih =>
    rw [Nat.succ_add, Nat.add_succ, ih]
end Proofs
"""
        lf1 = LeanFile.from_content(content)
        recon1 = lf1.reconstruct()
        assert content == recon1, "Complex indented code should be preserved"
        
        lf2 = LeanFile.from_content(recon1)
        recon2 = lf2.reconstruct()
        assert recon1 == recon2, "Should be stable after second reconstruction"

    def test_roundtrip_with_internal_blank_lines(self):
        """Test that blank lines within section content are preserved."""
        content = """section Work
def foo : Nat := 1


def bar : Nat := 2
end Work
"""
        lf1 = LeanFile.from_content(content)
        section = lf1.get_section("Work", assert_exists=True)
        assert "\n\n" in section.content, "Blank lines should be in content"
        
        recon1 = lf1.reconstruct()
        assert content == recon1, "Blank lines within content should be preserved"
        
        lf2 = LeanFile.from_content(recon1)
        recon2 = lf2.reconstruct()
        assert recon1 == recon2

    def test_roundtrip_with_comments_and_unicode(self):
        """Test preservation of comments between sections and Unicode characters."""
        content = """section A
def a := 1
end A
-- This is a comment about section B
-- Another line of comment
section B
def test : ℕ → ℕ := fun n => n

theorem sym : ∀ x : ℕ, x ≤ x := by rfl
end B
"""
        lf1 = LeanFile.from_content(content)
        recon1 = lf1.reconstruct()
        assert content == recon1, "Comments and Unicode should be preserved"
        
        lf2 = LeanFile.from_content(recon1)
        recon2 = lf2.reconstruct()
        assert recon1 == recon2

    def test_roundtrip_with_mutations(self):
        """Test that mutations followed by reconstruction remain stable."""
        content = """import Base

section Original1
orig1
end Original1

section ToRemove
remove me
end ToRemove

section Original2
orig2
end Original2
"""
        lf = LeanFile.from_content(content)
        
        # Mutations
        lf.remove_section("ToRemove")
        lf.add_or_replace_section("NewSection", "new content", after="Original1")
        lf.append_in_section("Original2", "appended", assert_section_present=True)
        lf.add_or_replace_section("Original1", "modified")
        
        recon1 = lf.reconstruct()
        lf2 = LeanFile.from_content(recon1)
        recon2 = lf2.reconstruct()
        assert recon1 == recon2, "After mutations, reconstruction should be stable"

    def test_multiple_consecutive_roundtrips(self):
        """Test 3+ consecutive roundtrips to verify stability."""
        content = """import Mathlib

section First
def f : Nat := 1
end First

section Second
def g : Nat := 2
end Second
"""
        lf1 = LeanFile.from_content(content)
        recon1 = lf1.reconstruct()
        assert content == recon1

        for i in range(2, 5):
            lf_next = LeanFile.from_content(recon1)
            recon_next = lf_next.reconstruct()
            assert recon1 == recon_next, f"Round-trip {i} should be idempotent"
            recon1 = recon_next


class TestEdgeCases:
    """Tests for edge cases and special structures."""

    def test_empty_and_whitespace_files(self):
        """Test empty files, whitespace-only files, and empty sections."""
        # Empty file
        lf = LeanFile.from_content("")
        assert lf.prologue == ""
        assert len(lf.sections) == 0
        assert lf.reconstruct() == ""

        # Only whitespace
        lf = LeanFile.from_content("   \n\n   \n")
        assert len(lf.sections) == 0

        # Empty section
        content = """section Empty
end Empty
"""
        _verify_exact_roundtrip(content)

        # Sections with only whitespace
        content = """section Whitespace


end Whitespace
"""
        _verify_exact_roundtrip(content)

    def test_special_section_names(self):
        """Test sections with underscores, numbers, and special naming."""
        content = """section My_Section_Name
content
end My_Section_Name

section Section123
content
end Section123

section Foo
foo content
end Foo

section FooBar
foobar content
end FooBar

section Foo2
foo2 content
end Foo2
"""
        lf = LeanFile.from_content(content)
        assert lf.has_section("My_Section_Name")
        assert lf.has_section("Section123")
        assert set(lf.section_names()) == {"Foo", "FooBar", "Foo2", "My_Section_Name", "Section123"}
        _verify_exact_roundtrip(content)

    def test_complex_realistic_files(self):
        """Test realistic Lean files with multiple sections and various content."""
        content = """import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Omega

set_option maxHeartbeats 400000
set_option pp.all false

section Definitions
def double (n : Nat) : Nat := n + n

def triple (n : Nat) : Nat := n + n + n
end Definitions

section Properties
theorem double_comm (n m : Nat) : double (n + m) = double n + double m := by
  unfold double
  omega

lemma triple_eq (n : Nat) : triple n = 3 * n := by
  unfold triple
  omega
end Properties
"""
        _verify_exact_roundtrip(content)

    def test_section_with_multiline_content(self):
        """Test sections with multi-line theorems, proofs, and nested content."""
        content = """section Complex
theorem complex_theorem
    (h1 : a = b)
    (h2 : b = c)
    : a = c := by
  rw [h1, h2]

theorem another : True := by
  have h : True := by trivial
  exact h

section WithComments
-- This is a comment
/- This is a
   multiline comment -/
theorem foo : True := trivial
end WithComments
end Complex
"""
        lf = LeanFile.from_content(content)
        section = lf.get_section("Complex", assert_exists=True)
        assert "theorem complex_theorem" in section.content
        assert "(h1 : a = b)" in section.content
        _verify_exact_roundtrip(content)

    def test_nested_same_name_sections_do_not_close_outer_section_early(self):
        """Top-level sections should tolerate nested section/namespace blocks in content."""
        content = """section Proof
lemma outer : True := by
  trivial

section Proof
lemma inner : True := by
  trivial
end Proof

namespace Hidden
lemma inside_ns : True := by
  trivial
end Hidden

theorem tail : True := by
  trivial
end Proof
"""
        lf = LeanFile.from_content(content)
        section = lf.get_section("Proof", assert_exists=True)
        assert "lemma inner : True := by" in section.content
        assert "namespace Hidden" in section.content
        assert "theorem tail : True := by" in section.content
        _verify_exact_roundtrip(content)
