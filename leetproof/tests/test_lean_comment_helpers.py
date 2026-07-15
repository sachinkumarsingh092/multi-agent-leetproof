"""Tests for Lean comment/uncomment helper functions."""

import pytest
from utils.lean_helpers import uncomment_lines_matching, comment_lines_matching


class TestUncommentLinesMatching:
    """Tests for uncomment_lines_matching function."""

    def test_uncomment_matching_lines(self):
        """Test uncommenting lines that match the pattern."""
        content = """-- theorem example : True := trivial
other line
-- theorem another : True := trivial"""

        result, modified = uncomment_lines_matching(content, r'^theorem')
        assert modified is True
        assert "theorem example : True := trivial" in result
        assert "theorem another : True := trivial" in result
        assert "-- theorem" not in result

    def test_preserve_indentation(self):
        """Test that indentation is preserved when uncommenting."""
        content = """  -- theorem example : True := trivial
     -- lemma test : True := trivial"""

        result, modified = uncomment_lines_matching(content, r'^theorem')
        assert "  theorem example : True := trivial" in result
        assert "    -- lemma test : True := trivial" in result  # Should remain commented

    def test_no_matches(self):
        """Test when no lines match the pattern."""
        content = """-- some comment
-- another comment"""

        result, modified = uncomment_lines_matching(content, r'^theorem')
        assert modified is False
        assert result == content

    def test_partial_pattern_matching(self):
        """Test that pattern matches correctly against uncommented content."""
        content = """-- theorem_test : True
-- test_theorem : True
-- theorem : True"""

        # Only lines starting with 'theorem' (after uncomment) should match
        result, modified = uncomment_lines_matching(content, r'^theorem\s*:')
        assert modified is True
        assert "theorem : True" in result
        assert "-- theorem_test : True" in result  # Should remain commented
        assert "-- test_theorem : True" in result  # Should remain commented

    def test_mixed_content(self):
        """Test with mix of commented and uncommented lines."""
        content = """theorem active : True := trivial
-- theorem inactive : True := trivial
other code"""

        result, modified = uncomment_lines_matching(content, r'^theorem')
        lines = result.split('\n')
        assert lines[0] == "theorem active : True := trivial"  # Already uncommented
        # Notice that this preserves the space after the -- comment as well
        assert lines[1] == " theorem inactive : True := trivial"  # Now uncommented
        assert lines[2] == "other code"


class TestCommentLinesMatching:
    """Tests for comment_lines_matching function."""

    def test_comment_matching_lines(self):
        """Test commenting lines that match the pattern."""
        content = """theorem example : True := trivial
lemma test : True := trivial
other line"""

        result, modified = comment_lines_matching(content, r'^theorem')
        assert modified is True
        assert "-- theorem example : True := trivial" in result
        assert "lemma test : True := trivial" in result  # Should not be commented
        assert "other line" in result  # Should not be commented

    def test_preserve_indentation_when_commenting(self):
        """Test that indentation is preserved when commenting."""
        content = """  theorem example : True := trivial
     lemma test : True := trivial"""

        result, modified = comment_lines_matching(content, r'^theorem')
        assert "  -- theorem example : True := trivial" in result
        assert "    lemma test : True := trivial" in result

    def test_already_commented_lines(self):
        """Test that already commented lines are not double-commented."""
        content = """-- theorem example : True := trivial
theorem another : True := trivial"""

        result, modified = comment_lines_matching(content, r'^theorem')
        lines = result.split('\n')
        assert lines[0] == "-- theorem example : True := trivial"  # Should stay as is
        assert lines[1] == "-- theorem another : True := trivial"  # Now commented

    def test_no_matches_when_commenting(self):
        """Test when no lines match the pattern for commenting."""
        content = """lemma example : True := trivial
other line"""

        result, modified = comment_lines_matching(content, r'^theorem')
        assert modified is False
        assert result == content

    def test_complex_pattern(self):
        """Test with more complex regex patterns."""
        content = """theorem foo : True := trivial
theorem bar : False := sorry
lemma baz : True := trivial
def something := 42"""

        # Comment all theorem and lemma declarations
        result, modified = comment_lines_matching(content, r'^(theorem|lemma)')
        assert "-- theorem foo : True := trivial" in result
        assert "-- theorem bar : False := sorry" in result
        assert "-- lemma baz : True := trivial" in result
        assert "def something := 42" in result  # Should not be commented


class TestRoundTrip:
    """Tests for round-trip operations (comment then uncomment and vice versa)."""

    def test_uncomment_then_comment_roundtrip(self):
        """Test uncommenting then commenting returns to near-original state."""
        original = """-- theorem example : True := trivial
other line"""

        # Uncomment
        uncommented, _ = uncomment_lines_matching(original, r'^theorem')
        assert "theorem example : True := trivial" in uncommented

        # Comment back
        recommented, _ = comment_lines_matching(uncommented, r'^theorem')
        assert "-- theorem example : True := trivial" in recommented

    def test_comment_then_uncomment_roundtrip(self):
        """Test commenting then uncommenting returns to original state."""
        original = """theorem example : True := trivial
other line"""

        # Comment
        commented, _ = comment_lines_matching(original, r'^theorem')
        assert "-- theorem example : True := trivial" in commented

        # Uncomment back
        uncommented, _ = uncomment_lines_matching(commented, r'^theorem', False)
        assert uncommented == original
