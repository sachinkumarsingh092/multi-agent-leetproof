"""Tests for the Differ utility."""

import pytest
from utils.differ import Differ, DiffHunk


class TestDiffer:
    """Tests for Differ class."""

    def test_identical_content(self):
        """Test that identical content produces empty diff."""
        d = Differ("A", "hello\nworld", "B", "hello\nworld")
        assert d.is_empty()
        assert d.diff() == []

    def test_single_line_change(self):
        """Test diff with single line changed."""
        d = Differ("ref", "line1\nline2\nline3", "out", "line1\nchanged\nline3")

        assert not d.is_empty()
        hunks = d.diff()
        assert len(hunks) == 2

        assert hunks[0].source == "ref"
        assert hunks[0].content == "line2"

        assert hunks[1].source == "out"
        assert hunks[1].content == "changed"

    def test_line_added(self):
        """Test diff with line added in right."""
        d = Differ("A", "line1\nline2\n", "B", "line1\nline2\nline3\n")

        hunks = d.diff()
        assert len(hunks) == 1
        assert hunks[0].source == "B"
        assert hunks[0].content == "line3"

    def test_line_removed(self):
        """Test diff with line removed from right."""
        d = Differ("A", "line1\nline2\nline3", "B", "line1\nline3")

        hunks = d.diff()
        assert len(hunks) == 1
        assert hunks[0].source == "A"
        assert hunks[0].content == "line2"

    def test_only_in_left(self):
        """Test only_in_left returns correct hunks."""
        d = Differ("left", "a\nb\nc", "right", "a\nx\nc")

        left_hunks = d.only_in_left()
        assert len(left_hunks) == 1
        assert left_hunks[0].source == "left"
        assert left_hunks[0].content == "b"

    def test_only_in_right(self):
        """Test only_in_right returns correct hunks."""
        d = Differ("left", "a\nb\nc", "right", "a\nx\nc")

        right_hunks = d.only_in_right()
        assert len(right_hunks) == 1
        assert right_hunks[0].source == "right"
        assert right_hunks[0].content == "x"

    def test_format_unified(self):
        """Test unified diff format output."""
        d = Differ("file_a", "line1\nold\nline3", "file_b", "line1\nnew\nline3")

        formatted = d.format()
        assert "--- file_a" in formatted
        assert "+++ file_b" in formatted
        assert "-old" in formatted
        assert "+new" in formatted

    def test_empty_content(self):
        """Test diff with empty content."""
        d = Differ("A", "", "B", "")
        assert d.is_empty()

    def test_one_empty(self):
        """Test diff where one side is empty."""
        d = Differ("A", "content", "B", "")

        assert not d.is_empty()
        hunks = d.diff()
        assert len(hunks) == 1
        assert hunks[0].source == "A"

    def test_multiline_hunk(self):
        """Test diff with multiple consecutive lines changed."""
        d = Differ("A", "a\nb\nc\nd", "B", "a\nx\ny\nd")

        hunks = d.diff()
        # Should have 2 hunks: one for A (b\nc), one for B (x\ny)
        assert len(hunks) == 2
        assert "b" in hunks[0].content
        assert "c" in hunks[0].content
        assert "x" in hunks[1].content
        assert "y" in hunks[1].content

    def test_line_numbers(self):
        """Test that line numbers are correct."""
        d = Differ("A", "a\nb\nc", "B", "a\nX\nc")

        hunks = d.diff()
        # Changed line is line 2
        assert hunks[0].line_start == 2
        assert hunks[0].line_end == 2
