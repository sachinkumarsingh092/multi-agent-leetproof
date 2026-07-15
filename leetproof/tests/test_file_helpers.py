"""Tests for file_helpers module."""

import json
import pytest
from utils.file_helpers import StringPosition, find_string_position


class TestStringPosition:
    """Tests for StringPosition dataclass."""

    def test_to_dict_and_json(self):
        """Test converting StringPosition to dict and JSON."""
        pos = StringPosition(start_line=1, start_col=5, end_line=1, end_col=10)
        assert pos.to_dict() == {
            "start_line": 1,
            "start_col": 5,
            "end_line": 1,
            "end_col": 10
        }
        parsed = json.loads(pos.to_json())
        assert parsed == pos.to_dict()


class TestFindStringPosition:
    """Tests for find_string_position function."""

    def test_basic_search_with_indexing(self):
        """Test basic string search with both indexing modes."""
        content = "hello world"

        # Zero-indexed
        result = find_string_position(content, "world", zero_indexed=True)
        assert result is not None
        assert result.start_line == 0 and result.start_col == 6
        assert result.end_line == 0 and result.end_col == 11

        # One-indexed
        result = find_string_position(content, "world", zero_indexed=False)
        assert result is not None
        assert result.start_line == 1 and result.start_col == 7
        assert result.end_line == 1 and result.end_col == 12

    def test_multiline_search_string(self):
        """Test that multiline search strings are not supported (searches line-by-line)."""
        content = "first line\nsecond line\nthird line"
        # The function searches line-by-line, so multiline strings won't be found
        result = find_string_position(content, "first line\nsecond", zero_indexed=True)
        assert result is None

        # But single-line searches work fine
        result = find_string_position(content, "first line", zero_indexed=True)
        assert result is not None
        assert result.start_line == 0 and result.start_col == 0
        assert result.end_line == 0 and result.end_col == 10

    def test_multiple_occurrences(self):
        """Test finding specific occurrences when string appears multiple times."""
        content = "hello\nhello\nhello"

        # First occurrence
        result = find_string_position(content, "hello", occurrence=1, zero_indexed=True)
        assert result is not None
        assert result.start_line == 0

        # Second occurrence
        result = find_string_position(content, "hello", occurrence=2, zero_indexed=True)
        assert result is not None
        assert result.start_line == 1

        # Non-existent occurrence
        result = find_string_position(content, "hello", occurrence=10)
        assert result is None

        def test_edge_cases(self):
            """Test edge cases: not found, invalid occurrence, empty strings."""
            content = "hello world"

            # String not found
            assert find_string_position(content, "goodbye") is None

            # Invalid occurrence numbers
            assert find_string_position(content, "hello", occurrence=0) is None
            assert find_string_position(content, "hello", occurrence=-1) is None

            # Empty content
            assert find_string_position("", "hello") is None

            # Empty search string (should find something)
            result = find_string_position(content, "")
            assert result is not None
            assert result.end_col == result.start_col

        def test_complex_code_search(self):
            """Test searching in realistic code with indentation and special chars."""
            content = """def foo():
    bar = 1
    return bar"""

            result = find_string_position(content, "    bar = 1", zero_indexed=True)
            assert result is not None
            assert result.start_line == 1 and result.start_col == 0
            assert result.end_col == 11

            result = find_string_position(content, "def foo():", zero_indexed=True)
            assert result is not None
            assert result.start_line == 0 and result.end_col == 10
