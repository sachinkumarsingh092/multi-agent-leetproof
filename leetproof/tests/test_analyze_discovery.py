"""Tests for find_and_group_files auto-discovery across all naming conventions."""

import pytest
from pathlib import Path
from unittest.mock import patch


@pytest.fixture
def tmp_dir(tmp_path):
    """Return a fresh temp directory."""
    return tmp_path


def _touch(base: Path, *parts: str) -> Path:
    """Create an empty file, making parent dirs as needed."""
    p = base.joinpath(*parts)
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text("")
    return p


class TestFindAndGroupFiles:
    """Test find_and_group_files with different naming conventions."""

    def test_flat_pascal_spec(self, tmp_dir):
        """Flat PascalCase: VerinaAdvanced9Spec.lean → spec for num 9."""
        _touch(tmp_dir, "VerinaAdvanced9Spec.lean")
        from scripts.analyze import find_and_group_files
        result = find_and_group_files(tmp_dir)
        assert 9 in result.groups
        assert result.groups[9].spec == "VerinaAdvanced9Spec.lean"

    def test_flat_pascal_with_impl(self, tmp_dir):
        """Flat PascalCase: finds Impl.lean via derive_from_spec."""
        _touch(tmp_dir, "VerinaBasic3Spec.lean")
        _touch(tmp_dir, "VerinaBasic3Impl.lean")
        from scripts.analyze import find_and_group_files
        result = find_and_group_files(tmp_dir)
        g = result.groups[3]
        assert g.spec == "VerinaBasic3Spec.lean"
        assert g.impl == "VerinaBasic3Impl.lean"

    def test_flat_pascal_example_verify(self, tmp_dir):
        """Flat PascalCase: finds Spec_example_verify via derive_from_spec."""
        _touch(tmp_dir, "Foo9Spec.lean")
        _touch(tmp_dir, "Foo9SpecExampleVerify.lean")
        from scripts.analyze import find_and_group_files
        result = find_and_group_files(tmp_dir)
        g = result.groups[9]
        assert g.spec_example_verify == "Foo9SpecExampleVerify.lean"

    def test_flat_snake(self, tmp_dir):
        """Flat snake_case: verina_basic_9_spec.lean → spec for num 9."""
        _touch(tmp_dir, "verina_basic_9_spec.lean")
        from scripts.analyze import find_and_group_files
        result = find_and_group_files(tmp_dir)
        assert 9 in result.groups
        assert result.groups[9].spec == "verina_basic_9_spec.lean"

    def test_flat_snake_with_impl(self, tmp_dir):
        """Flat snake_case: derives impl path."""
        _touch(tmp_dir, "verina_basic_1_spec.lean")
        _touch(tmp_dir, "verina_basic_1_impl.lean")
        from scripts.analyze import find_and_group_files
        result = find_and_group_files(tmp_dir)
        g = result.groups[1]
        assert g.spec == "verina_basic_1_spec.lean"
        assert g.impl == "verina_basic_1_impl.lean"

    def test_flat_snake_example_verify(self, tmp_dir):
        """Flat snake_case: derives example_verify path."""
        _touch(tmp_dir, "verina_basic_5_spec.lean")
        _touch(tmp_dir, "verina_basic_5_spec_example_verify.lean")
        from scripts.analyze import find_and_group_files
        result = find_and_group_files(tmp_dir)
        assert result.groups[5].spec_example_verify == "verina_basic_5_spec_example_verify.lean"

    def test_directory_based(self, tmp_dir):
        """Directory-based: VerinaBasic9/Spec.lean → spec for num 9."""
        _touch(tmp_dir, "VerinaBasic9", "Spec.lean")
        from scripts.analyze import find_and_group_files
        result = find_and_group_files(tmp_dir)
        assert 9 in result.groups
        assert result.groups[9].spec == "VerinaBasic9/Spec.lean"

    def test_directory_based_with_impl(self, tmp_dir):
        """Directory-based: derives Impl.lean inside the directory."""
        _touch(tmp_dir, "VerinaBasic9", "Spec.lean")
        _touch(tmp_dir, "VerinaBasic9", "Impl.lean")
        from scripts.analyze import find_and_group_files
        result = find_and_group_files(tmp_dir)
        g = result.groups[9]
        assert g.spec == "VerinaBasic9/Spec.lean"
        assert g.impl == "VerinaBasic9/Impl.lean"

    def test_directory_based_full(self, tmp_dir):
        """Directory-based: all derived files found."""
        _touch(tmp_dir, "Prob42", "Spec.lean")
        _touch(tmp_dir, "Prob42", "Impl.lean")
        _touch(tmp_dir, "Prob42", "SpecExampleVerify.lean")
        _touch(tmp_dir, "Prob42", "Impl.dfy")
        from scripts.analyze import find_and_group_files
        result = find_and_group_files(tmp_dir)
        g = result.groups[42]
        assert g.spec == "Prob42/Spec.lean"
        assert g.impl == "Prob42/Impl.lean"
        assert g.spec_example_verify == "Prob42/SpecExampleVerify.lean"
        assert g.dafny_impl == "Prob42/Impl.dfy"

    def test_dafny_flat_pascal(self, tmp_dir):
        """Flat PascalCase: finds Dafny impl via derive_from_spec."""
        _touch(tmp_dir, "Foo7Spec.lean")
        _touch(tmp_dir, "Foo7Impl.dfy")
        from scripts.analyze import find_and_group_files
        result = find_and_group_files(tmp_dir)
        assert result.groups[7].dafny_impl == "Foo7Impl.dfy"

    def test_dafny_flat_snake(self, tmp_dir):
        """Flat snake_case: finds Dafny impl via derive_from_spec."""
        _touch(tmp_dir, "foo_7_spec.lean")
        _touch(tmp_dir, "foo_7_impl.dfy")
        from scripts.analyze import find_and_group_files
        result = find_and_group_files(tmp_dir)
        assert result.groups[7].dafny_impl == "foo_7_impl.dfy"

    def test_multiple_problems(self, tmp_dir):
        """Multiple problems discovered in one directory."""
        _touch(tmp_dir, "VerinaBasic1Spec.lean")
        _touch(tmp_dir, "VerinaBasic2Spec.lean")
        _touch(tmp_dir, "VerinaBasic3Spec.lean")
        from scripts.analyze import find_and_group_files
        result = find_and_group_files(tmp_dir)
        assert set(result.groups.keys()) == {1, 2, 3}

    def test_missing_impl_not_set(self, tmp_dir):
        """If impl file doesn't exist, attr stays None."""
        _touch(tmp_dir, "VerinaBasic5Spec.lean")
        from scripts.analyze import find_and_group_files
        result = find_and_group_files(tmp_dir)
        assert result.groups[5].impl is None

    def test_nested_subdirectory(self, tmp_dir):
        """Files in a subdirectory are still found via rglob."""
        _touch(tmp_dir, "sub", "verina_basic_1_spec.lean")
        _touch(tmp_dir, "sub", "verina_basic_1_impl.lean")
        from scripts.analyze import find_and_group_files
        result = find_and_group_files(tmp_dir)
        assert 1 in result.groups
        assert result.groups[1].spec == "sub/verina_basic_1_spec.lean"
        assert result.groups[1].impl == "sub/verina_basic_1_impl.lean"


class TestDeriveFromSpec:
    """Verify derive_from_spec works correctly for all conventions."""

    def test_pascal_dir_spec_to_impl(self):
        from utils.naming import derive_from_spec, OutputTarget
        assert derive_from_spec("A/B/Spec.lean", OutputTarget.IMPL) == "A/B/Impl.lean"

    def test_pascal_dir_spec_to_example_verify(self):
        from utils.naming import derive_from_spec, OutputTarget
        assert derive_from_spec("A/B/Spec.lean", OutputTarget.EXAMPLE_VERIFY) == "A/B/SpecExampleVerify.lean"

    def test_pascal_flat_spec_to_impl(self):
        from utils.naming import derive_from_spec, OutputTarget
        assert derive_from_spec("Foo9Spec.lean", OutputTarget.IMPL) == "Foo9Impl.lean"

    def test_snake_spec_to_impl(self):
        from utils.naming import derive_from_spec, OutputTarget
        assert derive_from_spec("foo_9_spec.lean", OutputTarget.IMPL) == "foo_9_impl.lean"

    def test_snake_spec_to_dafny(self):
        from utils.naming import derive_from_spec, OutputTarget
        assert derive_from_spec("foo_9_spec.lean", OutputTarget.DAFNY_IMPL) == "foo_9_impl.dfy"
