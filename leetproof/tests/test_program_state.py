"""Tests for ProgramBuffer and ProgramState."""

from utils.program_state import ProgramBuffer


def test_empty_lazy_reads_from_disk(tmp_path):
    """Empty lazy buffer should initialize on first read."""
    file_path = tmp_path / "sample.txt"
    file_path.write_text("hello")

    buffer = ProgramBuffer.empty(str(file_path))
    assert buffer.get_current() == "hello"

    state = buffer.to_dict()
    assert state["initialized"] is True


def test_empty_creates_missing_file(tmp_path):
    """Empty lazy buffer should create the file if missing."""
    file_path = tmp_path / "new" / "sample.txt"
    assert not file_path.exists()

    buffer = ProgramBuffer.empty(str(file_path))
    assert buffer.get_current() == ""
    assert file_path.exists()
    assert file_path.read_text() == ""


def test_from_content_stores_content(tmp_path):
    """from_content should store content directly."""
    file_path = tmp_path / "sample.txt"
    buffer = ProgramBuffer.from_content(str(file_path), "hello")

    assert buffer.get_current() == "hello"
    assert buffer.get_stable() is None


def test_from_content_stable(tmp_path):
    """from_content with stable=True should set both current and stable."""
    file_path = tmp_path / "sample.txt"
    buffer = ProgramBuffer.from_content(str(file_path), "hello", stable=True)

    assert buffer.get_current() == "hello"
    assert buffer.get_stable() == "hello"


def test_to_dict_roundtrip(tmp_path):
    """Round-trip through to_dict/from_dict should preserve content."""
    file_path = tmp_path / "sample.txt"
    buffer = ProgramBuffer.from_content(str(file_path), "hello")
    buffer.update_stable("stable_v1")

    restored = ProgramBuffer.from_dict(buffer.to_dict())
    assert restored.get_current() == "hello"
    assert restored.get_stable() == "stable_v1"


def test_get_stable_returns_none_when_unset(tmp_path):
    """Stable content should be None until promoted or updated."""
    file_path = tmp_path / "sample.txt"
    buffer = ProgramBuffer.from_content(str(file_path), "hello")

    assert buffer.get_stable() is None


def test_update_current(tmp_path):
    """update_current should update current content."""
    file_path = tmp_path / "sample.txt"
    buffer = ProgramBuffer.empty(str(file_path))

    buffer.update_current("hello")
    assert buffer.get_current() == "hello"


def test_promote_current(tmp_path):
    """promote_current should copy current to stable."""
    file_path = tmp_path / "sample.txt"
    buffer = ProgramBuffer.empty(str(file_path))

    buffer.update_current("hello")
    buffer.promote_current()
    assert buffer.get_stable() == "hello"


def test_update_stable(tmp_path):
    """update_stable should set stable without changing current."""
    file_path = tmp_path / "sample.txt"
    buffer = ProgramBuffer.from_content(str(file_path), "current_v1")

    buffer.update_stable("stable_v1")
    assert buffer.get_current() == "current_v1"
    assert buffer.get_stable() == "stable_v1"


def test_update_current_promote(tmp_path):
    """update_current should optionally promote current to stable."""
    file_path = tmp_path / "sample.txt"
    buffer = ProgramBuffer.empty(str(file_path))

    state = buffer.update_current("hello", promote_to_stable=True)
    assert state["current"] == "hello"
    assert state["stable"] == "hello"


def test_dict_shape(tmp_path):
    """Serialized dict should have the expected flat shape."""
    file_path = tmp_path / "sample.txt"
    buffer = ProgramBuffer.from_content(str(file_path), "hello", stable=True)
    state = buffer.to_dict()

    assert set(state.keys()) == {"path", "current", "stable", "initialized"}
    assert isinstance(state["current"], str)
    assert isinstance(state["stable"], str)
    assert state["current"] == "hello"
    assert state["stable"] == "hello"
    assert state["initialized"] is True


def test_from_dict_migration_shim(tmp_path):
    """from_dict should handle old-shaped dicts with snapshot sub-dicts."""
    old_state = {
        "path": str(tmp_path / "sample.txt"),
        "current": {"content": "hello", "source": "test", "revision": 0},
        "stable": {"content": "stable", "source": "test", "revision": 1},
        "checkpoints": {},
        "dirty": False,
        "initialized": True,
    }

    buffer = ProgramBuffer.from_dict(old_state)
    assert buffer.get_current() == "hello"
    assert buffer.get_stable() == "stable"


def test_sync_from_disk(tmp_path):
    """sync_from_disk should re-read file content into current."""
    file_path = tmp_path / "sample.txt"
    file_path.write_text("original")

    buffer = ProgramBuffer.from_content(str(file_path), "original")

    # Simulate external write (e.g., LLM tool)
    file_path.write_text("modified externally")

    state = buffer.sync_from_disk()
    assert state["current"] == "modified externally"
    assert buffer.get_current() == "modified externally"


def test_get_stable_assert_exists(tmp_path):
    """get_stable with assert_exists=True should raise when missing."""
    file_path = tmp_path / "sample.txt"
    buffer = ProgramBuffer.from_content(str(file_path), "hello")

    import pytest
    with pytest.raises(ValueError, match="Stable program content is required"):
        buffer.get_stable(assert_exists=True)


def test_get_stable_assert_exists_passes(tmp_path):
    """get_stable with assert_exists=True should return content when present."""
    file_path = tmp_path / "sample.txt"
    buffer = ProgramBuffer.from_content(str(file_path), "hello", stable=True)

    assert buffer.get_stable(assert_exists=True) == "hello"

