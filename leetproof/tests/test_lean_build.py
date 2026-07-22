from tools import lean_build
from utils.lean.build import parse_lake_build_output


def test_failed_build_preserves_unparsed_lake_output(monkeypatch):
    commands = []

    class FakeProcess:
        returncode = 1

        def communicate(self, timeout):
            return "", "error: unknown package `artifacts`\n"

    def fake_popen(command, **_kwargs):
        commands.append(command)
        return FakeProcess()

    monkeypatch.setattr(lean_build.subprocess, "Popen", fake_popen)

    result = lean_build.lean_build_file_helper("artifacts/Candidate.lean")

    assert not result.typechecks
    assert result.diagnostics == []
    assert "unknown package `artifacts`" in result.build_log
    assert commands == [
        ["lake", "env", "lean", "artifacts/Candidate.lean"]
    ]


def test_parse_direct_lean_multiline_unsolved_goals():
    file_path = "/workspace/artifacts/Candidate.lean"
    output = f"""{file_path}:163:29: error: unsolved goals
case invariant_preserved
x : Nat
⊢ x ≤ x
{file_path}:156:0: warning: postcondition test skipped
"""

    diagnostics = parse_lake_build_output(
        output,
        file_path,
        truncate_messages=False,
    )

    assert diagnostics == [
        {
            "severity": "error",
            "message": "unsolved goals\ncase invariant_preserved\nx : Nat\n⊢ x ≤ x",
            "line": 163,
            "column": 29,
        },
        {
            "severity": "warning",
            "message": "postcondition test skipped",
            "line": 156,
            "column": 0,
        },
    ]


def test_parse_keeps_existing_lake_diagnostic_format():
    file_path = "artifacts/Candidate.lean"

    diagnostics = parse_lake_build_output(
        f"error: {file_path}:5:2: existing format\n",
        file_path,
    )

    assert diagnostics == [
        {
            "severity": "error",
            "message": "existing format",
            "line": 5,
            "column": 2,
        }
    ]
