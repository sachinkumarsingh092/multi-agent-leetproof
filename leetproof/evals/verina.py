#!/usr/bin/env python3
"""
VERINA benchmark loader - sets up repo and gets problems.
Auto-clones VERINA if needed, then fetches benchmark problems.

Usage:
    python3 scripts/verina.py basic 1
    python3 scripts/verina.py advanced 25 --components description code
"""

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional


VERINA_REPO_URL = "https://github.com/sunblaze-ucb/verina.git"


def ensure_verina_repo() -> Path:
    """Ensure VERINA repo exists locally, clone if missing.

    Clones into .lloom/benchmarks/verina under the current working directory.
    """
    from config.constants import BENCHMARKS_DIR
    verina_dir = Path.cwd() / BENCHMARKS_DIR / "verina"

    if verina_dir.exists():
        return verina_dir

    verina_dir.parent.mkdir(parents=True, exist_ok=True)

    print("Cloning VERINA (shallow clone)...", file=sys.stderr)
    result = subprocess.run(
        ["git", "clone", "--depth=1", VERINA_REPO_URL, str(verina_dir)],
        capture_output=True, text=True,
    )

    if result.returncode == 0:
        print(f"✓ VERINA cloned to {verina_dir}", file=sys.stderr)
        return verina_dir

    print(f"Error: Failed to clone VERINA: {result.stderr}", file=sys.stderr)
    raise RuntimeError("Failed to clone VERINA")


def extract_imports(lean_content: str, import_type: str) -> str:
    """Extract imports of a specific type (task or solution)."""
    start_pattern = rf'!benchmark\s+@start\s+import\s+type={re.escape(import_type)}'
    end_pattern = r'!benchmark\s+@end\s+import(?:\s|$)'
    
    lines = lean_content.split('\n')
    in_section = False
    result_lines = []
    
    for line in lines:
        if re.search(start_pattern, line):
            in_section = True
            continue
        if re.search(end_pattern, line):
            break
        if in_section:
            result_lines.append(line)
    
    return '\n'.join(result_lines).strip()


def extract_lean_section(lean_content: str, section_name: str) -> str:
    """Extract a section from Lean file marked with !benchmark markers."""
    start_pattern = rf'!benchmark\s+@start\s+{re.escape(section_name)}(?:\s|$)'
    end_pattern = rf'!benchmark\s+@end\s+{re.escape(section_name)}(?:\s|$)'
    
    lines = lean_content.split('\n')
    in_section = False
    result_lines = []
    
    for line in lines:
        if re.search(start_pattern, line):
            in_section = True
            continue
        if re.search(end_pattern, line):
            break
        if in_section:
            result_lines.append(line)
    
    return '\n'.join(result_lines).strip()


def extract_python_reference(markdown_content: str) -> str:
    """Extract reference Python implementation from coverage_report.md."""
    lines = markdown_content.split('\n')
    in_code_block = False
    code_lines = []
    found_coverage_section = False
    
    for line in lines:
        if '## Source Code with Coverage' in line:
            found_coverage_section = True
            continue
        if found_coverage_section:
            if line.strip().startswith('```python'):
                in_code_block = True
                continue
            if line.strip() == '```' and in_code_block:
                break
            if in_code_block:
                cleaned = re.sub(r'^\d+:\s*[✓✗]\s', '', line)
                code_lines.append(cleaned)
    
    return '\n'.join(code_lines).strip()


def load_problem(problem_dir: Path) -> Dict[str, Any]:
    """Load a single VERINA problem."""
    task_file = problem_dir / "task.json"
    if not task_file.exists():
        raise FileNotFoundError(f"task.json not found in {problem_dir}")
    
    with open(task_file) as f:
        task_data = json.load(f)
    
    desc_file = problem_dir / "description.txt"
    description = desc_file.read_text().strip() if desc_file.exists() else ""
    
    lean_file = problem_dir / "task.lean"
    lean_content = lean_file.read_text() if lean_file.exists() else ""
    
    test_file = problem_dir / "test.json"
    tests = json.loads(test_file.read_text()) if test_file.exists() else []
    
    reject_file = problem_dir / "reject_inputs.json"
    reject_inputs = json.loads(reject_file.read_text()) if reject_file.exists() else []
    
    coverage_file = problem_dir / "coverage_report.md"
    python_reference = ""
    if coverage_file.exists():
        coverage_content = coverage_file.read_text()
        python_reference = extract_python_reference(coverage_content)
    
    return {
        "problem_id": task_data["id"],
        "description": description,
        "signature": task_data["signature"],
        "precond_desc": task_data["specification"]["preconditions"],
        "postcond_desc": task_data["specification"]["postconditions"],
        "precond": extract_lean_section(lean_content, "precond"),
        "postcond": extract_lean_section(lean_content, "postcond"),
        "code": extract_lean_section(lean_content, "code"),
        "proof": extract_lean_section(lean_content, "proof"),
        "precond_aux": extract_lean_section(lean_content, "precond_aux"),
        "postcond_aux": extract_lean_section(lean_content, "postcond_aux"),
        "code_aux": extract_lean_section(lean_content, "code_aux"),
        "proof_aux": extract_lean_section(lean_content, "proof_aux"),
        "task_imports": extract_imports(lean_content, "task"),
        "solution_imports": extract_imports(lean_content, "solution"),
        "python_reference": python_reference,
        "tests": tests,
        "reject_inputs": reject_inputs,
        "metadata": task_data.get("metadata", {})
    }


def get_problem(difficulty: str, number: int, components: Optional[List[str]] = None) -> Dict[str, Any]:
    """Load a verina problem, optionally filtering to specific components.

    Args:
        difficulty: "basic" or "advanced"
        number: Problem number
        components: Optional list of keys to include (e.g. ["description", "signature"])

    Returns:
        Problem data dict
    """
    verina_dir = ensure_verina_repo()
    problem_dir = verina_dir / "datasets" / "verina" / f"verina_{difficulty}_{number}"
    if not problem_dir.exists():
        raise FileNotFoundError(f"Problem verina_{difficulty}_{number} not found")
    data = load_problem(problem_dir)
    if components:
        data = {k: v for k, v in data.items() if k in components}
    return data


def format_text(data: Dict[str, Any]) -> str:
    """Format a problem dict as human-readable text (same as CLI text output)."""
    parts = []
    for key, value in data.items():
        parts.append(f"=== {key.upper()} ===")
        if isinstance(value, (dict, list)):
            parts.append(json.dumps(value, indent=2))
        else:
            parts.append(str(value))
        parts.append("")
    return "\n".join(parts)


def main():
    parser = argparse.ArgumentParser(
        description="Get VERINA benchmark problems",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python3 scripts/verina.py basic 1
  python3 scripts/verina.py advanced 25 -c description signature
  python3 scripts/verina.py basic 1 -c code proof -f text
        """
    )

    parser.add_argument("difficulty", choices=["basic", "advanced"])
    parser.add_argument("number", type=int)
    parser.add_argument("-c", "--components", nargs="+", help="Specific components to extract")
    parser.add_argument("-f", "--format", choices=["json", "text"], default="json")

    args = parser.parse_args()

    try:
        data = get_problem(args.difficulty, args.number, args.components)
    except FileNotFoundError as e:
        print(f"Error: {e}", file=sys.stderr)
        return 1
    except Exception as e:
        print(f"Error loading problem: {e}", file=sys.stderr)
        return 1

    if args.format == "json":
        print(json.dumps(data, indent=2))
    else:
        print(format_text(data))

    return 0


if __name__ == "__main__":
    sys.exit(main())
