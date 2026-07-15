#!/usr/bin/env python3
"""
Build a RAG database from specification files.

Given a directory containing Lean specification files, this script extracts
problem descriptions and specification code, then outputs a JSON file suitable
for RAG (Retrieval-Augmented Generation) systems.
"""

import json
import re
from pathlib import Path
from typing import Dict, Optional


def extract_problem_description(content: str) -> str:
    """
    Extract the problem description from a Lean spec file.

    Handles both single-line (--) and multi-line (/-  -/) comment formats.
    """
    lines = content.split('\n')
    description_lines = []
    in_multiline_comment = False
    found_problem_desc = False

    for line in lines:
        stripped = line.strip()

        # Check for multi-line comment start
        if '/-' in stripped:
            in_multiline_comment = True
            # Extract content after /-
            after_start = stripped.split('/-', 1)[1].strip()
            if after_start and not after_start.startswith('-'):
                if 'Problem Description' in after_start or 'MBPP Problem' in after_start:
                    found_problem_desc = True
                    description_lines.append(after_start)
            continue

        # Check for multi-line comment end
        if '-/' in stripped:
            in_multiline_comment = False
            # Extract content before -/
            before_end = stripped.split('-/', 1)[0].strip()
            if before_end and found_problem_desc:
                description_lines.append(before_end)
            break

        # Handle multi-line comment content
        if in_multiline_comment:
            if 'Problem Description' in stripped or 'MBPP Problem' in stripped:
                found_problem_desc = True
                description_lines.append(stripped)
            elif found_problem_desc:
                # Skip "Natural language breakdown:" and similar headers
                if stripped and not stripped.startswith('Natural language'):
                    description_lines.append(stripped)
            continue

        # Handle single-line comments (--)
        if stripped.startswith('--'):
            comment_text = stripped[2:].strip()
            if 'MBPP Problem' in comment_text or 'Problem Description' in comment_text:
                found_problem_desc = True
                description_lines.append(comment_text)
            elif found_problem_desc:
                # Stop at empty comment or start of breakdown
                if not comment_text or 'Natural language' in comment_text:
                    break
                description_lines.append(comment_text)
        elif found_problem_desc:
            # Stop when we hit non-comment lines
            break

    # Join and clean up the description
    description = ' '.join(description_lines)
    # Remove "Problem Description:" or "MBPP Problem X:" prefix if present
    description = re.sub(r'^(Problem Description:\s*|MBPP Problem \d+:\s*)', '', description)
    return description.strip()


def extract_spec_code(content: str) -> str:
    """
    Extract the specification code from a Lean spec file.

    Includes everything from the start of the file up to the TestCases section.
    """
    # Find the TestCases section
    test_section_pattern = r'section TestCases'
    match = re.search(test_section_pattern, content)

    if match:
        # Extract everything before the TestCases section
        spec_code = content[:match.start()].rstrip()
    else:
        # If no TestCases section, include the entire file
        spec_code = content.rstrip()

    return spec_code


def process_spec_file(file_path: Path) -> Optional[Dict[str, str]]:
    """
    Process a single specification file and extract relevant information.

    Returns a dictionary with 'problem_description' and 'spec_code' keys,
    or None if the file cannot be processed.
    """
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()

        problem_description = extract_problem_description(content)
        spec_code = extract_spec_code(content)

        # Only return if we successfully extracted a problem description
        if not problem_description:
            print(f"Warning: Could not extract problem description from {file_path}")
            return None

        return {
            "problem_description": problem_description,
            "spec_code": spec_code
        }

    except Exception as e:
        print(f"Error processing {file_path}: {e}")
        return None


def build_rag_database(spec_dir: str, output_file: str) -> None:
    """
    Build a RAG database from all specification files in the given directory.

    Args:
        spec_dir: Directory containing specification files
        output_file: Path to output JSON file
    """
    spec_dir_path = Path(spec_dir)

    if not spec_dir_path.exists():
        raise ValueError(f"Directory does not exist: {spec_dir}")

    if not spec_dir_path.is_dir():
        raise ValueError(f"Not a directory: {spec_dir}")

    # Find all .lean files in the directory (recursively)
    spec_files = list(spec_dir_path.rglob("*.lean"))

    if not spec_files:
        print(f"Warning: No .lean files found in {spec_dir}")
        return

    print(f"Found {len(spec_files)} .lean files")

    # Process each file
    rag_entries = []
    for spec_file in sorted(spec_files):
        print(f"Processing: {spec_file}")
        entry = process_spec_file(spec_file)
        if entry:
            rag_entries.append(entry)

    # Write to JSON file
    with open(output_file, 'w', encoding='utf-8') as f:
        json.dump(rag_entries, f, indent=2, ensure_ascii=False)

    print(f"\nSuccessfully created RAG database with {len(rag_entries)} entries")
    print(f"Output written to: {output_file}")


def main():
    """Main entry point for the script."""
    import argparse

    parser = argparse.ArgumentParser(
        description="Build a RAG database from specification files"
    )
    parser.add_argument(
        "--input-dir",
        required=True,
        help="Directory containing specification files"
    )
    parser.add_argument(
        "--output",
        default="spec_rag_data.json",
        help="Output JSON file path (default: spec_rag_data.json)"
    )

    args = parser.parse_args()

    build_rag_database(args.input_dir, args.output)


if __name__ == "__main__":
    main()
