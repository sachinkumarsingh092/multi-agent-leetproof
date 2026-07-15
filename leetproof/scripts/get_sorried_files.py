import argparse
import json
import re
import sys
from enum import Enum
from pathlib import Path

from utils.lean.parser import LeanFile
from utils.sorry_extraction import extract_sorry_goals
from utils.velvet_helpers import COMMENT

PROOF_SECTION = 'Proof'

class LeanProofStatus(Enum):
    SORRIED = "sorried"  
    MISSING = "missing"
    COMPLETE = "complete"


def analyze_proofs_in_file(lean_file : LeanFile, proof_section: str ) -> tuple[LeanProofStatus, list[str]]:
    """
    Returns the status and the goals that are sorried
    """
    proofs = lean_file.get_section(proof_section)
    status: LeanProofStatus = LeanProofStatus.MISSING
    sorried_goals : list[str] = []
    if not proofs:
        return (status ,sorried_goals)

    extraction_result = extract_sorry_goals(lean_file, proof_section, [] )
    sorry_goals_extracted = extraction_result.sorry_goals
    status : LeanProofStatus = LeanProofStatus.SORRIED if len(sorry_goals_extracted) != 0 else LeanProofStatus.COMPLETE
    sorried_goals = [goal.name for goal in sorry_goals_extracted]
    return (status, sorried_goals )



def main():
    parser = argparse.ArgumentParser(description="Find sorried goals in Lean files")
    parser.add_argument("project", type=str, help="Path to the project directory")
    parser.add_argument("--sections-to-show", type=str, nargs="*", default=[], help="Sections to extract")
    parser.add_argument("--file-pattern", type=str, default="*.lean", help="File pattern to match, e.g. '*.lean'")
    parser.add_argument("--proof-section", type=str, default="Proof", help="Section to check the sorried goals")
    parser.add_argument("--proof-status", type=str, choices=["sorried", "missing", "complete"], help="Filter by proof status")
    parser.add_argument("--json", action="store_true", help="Output results as JSON")
    
    args = parser.parse_args()

    project_path = Path(args.project)
    if not project_path.is_dir():
        print(f"Error: Project directory '{args.project}' not found.", file=sys.stderr)
        sys.exit(1)

    results = []

    for file_path in project_path.rglob(args.file_pattern):
        if not file_path.is_file():
            continue

        try:
            lean_file = LeanFile.from_path(file_path)
            status, sorried_goals = analyze_proofs_in_file(lean_file, args.proof_section)
            
            if args.proof_status and status.value != args.proof_status:
                continue

            extracted_sections = []
            if args.sections_to_show:
                for sec_name in args.sections_to_show:
                    section_obj = lean_file.get_section(sec_name)
                    if section_obj:
                        extracted_sections.append({
                            "section_name": sec_name,
                            "content": section_obj.content
                        })

            results.append({
                "file": str(file_path),
                "proof_status": status.value,
                "sections": extracted_sections,
                "sorried_goals": sorried_goals
            })
        except Exception:
            # Skip files that can't be parsed
            continue

    if args.json:
        print(json.dumps(results, indent=2))
    else:
        for res in results:
            print("="*100)
            print(f"\n\n## File: {res['file']}")
            print(f"\n**Proof Status**: {res['proof_status']}")
            
            if res['sorried_goals']:
                print("\n**Sorried Goals**:")
                for sg in res['sorried_goals']:
                    print(f"- {sg}")
                    
            if res['sections']:
                print("\n**Sections**:")
                for sec in res['sections']:
                    print(f"### {sec['section_name']}")
                    print(sec['content'])
            print("="*100)
            print()

if __name__ == '__main__':
    main()
