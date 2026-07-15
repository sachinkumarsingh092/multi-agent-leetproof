#!/usr/bin/env python3
"""
Generate verification file from SpecDSL specification file.

This script extracts the specdef block from a spec file and generates
a verification file with test cases and proof goals.
"""

import re
import sys
import argparse

from utils.lean.constants import SET_MAX_HEARTBEATS
from utils.lean_proof_parser import extract_declarations, LeanDef, parse_lean_theorem


def find_matching_paren(text, start):
    """Find matching closing parenthesis"""
    depth = 1
    i = start + 1
    while i < len(text) and depth > 0:
        if text[i] == '(':
            depth += 1
        elif text[i] == ')':
            depth -= 1
        i += 1
    return i - 1 if depth == 0 else -1


def extract_specs_section(content):
    """
    Extract everything between 'section Specs' and 'end Specs'.
    Returns the content inside the section.
    """
    # Find section Specs block
    section_match = re.search(r'section\s+Specs\s*\n', content)
    if not section_match:
        raise ValueError("Cannot find 'section Specs' block")

    section_start = section_match.end()

    # Find matching end Specs
    end_match = re.search(r'end\s+Specs', content[section_start:])
    if not end_match:
        raise ValueError("Cannot find 'end Specs'")

    end_pos = section_start + end_match.start()

    # Extract content between section Specs and end Specs
    specs_content = content[section_start:end_pos].strip()

    return specs_content


def parse_specs_content(specs_content):
    """
    Parse the content inside a section Specs block.
    Extract helper functions, require/ensures definitions, and precondition/postcondition.
    Uses the lean_proof_parser for robust multi-line parameter parsing.
    """
    # Use extract_declarations to get all definitions
    decls = extract_declarations(specs_content)
    defs = [d for d in decls if isinstance(d, LeanDef) and d.kind == 'def']

    # Find precondition and postcondition by name
    precond_def_obj = None
    postcond_def_obj = None
    for d in defs:
        if d.name == 'precondition':
            precond_def_obj = d
        elif d.name == 'postcondition':
            postcond_def_obj = d

    if not precond_def_obj:
        raise ValueError("Cannot find 'def precondition' in section Specs")
    if not postcond_def_obj:
        raise ValueError("Cannot find 'def postcondition' in section Specs")

    precond_def = precond_def_obj.content.strip()
    postcond_def = postcond_def_obj.content.strip()

    # Parse parameters using parse_lean_theorem (handles multi-line defs)
    try:
        precond_parsed = parse_lean_theorem(precond_def)
        postcond_parsed = parse_lean_theorem(postcond_def)
    except Exception as e:
        raise ValueError(f"Cannot parse precondition or postcondition parameters: {e}")

    # Convert LeanBinder params to (name, type) tuples
    # LeanBinder has names (list) and type_expr (str)
    precond_params_list = []
    for binder in precond_parsed.params:
        for name in binder.names:
            precond_params_list.append((name, binder.type_expr))

    postcond_params_list = []
    for binder in postcond_parsed.params:
        for name in binder.names:
            postcond_params_list.append((name, binder.type_expr))

    # The last parameter of postcondition is the return value
    if len(postcond_params_list) <= len(precond_params_list):
        raise ValueError("postcondition must have more parameters than precondition")

    return_param = postcond_params_list[-1]

    # Extract everything before precondition definition (helpers + require/ensures)
    precond_pos = specs_content.find('def precondition')
    helpers_and_requires = specs_content[:precond_pos].strip()

    return {
        'helpers_and_requires': helpers_and_requires,
        'precond_def': precond_def,
        'postcond_def': postcond_def,
        'precond_params_list': precond_params_list,
        'postcond_params_list': postcond_params_list,
        'return_param': return_param
    }


def extract_test_cases(content):
    """
    Extract test case definitions from content.
    Returns a dict mapping test case IDs to their variable definitions.
    """
    def extract_test_defs(text):
        """Extract test case definitions that may span multiple lines"""
        results = []
        pattern = r'\bdef\s+(test\w+)\s*:\s*([^:=]+?)\s*:='
        matches = list(re.finditer(pattern, text))

        for match in matches:
            name = match.group(1)
            typ = match.group(2).strip()

            # Find where the value starts (after :=)
            value_start = match.end()
            remaining_text = text[value_start:]
            lines = remaining_text.split('\n')

            # Collect lines until we hit empty line, comment, or next def
            value_lines = []
            started = False
            first_line = True

            for line in lines:
                stripped = line.strip()

                if first_line:
                    first_line = False
                    if not stripped:
                        value_lines.append('')
                        continue

                if stripped:
                    started = True

                if started:
                    if not stripped:
                        break
                    if stripped.startswith('--'):
                        break
                    if stripped.startswith('def '):
                        break

                value_lines.append(line.rstrip())

            value = '\n'.join(value_lines).rstrip()

            if value and not value.startswith('\n'):
                value = value.lstrip()

            if value:
                results.append((name, typ, value))

        return results

    test_defs = extract_test_defs(content)

    # Organize by test case
    test_cases = {}
    for name, typ, val in test_defs:
        test_id_match = re.match(r'(test\d+)', name)
        if test_id_match:
            case_id = test_id_match.group(1)
            if case_id not in test_cases:
                test_cases[case_id] = []
            test_cases[case_id].append((name, typ, val))

    return test_cases


def find_recommended_tests(content):
    """Find recommended test cases from comments"""
    rec_pattern = re.compile(r"Recommend to validate:\s*(.+?)(?:\n|$)")
    rec_match = rec_pattern.search(content)

    if rec_match:
        rec_text = rec_match.group(1)
        numbers = re.findall(r'\d+', rec_text)
        # Remove duplicates while preserving order
        unique_tests = []
        for test in [f"test{num}" for num in numbers]:
            if test not in unique_tests:
                unique_tests.append(test)
        return unique_tests

    # If no recommendation, find all test cases
    test_matches = re.findall(r'def (test\d+)_', content)
    if test_matches:
        def get_test_num(k: str) -> int:
            m = re.search(r'\d+', k)
            return int(m.group()) if m else 0
        unique_tests = sorted(set(test_matches), key=get_test_num)
        return unique_tests

    return []


def generate_verification_file(spec_file_path, output_file_path):
    """Generate verification file from spec file"""

    with open(spec_file_path, 'r', encoding='utf-8') as f:
        content = f.read()

    # Extract section Specs block
    specs_content = extract_specs_section(content)

    # Parse specs content
    spec_data = parse_specs_content(specs_content)

    # Extract test cases
    test_cases = extract_test_cases(content)

    # Find recommended tests
    rec_cases = find_recommended_tests(content)

    # Generate output file
    with open(output_file_path, 'w', encoding='utf-8') as f:
        # Header
        f.write("import Lean\n")
        f.write("import Mathlib.Tactic\n")
        f.write("\n")
        f.write(f"{SET_MAX_HEARTBEATS}\n")
        f.write("\n")

        # --- section Specs ---
        f.write("section Specs\n\n")

        # Separate actual helpers from require/ensures definitions
        if spec_data['helpers_and_requires']:
            # Clean up: remove unwanted lines
            helpers_lines = spec_data['helpers_and_requires'].split('\n')
            cleaned_lines = []

            skip_next_empty = False
            for line in helpers_lines:
                stripped = line.strip()

                if skip_next_empty:
                    skip_next_empty = False
                    if not stripped:
                        continue

                # Skip register commands, set_option, and all comment-only lines
                if (stripped.startswith('register_specdef_') or
                    stripped.startswith('set_option ') or
                    stripped.startswith('--')):
                    skip_next_empty = True
                    continue
                cleaned_lines.append(line)

            # Separate helpers from require/ensures
            actual_helpers = []
            require_ensures = []
            current_block = actual_helpers

            for line in cleaned_lines:
                stripped = line.strip()

                # Check if this line starts a new definition
                if stripped.startswith('def '):
                    # Check if it's require or ensures
                    if re.match(r'def\s+(require\d+|ensures\d+)\s', stripped):
                        current_block = require_ensures
                    else:
                        current_block = actual_helpers

                current_block.append(line)

            # Write actual helper functions (if any)
            helpers_text = '\n'.join(actual_helpers).strip()
            if helpers_text:
                f.write("-- Helper Functions\n\n")
                f.write(helpers_text)
                f.write("\n\n")

            # Write require/ensures definitions
            require_ensures_text = '\n'.join(require_ensures).strip()
            if require_ensures_text:
                f.write(require_ensures_text)
                f.write("\n\n")

        # Write precondition and postcondition definitions directly from spec file
        f.write(spec_data['precond_def'])
        f.write("\n\n")
        f.write(spec_data['postcond_def'])
        f.write("\n\n")

        f.write("end Specs\n\n")

        # Generate parameter names for test theorems
        pre_param_names = ' '.join([name for name, _ in spec_data['precond_params_list']])

        # --- section TestCases ---
        f.write("section TestCases\n\n")
        test_data = []

        for case_id in rec_cases:
            if case_id not in test_cases:
                continue

            lines = test_cases[case_id]
            for var_name, var_type, var_value in lines:
                if var_value.startswith('\n'):
                    f.write(f"abbrev {var_name} : {var_type} :={var_value}\n\n")
                else:
                    f.write(f"abbrev {var_name} : {var_type} := {var_value}\n\n")

            # Find parameter variables and expected result
            param_vars = [v[0] for v in lines
                         if not (v[0].lower().endswith("expected") or
                                v[0].endswith("_α") or
                                v[0].endswith("_Inh") or
                                v[0].endswith("_Dec"))]
            expected_vars = [v[0] for v in lines if v[0].lower().endswith("expected")]

            if expected_vars:
                param_list = " ".join(param_vars)
                ret_var = expected_vars[0]
                test_data.append((case_id, param_list, ret_var))

        f.write("end TestCases\n\n")

        # --- section Proof ---
        f.write("section Proof\n\n")

        # Verifications
        f.write("-------------------------------\n")
        f.write("-- Verifications\n")
        f.write("-------------------------------\n\n")

        for case_id, param_list, ret_var in test_data:
            f.write(f"-- {case_id}\n")

            # Precondition verification
            f.write(f"theorem {case_id}_precondition :\n")
            f.write(f"  precondition {param_list} := by\n")
            f.write(f"  sorry\n\n")

            # Postcondition verification
            f.write(f"theorem {case_id}_postcondition :\n")
            f.write(f"  postcondition {param_list} {ret_var} := by\n")
            f.write(f"  sorry\n\n")

        # Uniqueness
        f.write("-----------------------------\n")
        f.write("-- Uniqueness Verification --\n")
        f.write("-----------------------------\n")

        # Extract parameter string from precondition definition
        # Match parameters before optional return type and :=
        precond_params_match = re.search(r'def\s+precondition\s+((.*?))\s*(?::\s*\w+)?\s*:=', spec_data['precond_def'])
        if precond_params_match:
            param_str = precond_params_match.group(1).strip()
        else:
            # Fallback to constructing from list
            param_str = ' '.join([f"({name}: {typ})" for name, typ in spec_data['precond_params_list']])

        f.write(f"theorem uniqueness {param_str}:\n")
        f.write(f"  precondition {pre_param_names} →\n")
        f.write(f"  (∀ ret1 ret2,\n")
        f.write(f"    postcondition {pre_param_names} ret1 →\n")
        f.write(f"    postcondition {pre_param_names} ret2 →\n")
        f.write(f"    ret1 = ret2) := by\n")
        f.write(f"  sorry\n\n")
        f.write("end Proof\n")


def main():
    parser = argparse.ArgumentParser(
        description='Generate verification file from SpecDSL specification file'
    )
    parser.add_argument('--input-file', required=True,
                       help='Input specification file (e.g., mbpp_1_spec.lean)')
    parser.add_argument('--output-file', required=True,
                       help='Output verification file (e.g., mbpp_1_example_verify.lean)')

    args = parser.parse_args()

    try:
        generate_verification_file(args.input_file, args.output_file)
        print(f"Successfully generated {args.output_file} from {args.input_file}")
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
