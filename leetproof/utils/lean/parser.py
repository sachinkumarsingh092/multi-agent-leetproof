"""Parsing utilities for Lean files."""

from pathlib import Path
import re
from dataclasses import dataclass, field
from typing import Tuple, List, Dict, Optional, Literal, overload, Callable

from logging_config import get_logger
from utils.lean.types import Param, Goal
from utils.velvet_types import VelvetMethod

logger = get_logger(__name__)

@dataclass
class TheoremSignaturesCheckResult:
    matches: bool
    reason: str
    expected: str | None = None
    received: str | None = None

def extract_theorem_name(theorem_text: str, theorem_declaration_identifier: str = "theorem") -> str:
    """Extract the name of a theorem from its declaration."""
    text = _remove_comments(theorem_text)

    if "theorem" not in text:
        raise ValueError("No theorem keyword found in theorem declaration")

    name_start = text.find(f"{theorem_declaration_identifier} ") + len(f"{theorem_declaration_identifier} ")
    idx = name_start
    stop_chars = {':', '(', '{', '[', '⦃'}
    while idx < len(theorem_text) and text[idx] != ":" and text[idx] not in stop_chars:
        idx += 1
    name_end = idx
    name = text[name_start:name_end].strip()
    return name


def replace_have_proofs_with_sorry(theorem_text: str) -> str:
    """Replace the proofs of have statements with sorry while preserving the theorem structure."""
    if not theorem_text or not theorem_text.strip():
        return theorem_text

    lines = theorem_text.split('\n')
    result_lines = []
    i = 0

    while i < len(lines):
        line = lines[i]
        stripped_line = line.strip()

        if not stripped_line or stripped_line.startswith('--'):
            result_lines.append(line)
            i += 1
            continue

        if 'have ' in line:
            have_pos = line.find('have ')
            if (have_pos == 0 or not line[have_pos - 1].isalnum()) and \
               (have_pos + 4 >= len(line) or not line[have_pos + 4].isalnum()):

                have_declaration, next_i = _parse_have_statement(lines, i)

                if have_declaration:
                    prefix = line[:have_pos]
                    result_lines.append(f"{prefix}{have_declaration} := by sorry")
                    i = next_i
                else:
                    result_lines.append(line)
                    i += 1
            else:
                result_lines.append(line)
                i += 1
        else:
            result_lines.append(line)
            i += 1

    return '\n'.join(result_lines)


def _parse_have_statement(lines: List[str], start_idx: int) -> Tuple[str, int]:
    """Parse a have statement to extract the declaration part."""
    if start_idx >= len(lines):
        return "", start_idx + 1

    have_line = lines[start_idx]
    have_pos = have_line.find('have ')

    if have_pos == -1:
        return "", start_idx + 1

    have_indent = have_pos
    in_let_statement = False
    bracket_stack = []
    bracket_pairs = {'(': ')', '[': ']', '{': '}'}
    declaration_parts = []
    i = start_idx

    while i < len(lines):
        line = lines[i]
        stripped_line = line.strip()
        line_indent = len(line) - len(line.lstrip())

        if stripped_line and line_indent <= have_indent and i > start_idx:
            break

        if i == start_idx:
            line_to_process = line[have_pos:]
        else:
            line_to_process = line

        j = 0
        found_terminal = False
        while j < len(line_to_process):
            char = line_to_process[j]

            if char in bracket_pairs:
                bracket_stack.append(bracket_pairs[char])
            elif char in bracket_pairs.values():
                if bracket_stack and bracket_stack[-1] == char:
                    bracket_stack.pop()

            if j <= len(line_to_process) - 4 and line_to_process[j:j+4] == 'let ':
                if (j == 0 or not line_to_process[j-1].isalnum()) and \
                   (j+4 >= len(line_to_process) or not line_to_process[j+3].isalnum()):
                    in_let_statement = True

            if j < len(line_to_process) - 1 and line_to_process[j:j+2] == ':=':
                if in_let_statement:
                    in_let_statement = False
                elif len(bracket_stack) == 0:
                    if line_to_process[:j].strip():
                        declaration_parts.append(line_to_process[:j])
                    found_terminal = True
                    i += 1
                    break

            j += 1

        if found_terminal:
            break

        declaration_parts.append(line_to_process)
        i += 1

    have_declaration = '\n'.join(part for part in declaration_parts if part).strip()

    while i < len(lines):
        line = lines[i]
        stripped_line = line.strip()
        line_indent = len(line) - len(line.lstrip())

        if stripped_line and line_indent <= have_indent:
            break

        i += 1

    return have_declaration, i


@overload
def _split_at_first_assignment(text_input: str, start_idx: int, return_idx: Literal[True]) -> Tuple[str, str] : ...

@overload
def _split_at_first_assignment(text_input: str, start_idx: int = 0, return_idx: Literal[False] = False) -> Tuple[str, str, int | None] : ...

def _split_at_first_assignment(text_input: str, start_idx: int = 0, return_idx: bool = False) -> Tuple[str, str] | Tuple[str, str, int | None]:
    """Split text at the first := that's not inside parentheses/brackets."""
    stack = []
    bracket_pairs = {'(': ')', '[': ']', '{': '}'}

    i = start_idx
    in_let_statement = False
    text = _remove_comments(text_input)

    while i < len(text):
        char = text[i]
        if char in bracket_pairs:
            stack.append(bracket_pairs[char])
        elif char in bracket_pairs.values():
            if stack and stack[-1] == char:
                stack.pop()

        if i <= len(text) - 4 and text[i:i+4] == 'let ':
            if (i == 0 or not text[i-1].isalnum()) and \
                (i+4 >= len(text) or not text[i+3].isalnum()):
                in_let_statement = True

        if i < len(text) - 1 and text[i:i+2] == ':=':
            if in_let_statement:
                in_let_statement = False
            elif len(stack) == 0:
                before = text[start_idx:i].strip()
                after = text[i + 2:].strip()
                if return_idx:
                    return before, after, i 
                else:
                    return before, after

        i += 1

    if return_idx:
        return text, "", None
    else:
        return text, ""


def _remove_all_nontheorem_lines(text):
    """Remove all lines before the theorem declaration."""
    all_lines = text.split("\n")
    to_include = []
    for idx, line in enumerate(all_lines):
        if line.startswith('theorem'):
            to_include = all_lines[idx:]
            break
    if not to_include:
        logger.info("Theorem does not have non-theorem lines\n%s", text)
        return None

    new_text = "\n".join(to_include).strip()
    return new_text


def extract_theorem_signature(text):
     """Extract the theorem statement from Lean 4 code up to ':='."""
     new_text = _remove_all_nontheorem_lines(text)
     if not new_text:
         return None
     before, _ = _split_at_first_assignment(new_text)  # type: ignore
     return before


def normalize_signature(signature: str) -> str:
    """Normalize a signature by removing extra whitespace and standardizing formatting."""
    if not signature:
        return ""

    normalized = re.sub(r'\s+', ' ', signature.strip())

    operators = [
        (r'\s*=\s*', '='),
        (r'\s*∈\s*', '∈'),
        (r'\s*∏\s*', '∏'),
        (r'\s*∑\s*', '∑'),
        (r'\s*→\s*', '→'),
        (r'\s*←\s*', '←'),
        (r'\s*↔\s*', '↔'),
        (r'\s*%\s*', '%'),
        (r'\s*\|\s*', '|'),
        (r'\s*∣\s*', '∣'),
        (r'\s*∤\s*', '∤'),
    ]

    for pattern, replacement in operators:
        normalized = re.sub(pattern, replacement, normalized)

    brackets = [
        (r'\s*\(\s*', '('),
        (r'\s*\)\s*', ')'),
        (r'\s*\[\s*', '['),
        (r'\s*\]\s*', ']'),
        (r'\s*\{\s*', '{'),
        (r'\s*\}\s*', '}'),
    ]

    for pattern, replacement in brackets:
        normalized = re.sub(pattern, replacement, normalized)

    punctuation = [
        (r'\s*,\s*', ','),
        (r'\s*:\s*', ':'),
        (r'\s*;\s*', ';'),
        (r'\s*\.\s*', '.'),
    ]

    for pattern, replacement in punctuation:
        normalized = re.sub(pattern, replacement, normalized)

    normalized = re.sub(r'\s+!', '!', normalized)

    arrows = [
        (r'\s*=>\s*', '=>'),
        (r'\s*->\s*', '->'),
        (r'\s*<-\s*', '<-'),
        (r'\s*\|\-\s*', '|-'),
    ]

    for pattern, replacement in arrows:
        normalized = re.sub(pattern, replacement, normalized)

    math_ops = [
        (r'\s*\*\s*', '*'),
        (r'\s*\+\s*', '+'),
        (r'\s*-\s*', '-'),
        (r'\s*/\s*', '/'),
        (r'\s*\^\s*', '^'),
    ]

    for pattern, replacement in math_ops:
        normalized = re.sub(pattern, replacement, normalized)

    normalized = re.sub(r'\s+', ' ', normalized)

    return normalized.strip()


def check_theorem_signature_match(received_theorem: str, expected_theorem: str) -> TheoremSignaturesCheckResult:
    """Check if two theorems have matching signatures (name, params, return type)."""
    from utils.lean_proof_parser import parse_lean_theorem

    try:
        expected_parsed = parse_lean_theorem(expected_theorem)
    except Exception as e:
        return TheoremSignaturesCheckResult(expected=expected_theorem, matches=False, reason=f"Couldn't parse expected theorem signature: {e}")

    try:
        received_parsed = parse_lean_theorem(received_theorem)
    except Exception as e:
        return TheoremSignaturesCheckResult(matches=False, expected=expected_theorem, received=received_theorem, reason=f"Couldn't parse received theorem signature: {e}")

    def norm(s: str) -> str:
        return re.sub(r'\s+', ' ', s.strip()) if s else ""

    name_match = expected_parsed.name == received_parsed.name
    params_match = expected_parsed.params == received_parsed.params
    return_type_match = norm(expected_parsed.return_type or "") == norm(received_parsed.return_type or "")

    matches = name_match and params_match and return_type_match
    reason = ""
    if not matches:
        parts = []
        if not name_match:
            parts.append(f"name: expected '{expected_parsed.name}', got '{received_parsed.name}'")
        if not params_match:
            parts.append(f"params mismatch")
        if not return_type_match:
            parts.append(f"return type: expected '{expected_parsed.return_type}', got '{received_parsed.return_type}'")
        reason = "Signature mismatch: " + "; ".join(parts)
        logger.info(reason)
    return TheoremSignaturesCheckResult(matches, reason, expected=expected_theorem, received=received_theorem)



def _remove_comments(text: str) -> str:
    """Remove comments from Lean code while preserving structure."""
    result = ""
    i = 0
    while i < len(text):
        if i < len(text) - 1 and text[i:i+2] == '/-':
            end_pos = text.find('-/', i + 2)
            if end_pos != -1:
                i = end_pos + 2
                continue
            else:
                break
        else:
            result += text[i]
            i += 1

    lines = result.split('\n')
    cleaned_lines = []

    for line in lines:
        if '--' in line:
            comment_pos = line.find('--')
            if comment_pos != -1:
                line = line[:comment_pos].rstrip()

        cleaned_lines.append(line)

    return '\n'.join(cleaned_lines)


def _skip_to_matching_paren(s: str, start: int) -> int:
    """Skip from opening '(' to after matching ')'."""
    if start >= len(s) or s[start] != '(':
        return start + 1

    depth = 1
    pos = start + 1
    while pos < len(s) and depth > 0:
        if s[pos] == '(':
            depth += 1
        elif s[pos] == ')':
            depth -= 1
        pos += 1
    return pos


def _manual_parse_param(param_str: str) -> tuple[str, str] | None:
    """Manually parse a parameter string like "name : type"."""
    depth = 0
    for i, c in enumerate(param_str):
        if c == '(':
            depth += 1
        elif c == ')':
            depth -= 1
        elif c == ':' and depth == 0:
            name = param_str[:i].strip()
            ty = param_str[i + 1:].strip()
            if name:
                return (name, ty)
            return None
    return None


def parse_theorem(theorem_str: str) -> Goal:
    """Parse a theorem/lemma/have statement into a structured Goal."""
    from utils.velvet_helpers import _parse_name_info

    try:
        stmt_match = re.search(r'\b(theorem|lemma|have)\s+(\w+)', theorem_str)
        if not stmt_match:
            raise ValueError("Could not find theorem/lemma/have statement")

        name = stmt_match.group(2)
        search_start = stmt_match.end()

        first_paren = theorem_str.find('(', search_start)

        params = []
        if first_paren != -1:
            paren_count = 0
            i = first_paren
            params_end = -1
            while i < len(theorem_str):
                if theorem_str[i] == '(':
                    paren_count += 1
                elif theorem_str[i] == ')':
                    paren_count -= 1
                elif theorem_str[i] == ':' and paren_count == 0:
                    params_end = i
                    break
                i += 1

            if params_end != -1:
                params_str = theorem_str[first_paren:params_end]

                pos = 0
                while pos < len(params_str):
                    if params_str[pos] == '(':
                        try:
                            name_info, remaining = _parse_name_info.parse_partial(params_str[pos:])
                            params.append(Param(name=name_info.name, ty=name_info.ty))
                            consumed = len(params_str[pos:]) - len(remaining)
                            pos += consumed
                        except Exception:
                            end_pos = _skip_to_matching_paren(params_str, pos)
                            param_content = params_str[pos + 1:end_pos - 1].strip()

                            parsed = _manual_parse_param(param_content)
                            if parsed:
                                param_name, param_type = parsed
                                params.append(Param(name=param_name, ty=param_type))
                            else:
                                logger.debug(f"Failed to parse param at pos {pos}: {param_content[:50]}")

                            pos = end_pos
                    else:
                        pos += 1

                goal_start = params_end
            else:
                goal_start = first_paren
        else:
            colon_pos = theorem_str.find(':', search_start)
            goal_start = colon_pos if colon_pos != -1 else search_start

        goal_match = re.search(r':\s*(.+?)\s*:=', theorem_str[goal_start:], re.DOTALL)
        if not goal_match:
            raise ValueError("Could not find goal statement")

        goal_statement = goal_match.group(1).strip()

        return Goal(name=name, params=params, final_goal=goal_statement)

    except Exception as e:
        logger.warning(f"Failed to parse theorem: {e}")
        return Goal(name="unknown", params=[], final_goal="")


def extract_theorem_blocks(lean_content: str) -> List[Tuple[str, str]]:
    """Extract all theorem/lemma blocks with their names and full text.

    Args:
        lean_content: Full Lean file content

    Returns:
        List of (name, full_text) tuples for each theorem/lemma
    """
    # Find all theorem/lemma declarations
    pattern = r'^\s*(theorem|lemma)\s+(\w+)'
    matches = list(re.finditer(pattern, lean_content, re.MULTILINE))

    results = []
    for i, match in enumerate(matches):
        name = match.group(2)
        start = match.start()

        # Find end: next top-level declaration or end of file
        if i + 1 < len(matches):
            end = matches[i + 1].start()
        else:
            # Look for other declarations after this theorem
            remaining = lean_content[start:]
            # Find next top-level declaration (def, abbrev, section, etc.)
            next_decl = re.search(r'\n(def|abbrev|theorem|lemma|section|namespace|----)', remaining[1:])
            if next_decl:
                end = start + 1 + next_decl.start()
            else:
                end = len(lean_content)

        theorem_text = lean_content[start:end].rstrip()
        results.append((name, theorem_text))

    return results


def extract_theorems_with_sorry(lean_content: str) -> List[str]:
    """Extract theorems/lemmas that have 'by sorry' proofs.

    Args:
        lean_content: Full Lean file content

    Returns:
        List of theorem statements (as strings, including 'by sorry')
    """
    from utils.lean_proof_parser import parse_lean_theorem

    theorem_blocks = extract_theorem_blocks(lean_content)
    theorems_with_sorry = []

    for name, theorem_text in theorem_blocks:
        try:
            parsed = parse_lean_theorem(theorem_text)

            # Check if it has a 'by' proof with sorry
            if parsed.proof and parsed.proof.is_by:
                has_sorry = any('sorry' in t.content.lower() for t in parsed.proof.tactics)
                if has_sorry:
                    theorems_with_sorry.append(theorem_text)
        except Exception as e:
            logger.debug(f"Failed to parse theorem {name}: {e}")
            continue

    return theorems_with_sorry


def remove_theorems_by_name(lean_content: str, theorem_names: set) -> str:
    """Remove theorems by name from Lean content while preserving all other content.

    Args:
        lean_content: Full Lean file content
        theorem_names: Set of theorem names to remove

    Returns:
        Content with specified theorems removed (imports, comments, etc. preserved)
    """
    lines = lean_content.split('\n')
    result_lines = []
    i = 0

    while i < len(lines):
        line = lines[i]

        # Check if this line starts a theorem/lemma declaration
        keyword_match = re.match(r'\s*(lemma|theorem)\s+(\w+)', line)
        if keyword_match:
            name = keyword_match.group(2)

            if name in theorem_names:
                # Skip this theorem - find its end
                j = i + 1

                # Find the end of this theorem
                while j < len(lines):
                    next_line = lines[j]
                    stripped = next_line.strip()

                    # Check if we've reached another top-level declaration
                    if re.match(r'^(lemma|theorem|def|abbrev|inductive|structure|class|instance)\s+', stripped):
                        break

                    # Also break on section markers
                    if re.match(r'^(section|namespace|end)\s+', stripped):
                        break

                    j += 1

                logger.debug(f"Removed theorem '{name}' (lines {i+1}-{j})")
                i = j  # Skip to after this theorem
                continue

        # Keep this line
        result_lines.append(line)
        i += 1

    return '\n'.join(result_lines)

# --- File Section Parsing ---

@dataclass
class Section:
    """Represents a section in a Lean file.

    Line numbers are 1-indexed and always populated during parsing.
    After modification (append, etc.), line numbers become stale - re-parse if needed.
    """
    name: str
    content: str  # Content between section/end markers (excluding markers)
    trailing_content: str = ""  # Content after 'end <name>' before next section
    # Line numbers (1-indexed, populated during parsing)
    start_line: int = 1  # Line of "section X"
    content_start_line: int = 1  # First line after "section X" (start of content)
    end_line: int = 1  # Line of "end X"

    def full_text(self) -> str:
        """Get the full section text including markers and trailing content.
        
        The format matches what the parser expects:
        - Leading newline (separator from prologue/previous section)
        - "section <name>"
        - Content lines (with preserved internal structure)
        - "end <name>"
        - Trailing content (comments/whitespace between sections)
        """
        # Start with separator newline
        result = f"\nsection {self.name}\n"
        
        # Add content (preserving internal structure, but remove extraneous leading/trailing newlines)
        content = self.content.strip('\n') if self.content else ""
        if content:
            result += f"{content}\n"
        
        # Add end marker
        result += f"end {self.name}\n"
        
        # Add trailing content (comments/whitespace after 'end')
        if self.trailing_content:
            result += self.trailing_content
        
        return result

    def content_line_span(self) -> Tuple[int, int]:
        """Get the line span of section content (inclusive, 1-indexed).

        Returns:
            (first_content_line, last_content_line) - the range of lines
            containing the section content (between 'section X' and 'end X').
        """
        # Content ends on the line before 'end X'
        return (self.content_start_line, self.end_line - 1)

    def is_line_in_content(self, absolute_line: int) -> bool:
        """Check if an absolute line number falls within section content."""
        start, end = self.content_line_span()
        return start <= absolute_line <= end


@dataclass
class LeanFile:
    """Parsed Lean file with prologue and sections."""
    prologue: str
    sections: List[Section] = field(default_factory=list)

    @classmethod
    def from_content(cls, content: str) -> "LeanFile":
        """Parse a Lean file from string content."""
        return parse_lean_file_sections(content)

    @classmethod
    def from_path(cls, path: str | Path) -> "LeanFile":
        """Parse a Lean file from disk."""
        if isinstance(path, str):
            path = Path(path)
        with open(path, 'r') as f:
            return cls.from_content(f.read())

    @overload
    def get_section(self, name: str, assert_exists: Literal[True]) -> Section: ...

    @overload
    def get_section(self, name: str, assert_exists: Literal[False] = False) -> Section | None: ...

    def get_section(self, name: str, assert_exists: bool = False) -> Section | None:
        """Get a section by name.

        Args:
            name: The name of the section to retrieve
            assert_exists: If True, raise an AssertionError if section doesn't exist

        Returns:
            Section if found, None otherwise (unless assert_exists=True)

        Raises:
            AssertionError: If assert_exists=True and section is not found
        """
        for section in self.sections:
            if section.name == name:
                return section
        if assert_exists:
            assert False, f"Section '{name}' not found in file"
        return None

    def has_section(self, name: str) -> bool:
        """Check if a section with the given name exists."""
        return any(s.name == name for s in self.sections)

    def section_names(self) -> List[str]:
        """Get list of all section names in order."""
        return [s.name for s in self.sections]

    def reconstruct(self) -> str:
        """Reconstruct the file content from parsed structure."""
        result = ""
        if self.prologue:
            result = self.prologue

        # Concatenate sections directly
        # Each section.full_text() starts with \n (separator), which is correct when there's a prologue
        # But if there's no prologue, the first section's leading \n should be removed
        for i, section in enumerate(self.sections):
            section_text = section.full_text()
            if i == 0 and not self.prologue:
                # First section with no prologue: remove leading \n
                section_text = section_text.lstrip('\n')
            result += section_text

        return result

    def add_or_replace_section(self, name: str, content: str, after: str | None = None) -> None:
        """Add a new section or replace existing section content.

        Args:
            name: Section name
            content: Section content (without section/end markers)
            after: If adding new section, place it after this section (default: at end)
        """
        existing = self.get_section(name)
        if existing:
            existing.content = content
        else:
            new_section = Section(name=name, content=content)
            if after:
                # Find position after the specified section
                for i, s in enumerate(self.sections):
                    if s.name == after:
                        self.sections.insert(i + 1, new_section)
                        return
            # Default: add at end
            self.sections.append(new_section)

    def remove_section(self, name: str) -> bool:
        """Remove a section by name.

        Args:
            name: Section name to remove

        Returns:
            True if section was found and removed, False if not found
        """
        for i, section in enumerate(self.sections):
            if section.name == name:
                self.sections.pop(i)
                return True
        return False

    def clear_section(self, name: str) -> bool:
        """Clear a section's content (keep the section but make it empty).

        Args:
            name: Section name to clear

        Returns:
            True if section was found and cleared, False if not found
        """
        section = self.get_section(name)
        if section:
            section.content = ""
            section.trailing_content = ""
            return True
        return False

    def comment_out_section(self, name: str, reason: str = "") -> bool:
        """Comment out all lines in a section.

        Args:
            name: Section name to comment out
            reason: Optional reason to add as comment at top (can be multi-line)

        Returns:
            True if section was found and commented, False otherwise
        """
        section = self.get_section(name)
        if not section:
            return False

        lines = section.content.split('\n')
        commented_lines = []

        if reason:
            # Handle multi-line reasons
            for reason_line in reason.split('\n'):
                commented_lines.append(f"-- {reason_line}")
            commented_lines.append("")

        for line in lines:
            if line.strip() and not line.strip().startswith('--'):
                commented_lines.append(f"-- {line}")
            else:
                commented_lines.append(line)

        section.content = '\n'.join(commented_lines)
        return True

    def append_in_section(self, name: str, content: str, assert_section_present : bool) -> bool:
        section = self.get_section(name)
        if not section and assert_section_present:
            raise ValueError(f"Section {name} not found")
        if not section:
            return False

        section.content = section.content + "\n\n" + content + "\n"
        return True

    def reconstruct_and_write_to_file(self,file_path: Path) -> str :
        content = self.reconstruct()
        Path(file_path).write_text(content)
        return content

    @classmethod
    def update_section_on_disk(cls, file_path: Path, section: str, content: str) -> str:
        """Read file, replace a section's content, write back, return new file content."""
        lf = cls.from_path(file_path)
        lf.add_or_replace_section(section, content)
        return lf.reconstruct_and_write_to_file(file_path)

    @classmethod
    def append_to_section_on_disk(cls, file_path: Path, section: str, content: str) -> str:
        """Read file, append to a section, write back, return new file content."""
        lf = cls.from_path(file_path)
        lf.append_in_section(section, content, assert_section_present=True)
        return lf.reconstruct_and_write_to_file(file_path)



def parse_lean_file_sections(content: str) -> LeanFile:
    """Parse a Lean file into prologue and top-level sections.

    This parser only extracts top-level `section ... end ...` blocks used by our
    file format, but it is nesting-aware so inner Lean `section` / `namespace`
    blocks do not prematurely terminate an outer top-level section.
    """
    def _block_name(stripped: str, keyword: str) -> str:
        return "" if stripped == keyword else stripped[len(keyword):].strip()

    def _is_section_start(stripped: str) -> bool:
        return stripped == 'section' or stripped.startswith('section ')

    def _nested_block_start_name(stripped: str) -> str | None:
        if _is_section_start(stripped):
            return _block_name(stripped, 'section')
        if stripped == 'namespace' or stripped.startswith('namespace '):
            return _block_name(stripped, 'namespace')
        return None

    def _end_block_name(stripped: str) -> str | None:
        if stripped == 'end' or stripped.startswith('end '):
            return _block_name(stripped, 'end')
        return None

    def _matches_open_block(end_name: str, open_name: str) -> bool:
        return end_name == '' or open_name == '' or end_name == open_name

    lines = content.split('\n')
    prologue_lines: list[str] = []
    sections: list[Section] = []
    i = 0

    while i < len(lines):
        line = lines[i]
        stripped = line.strip()
        if _is_section_start(stripped):
            break
        prologue_lines.append(line)
        i += 1

    while i < len(lines):
        line = lines[i]
        stripped = line.strip()
        if not _is_section_start(stripped):
            raise ValueError(
                f"Unexpected content outside section at line {i + 1}: {line!r}"
            )

        section_start_line = i + 1
        name = _block_name(stripped, 'section')
        content_start_line = i + 2
        i += 1

        section_lines: list[str] = []
        nested_blocks: list[str] = []
        end_line = -1

        while i < len(lines):
            line = lines[i]
            stripped = line.strip()

            nested_name = _nested_block_start_name(stripped)
            if nested_name is not None:
                nested_blocks.append(nested_name)
                section_lines.append(line)
                i += 1
                continue

            end_name = _end_block_name(stripped)
            if end_name is not None:
                if nested_blocks:
                    if _matches_open_block(end_name, nested_blocks[-1]):
                        nested_blocks.pop()
                    section_lines.append(line)
                    i += 1
                    continue

                if _matches_open_block(end_name, name):
                    end_line = i + 1
                    i += 1
                    break

            section_lines.append(line)
            i += 1

        if end_line == -1:
            raise ValueError(
                f"Section '{name}' starting at line {section_start_line} has no matching 'end {name}'"
            )

        trailing_lines: list[str] = []
        while i < len(lines):
            line = lines[i]
            stripped = line.strip()
            if _is_section_start(stripped):
                break
            if stripped == '' or stripped.startswith('--'):
                trailing_lines.append(line)
                i += 1
                continue
            raise ValueError(
                f"Unexpected content outside section at line {i + 1}: {line!r}"
            )

        sections.append(Section(
            name=name,
            content='\n'.join(section_lines),
            trailing_content='\n'.join(trailing_lines) if trailing_lines else "",
            start_line=section_start_line,
            content_start_line=content_start_line,
            end_line=end_line,
        ))

    return LeanFile(
        prologue='\n'.join(prologue_lines),
        sections=sections,
    )


# --- Test Case Parsing ---

@dataclass
class VelvetTestCase:
    """A single test case with inputs and expected outputs.

    Naming convention:
    - test<N>_<param_name>: input value for param
    - test<N>_Expected: expected return value
    - test<N>_Expected_<param_name>: expected value for mutated param
    """
    id: int  # e.g., 1
    inputs: Dict[str, str]  # param_name -> value
    expected_return: Optional[str]  # Expected return value
    expected_mutations: Dict[str, str]  # param_name -> expected mutated value

    @property
    def name(self) -> str:
        """Get test case name (e.g., 'test1')."""
        return f"test{self.id}"

    def __str__(self) -> str:
        return self.name


def parse_test_cases(content: str, method: VelvetMethod) -> List[VelvetTestCase]:
    """Parse test cases from VelvetTestCases section content.

    Args:
        content: The content of the VelvetTestCases section
        method: The VelvetMethod to understand parameter names

    Returns:
        List of VelvetTestCase objects grouped by test number
    """
    from utils.lean_proof_parser import extract_declarations, LeanDef

    # Extract all definitions
    decls = extract_declarations(content)
    defs = [d for d in decls if isinstance(d, LeanDef) and d.kind == 'def']

    # Pattern to match test case definitions: test<N>_<suffix>
    test_pattern = re.compile(r'^(test\d+)_(.+)$')

    # Group definitions by test name
    test_groups: Dict[str, Dict[str, str]] = {}

    for d in defs:
        match = test_pattern.match(d.name)
        if match:
            test_name = match.group(1)  # e.g., "test1"
            suffix = match.group(2)  # e.g., "a", "Expected", "Expected_a"

            if test_name not in test_groups:
                test_groups[test_name] = {}

            # Extract the value (everything after :=)
            value_match = re.search(r':=\s*(.+)$', d.content, re.DOTALL)
            value = value_match.group(1).strip() if value_match else ""

            test_groups[test_name][suffix] = value

    # Get param names from method
    param_names = [p.name for p in method.params]
    mutable_params = [p.name for p in method.params if p.is_mut]

    # Build VelvetTestCase objects
    test_cases = []
    
    def extract_test_id(test_name: str) -> int:
        """Extract numeric test ID from test name (e.g., 'test1' -> 1)."""
        match = re.search(r'\d+', test_name)
        assert match is not None, f"Could not extract test ID from {test_name}"
        return int(match.group())
    
    for test_name in sorted(test_groups.keys(), key=extract_test_id):
        group = test_groups[test_name]
        test_id = extract_test_id(test_name)

        # Extract inputs (param values)
        inputs = {}
        for param_name in param_names:
            if param_name in group:
                inputs[param_name] = group[param_name]

        # Extract expected return
        expected_return = group.get('Expected')

        # Extract expected mutations (Expected_<param_name>)
        expected_mutations = {}
        for param_name in mutable_params:
            key = f'Expected_{param_name}'
            if key in group:
                expected_mutations[param_name] = group[key]

        test_cases.append(VelvetTestCase(
            id=test_id,
            inputs=inputs,
            expected_return=expected_return,
            expected_mutations=expected_mutations
        ))

    return test_cases
