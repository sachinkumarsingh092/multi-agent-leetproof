import re
from dataclasses import dataclass, field
from typing import List, Optional, Union, Tuple, Callable
from enum import Enum
from parsy import generate, regex, string, any_char

# Note: _parse_have_statement imported lazily in parse_proof_lines to avoid circular import

# --- Enums ---

class LeanBinderKind(str, Enum):
    EXPLICIT = "explicit"
    IMPLICIT = "implicit"
    STRICT_IMPLICIT = "strict_implicit"
    INST_IMPLICIT = "inst_implicit"

class LeanTheoremKind(str, Enum):
    THEOREM = "theorem"
    LEMMA = "lemma"
    DEF = "def"
    EXAMPLE = "example"
    INSTANCE = "instance"

# --- Data Structures ---

@dataclass
class LeanBinder:
    names: List[str]
    type_expr: str
    kind: LeanBinderKind = LeanBinderKind.EXPLICIT

    def __str__(self):
        names_str = " ".join(self.names)
        if self.kind == LeanBinderKind.EXPLICIT:
            return f"({names_str} : {self.type_expr})"
        elif self.kind == LeanBinderKind.IMPLICIT:
            return f"{{{names_str} : {self.type_expr}}}"
        elif self.kind == LeanBinderKind.STRICT_IMPLICIT:
            return "{{" + f" {names_str} : {self.type_expr} " + "}}"
        elif self.kind == LeanBinderKind.INST_IMPLICIT:
            if not self.type_expr:
                return f"[{names_str}]"
            return f"[{names_str} : {self.type_expr}]"
        
        # Fallback (should cover explicit)
        if not self.type_expr:
            return f"({names_str})"
        return f"({names_str} : {self.type_expr})"

@dataclass(kw_only=True)
class LeanProofStep:
    content: str
    indent: int = 0

@dataclass
class LeanProof:
    is_by: bool = False
    is_inline: bool = False
    tactics: List[LeanProofStep] = field(default_factory=list)
    term: Optional[str] = None
    
    def __str__(self):
        if not self.is_by:
            return self.term if self.term else ""
        
        lines = []
        for t in self.tactics:
            lines.append(str(t))
        return "\n".join(lines)

@dataclass(kw_only=True)
class LeanHaveDecl(LeanProofStep):
    name: str
    type_expr: str
    proof: Optional[LeanProof] = None
    prefix: str = ""
    
    def __str__(self):
        proof_str = str(self.proof) if self.proof else ""
        
        sep = " "
        if self.proof and self.proof.is_by:
             if self.proof.is_inline:
                 sep = " := by "
             else:
                 sep = " := by\n"
             proof_str = str(self.proof)
        else:
             sep = " := "
        
        indent_str = " " * self.indent
        return f"{indent_str}{self.prefix}have {self.name} : {self.type_expr} :={sep}{proof_str}"

@dataclass(kw_only=True)
class LeanLetDecl(LeanProofStep):
    name: str
    value: str 
    prefix: str = ""
    
    def __str__(self):
        indent_str = " " * self.indent
        return f"{indent_str}{self.prefix}let {self.name} := {self.value}"

@dataclass(kw_only=True)
class LeanTactic(LeanProofStep):
    def __str__(self):
        indent_str = " " * self.indent
        return f"{indent_str}{self.content}"

@dataclass
class LeanTheorem:
    name: str
    params: List[LeanBinder]
    return_type: Optional[str]
    proof: Optional[LeanProof] = None # Optional proof
    modifiers: List[str] = field(default_factory=list) 
    kind: LeanTheoremKind = LeanTheoremKind.THEOREM

    def __str__(self):
        params_str = " ".join(str(p) for p in self.params)
        ret_part = f" : {self.return_type}" if self.return_type else ""
        
        # Reconstruct base signature: "kind name (params) : return_type"
        base_signature = f"{self.kind.value} {self.name}"
        if params_str: # Add space only if params_str is not empty
            base_signature += f" {params_str}"
        base_signature += ret_part # ret_part already includes leading space if needed
        
        if not self.proof:
            return base_signature
        
        proof_part = str(self.proof)
        sep = " := "
        if self.proof.is_by:
            if self.proof.is_inline:
                sep = " := by "
            else:
                sep = " := by\n"
        
        return f"{base_signature}{sep}{proof_part}"

@dataclass
class LeanDef:
    name: str
    kind: str # def, abbrev
    content: str
    
    def __str__(self):
        return self.content

# --- Parsers ---

newline = regex(r'\n')
whitespace_no_newline = regex(r'[ \t]+')
optional_whitespace_no_newline = regex(r'[ \t]*')
comment_single = regex(r'--[^\n]*')
comment_multi = regex(r'/-(?:[^-]|-+(?!/))*-+/')
ws_with_comments = regex(r'(\s|--[^\n]*|/-(?:[^-]|-+(?!/))*-+/)+')

# Supports dotted names like Foo.Bar.baz
identifier = regex(r"[a-zA-Z_][a-zA-Z0-9_']*(?:\.[a-zA-Z_][a-zA-Z0-9_']*)*")

@generate
def generic_binder():
    yield ws_with_comments.optional()
    
    start_marker = yield regex(r'{{|[\(\[{]')
    
    kind = LeanBinderKind.EXPLICIT
    end_marker = ")"
    if start_marker == '(': 
        kind = LeanBinderKind.EXPLICIT
        end_marker = ")"
    elif start_marker == '{':
        kind = LeanBinderKind.IMPLICIT
        end_marker = "}"
    elif start_marker == '[':
        kind = LeanBinderKind.INST_IMPLICIT
        end_marker = "]"
    elif start_marker == '{{':
        kind = LeanBinderKind.STRICT_IMPLICIT
        end_marker = "}}"
        
    content_chars = []
    stack = [] 
    
    while True:
        c = yield any_char
        
        if not stack:
            if kind == LeanBinderKind.STRICT_IMPLICIT:
                if c == '}' and content_chars and content_chars[-1] == '}':
                    content_chars.pop() 
                    break
            elif c == end_marker:
                break
        
        content_chars.append(c)

        # Skip Lean character/string literals so inner brackets don't corrupt the stack.
        if c in ("'", '"'):
            closing = c
            while True:
                nc = yield any_char
                content_chars.append(nc)
                if nc == '\\':          # escape sequence — consume one more char
                    nc2 = yield any_char
                    content_chars.append(nc2)
                elif nc == closing:
                    break
            continue

        if c in '({[':
            stack.append(c)
        elif c in ')}]':
            if stack:
                if (c == ')' and stack[-1] == '(') or \
                   (c == '}' and stack[-1] == '{') or \
                   (c == ']' and stack[-1] == '['):
                    stack.pop()
    
    content_str = "".join(content_chars)
    
    if ':' in content_str:
        colon_idx = -1
        depth = 0
        for i, char in enumerate(content_str):
            if char in '({[': depth += 1
            elif char in ')}]': depth -= 1
            elif char == ':' and depth == 0:
                colon_idx = i
                break
        
        if colon_idx != -1:
            names_part = content_str[:colon_idx].strip()
            type_part = content_str[colon_idx+1:].strip()
            names = names_part.split()
            return LeanBinder(names, type_part, kind)
    
    return LeanBinder([content_str.strip()], "", kind)

@generate
def theorem_signature():
    yield ws_with_comments.optional()
    
    # Skip modifiers and attributes
    modifier = regex(r'\b(private|protected|noncomputable|unsafe|partial|scoped|local)\b')
    attribute = regex(r'@\[[^\]]*\]')
    yield (modifier | attribute | ws_with_comments).many()
    
    kind_str = yield string("theorem") | string("lemma") | string("def") | string("example") | string("instance")
    kind = LeanTheoremKind(kind_str)
    
    yield ws_with_comments
    
    name = yield identifier
    
    # Optional universe params (e.g. .{u})
    univ = yield regex(r'\.[^}]+\}').optional()
    if univ:
        name += univ
    
    params = yield generic_binder.many()

    yield ws_with_comments.optional()

    return_type = None

    # First try to match := directly (def without explicit return type)
    # e.g., "def foo (x : Nat) := ..."
    assign = yield string(':=').optional()

    if not assign:
        # No direct :=, so we expect ": <return_type> :="
        # e.g., "def foo (x : Nat) : Nat := ..." or "theorem bar : Prop := ..."
        yield string(':')
        yield ws_with_comments.optional()
        type_chars = []
        while True:
            c = yield any_char
            if c == ':':
                # Check if this is the := delimiter
                equals_char = yield string('=').optional()
                if equals_char:
                    # Found ':=' - end of return type
                    break
                else:
                    # Just a ':' inside the type (e.g., in a dependent type)
                    type_chars.append(c)
            else:
                type_chars.append(c)

        return_type = "".join(type_chars).strip()

    return LeanTheorem(name, params, return_type, None, kind=kind)

# --- Proof Parsing Logic ---

def parse_proof_lines(lines: List[str], current_idx: int, base_indent: int = -1, is_inline: bool = False) -> Tuple[LeanProof, int]:
    """
    Parses a proof block starting from current_idx.
    Consumes lines as long as they are indented > base_indent (or same indent for the block elements).
    """
    proof = LeanProof(is_by=True, is_inline=is_inline)
    i = current_idx
    
    if i >= len(lines):
        return proof, i

    # Determine block indentation from first relevant line
    while i < len(lines):
        line = lines[i]
        if not line.strip() or line.strip().startswith("--"):
             # Keep comments/empty lines
             cur_len = len(line) - len(line.lstrip())
             proof.tactics.append(LeanTactic(content=line.strip(), indent=cur_len))
             i += 1
             continue
        break
    
    if i >= len(lines):
        return proof, i
        
    first_line = lines[i]
    first_indent_len = len(first_line) - len(first_line.lstrip())
    
    if base_indent != -1 and first_indent_len <= base_indent:
        # End of block
        return proof, i
        
    block_indent = first_indent_len
    
    while i < len(lines):
        line = lines[i]
        stripped = line.strip()
        current_indent_len = len(line) - len(line.lstrip())
        
        if not stripped or stripped.startswith("--"):
            proof.tactics.append(LeanTactic(content=stripped, indent=current_indent_len))
            i += 1
            continue

        if current_indent_len < block_indent:
            # End of block
            break
            
        # Check for 'have'
        # We look for "have "
        if 'have ' in line:
            # verify it's a have statement
            have_pos = line.find('have ')
            if (have_pos == 0 or not line[have_pos-1].isalnum()) and \
               (have_pos + 4 >= len(line) or not line[have_pos+4].isalnum()):
                
                # Use _parse_have_statement logic (lazy import to avoid circular dependency)
                from utils.lean_helpers import _parse_have_statement
                decl_str, next_i = _parse_have_statement(lines, i)
                
                if decl_str:
                    # decl_str is like "have h : T"
                    # We need to parse this string to get name and type
                    # Assumes "have name : type"
                    
                    # Capture prefix (bullets)
                    # line is like "   · have ..."
                    # have_pos is index of 'have'
                    # indent is "   " (len 3)
                    # prefix is "· "
                    prefix = line[current_indent_len:have_pos]
                    
                    # Split 'have'
                    # Remove 'have ' prefix
                    inner = decl_str[5:].strip()
                    if ':' in inner:
                        name_part, type_part = inner.split(':', 1)
                        name = name_part.strip()
                        type_part = type_part.strip()
                        
                        # Now parse the proof.
                        # The proof is in lines[i...next_i] roughly?
                        # _parse_have_statement scans until the end of the proof block.
                        # We need to find where the declaration ended (at :=) inside the original lines
                        # to know where the proof starts.
                        
                        # This is tricky because _parse_have_statement logic is internal.
                        # But we know the proof ends at next_i.
                        # And the proof starts after ':=', which might be on line 'i' or subsequent.
                        
                        # Let's search for := starting from i
                        proof_start_line_idx = i
                        found_assign = False
                        
                        # Scan lines to find :=
                        for k in range(i, next_i):
                            l = lines[k]
                            if ':=' in l:
                                # Found it.
                                # Check if 'by' is after it
                                parts = l.split(':=', 1)
                                after_assign = parts[1].strip()
                                
                                # If after_assign starts with 'by', then the proof is 'by ...'
                                # If it's empty, maybe next line?
                                
                                proof_start_line_idx = k
                                found_assign = True
                                break
                        
                        if found_assign:
                            # Proof is from proof_start_line_idx (partial) to next_i
                            # We'll recursively parse
                            # But we need to handle the content on the same line as :=
                            
                            sub_lines = lines[proof_start_line_idx:next_i]
                            
                            is_inline_sub = False
                            
                            if ':=' in sub_lines[0]:
                                pre, post = sub_lines[0].split(':=', 1)
                                
                                stripped_post = post.strip()
                                if stripped_post == 'by':
                                     # Proof starts on next line
                                     sub_lines[0] = "" 
                                elif stripped_post.startswith('by '):
                                     # '... := by tactic'
                                     by_match = re.search(r'by\s+', post)
                                     if by_match:
                                         is_inline_sub = True
                                         # Remove 'by ' prefix to normalize indentation
                                         sub_lines[0] = post[by_match.end():]
                                     else:
                                         # fallback
                                         sub_lines[0] = " " * (len(pre) + 2) + post
                                else:
                                     # '... := term'
                                     sub_lines[0] = " " * (len(pre) + 2) + post
                            
                            # Recursively parse
                            sub_proof, _ = parse_proof_lines(sub_lines, 0, -1, is_inline=is_inline_sub)
                            
                            proof.tactics.append(LeanHaveDecl(
                                content=decl_str, # fallback
                                indent=current_indent_len,
                                name=name,
                                type_expr=type_part,
                                proof=sub_proof,
                                prefix=prefix
                            ))
                            
                            i = next_i
                            continue

                # If parsing failed or not a valid have block, fall through
        
        if 'let ' in line:
             let_pos = line.find('let ')
             if (let_pos == 0 or not line[let_pos-1].isalnum()):
                 # It's a let
                 prefix = line[current_indent_len:let_pos]
                 content = line[let_pos+4:]
                 if ':=' in content:
                     lhs, rhs = content.split(':=', 1)
                     proof.tactics.append(LeanLetDecl(
                         content=line.strip(),
                         indent=current_indent_len,
                         name=lhs.strip(),
                         value=rhs.strip(),
                         prefix=prefix
                     ))
                     i += 1
                     continue
        
        # Default: treat as tactic
        proof.tactics.append(LeanTactic(content=stripped, indent=current_indent_len))
        i += 1
        
    return proof, i

def parse_lean_theorem(text: str) -> LeanTheorem:
    # 1. Parse signature
    try:
        theorem_part, remainder = theorem_signature.parse_partial(text)
    except Exception as e:
        raise ValueError(f"Failed to parse theorem signature: {e}")
    
    # remainder = remainder.strip() # Removed to preserve whitespace

    if isinstance(remainder, str) and remainder.lstrip().startswith("by"):
        # Tactic proof
        proof_lines = remainder.splitlines()
        
        # Handle 'by' on the first line
        stripped_first = proof_lines[0].strip()
        start_idx = 0
        is_inline_proof = False
        
        match = re.match(r'^\s*by\s+', proof_lines[0])
        
        if stripped_first == 'by':
            start_idx = 1
        elif match:
            # ' by tactic' -> replace ' by ' with spaces to preserve relative indentation
            is_inline_proof = True
            end_by = match.end()
            proof_lines[0] = proof_lines[0][end_by:]
            
        proof_obj, _ = parse_proof_lines(proof_lines, start_idx, -1, is_inline=is_inline_proof)
        theorem_part.proof = proof_obj
        
    else:
        # Term proof
        term_str = remainder.strip() if isinstance(remainder, str) else str(remainder).strip()
        theorem_part.proof = LeanProof(is_by=False, term=term_str)
    
    return theorem_part

def strip_comments(text: str) -> str:
    # Remove multiline comments /- ... -/
    text = re.sub(r'/-[\s\S]*?-/', '', text)
    # Remove single line comments -- ...
    text = re.sub(r'--.*', '', text)
    return text.strip()

ALLOWED_KEYWORDS = {
    'def', 'abbrev', 'theorem', 'lemma', 'example', 'instance', 'structure', 
    'class', 'inductive', 'section', 'namespace', 'end', 'variable', 
    'universe', 'axiom', 'constant', 'open', 'import', 'set_option'
}

def extract_declarations(text: str) -> List[Union[LeanTheorem, LeanDef]]:
    """
    Extracts definitions and theorem signatures from Lean code, ignoring other commands.
    
    Args:
        text: Full Lean file content.
        
    Returns:
        List of parsed objects (LeanTheorem or LeanDef).
    """
    modifiers_pattern = r"(?:private|protected|noncomputable|partial|unsafe|scoped|local|rec)"
    
    # Construct regex from allowed keywords + method (to ensure segmentation)
    # Sort by length desc to ensure longest match
    all_keywords = ALLOWED_KEYWORDS | {'method'}
    sorted_keywords = sorted(list(all_keywords), key=len, reverse=True)
    keywords_pattern = "|".join(str(kw) for kw in sorted_keywords)
    
    # Regex to find start of declarations
    # Group 1: The full match of the preamble (docs, attrs, mods)
    # Group 2: The keyword OR Hash command OR Unknown (col 0)
    keyword_regex = re.compile(
        r"(?m)" 
        r"(?:"
            # Option 1: Allowed keywords (can be indented)
            r"^\s*("
                r"(?:/--[\s\S]*?-/\s*)?" # Optional doc comment
                r"(?:@\[[^\]]*\]\s*)?" # Optional attributes
                r"(?:" + modifiers_pattern + r"\s+)*" # Optional modifiers
                r"(?P<keyword>" + keywords_pattern + r")" 
            r")\b"
        r"|"
            # Option 2: Any identifier at column 0 (catch-all for unknown top-level blocks)
            # This handles 'unknown_command' and others not in keywords_pattern
            r"^"
            r"(?:"
                r"(?:/--[\s\S]*?-/\s*)?" 
                r"(?:@\[[^\]]*\]\s*)?" 
                r"(?:" + modifiers_pattern + r"\s+)*" 
                r"(?P<unknown>[a-zA-Z_]\w*)" 
            r")\b"
        r"|"
            # Option 3: Hash command
            r"^\s*(?P<hash>#[a-zA-Z_]\w*)\b"
        r")"
    )
    
    matches = list(keyword_regex.finditer(text))
    results = []
    
    for i, match in enumerate(matches):
        keyword = match.group('keyword')
        unknown = match.group('unknown')
        hash_cmd = match.group('hash')
        
        if hash_cmd:
            continue
            
        if unknown:
            continue
            
        # If we are here, 'keyword' group matched.
        # It must be in allowed keywords.
        if keyword not in ALLOWED_KEYWORDS:
            continue
        
        # Extract block
        start_idx = match.start()
        
        if i + 1 < len(matches):
            end_idx = matches[i+1].start()
        else:
            end_idx = len(text)
            
        block_text = text[start_idx:end_idx]
        
        # Clean comments
        clean_block = strip_comments(block_text)
        if not clean_block:
            continue
            
        if keyword in ['def', 'abbrev']:
            # Extract name using regex from block_text (after keyword)
            name_match = re.search(fr"\b{keyword}\s+(?P<name>[a-zA-Z0-9_.]+)", clean_block)
            name = name_match.group('name') if name_match else "<unknown>"
            results.append(LeanDef(name=name, kind=keyword, content=clean_block))

        elif keyword in ['theorem', 'lemma']:
            try:
                # Use parse_lean_theorem to get full theorem including proof
                lean_theorem = parse_lean_theorem(clean_block)
                results.append(lean_theorem)
            except Exception:
                pass
                
    return results

def parse_lean_decls[T](content: str, filter_map: Callable[[Union[LeanTheorem, LeanDef]], Optional[T]] = (lambda node: node) ) -> List[T] :
    """
    Parses Lean content, extracts declarations, and applies a filter/map function.
    
    Args:
        content: The Lean file content.
        filter_map: A function that takes a declaration node and returns a string (to include)
                    or default (identity function)
                    
    Returns:
        The processed list of nodes
    """
    declarations = extract_declarations(content)
    result_decls: List[T] = []
    
    for decl in declarations:
        result = filter_map(decl)
        if result is not None:
            result_decls.append(result)
            
    return result_decls
