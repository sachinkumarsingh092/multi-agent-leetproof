import decimal
import pytest
import textwrap
from utils.lean_proof_parser import parse_lean_theorem, extract_declarations, parse_lean_decls, LeanTheorem, LeanHaveDecl, LeanLetDecl, LeanTactic, LeanProof, LeanBinder, LeanBinderKind, LeanTheoremKind, LeanDef

def test_cases_hierarchical():
    code = """
    theorem cases_hierarchical (n : ℕ) : n = 0 ∨ n > 0 := by
      cases' n with k
      · have h1 : 0 = 0 := by rfl
        have h2 : 0 = 0 ∨ 0 > 0 := by
          left
          exact h1
        exact h2
      · have h3 : Nat.succ k > 0 := by
          exact Nat.succ_pos k
        have h4 : Nat.succ k = 0 ∨ Nat.succ k > 0 := by
          right
          exact h3
        exact h4
    """
    parsed = parse_lean_theorem(code)
    
    expected = LeanTheorem(
        name='cases_hierarchical', 
        params=[LeanBinder(names=['n'], type_expr='ℕ', kind=LeanBinderKind.EXPLICIT)], 
        return_type='n = 0 ∨ n > 0', 
        proof=LeanProof(is_by=True, is_inline=False, tactics=[
            LeanTactic(content="cases' n with k", indent=6), 
            LeanHaveDecl(content='have h1 : 0 = 0', indent=6, name='h1', type_expr='0 = 0', proof=LeanProof(is_by=True, is_inline=True, tactics=[
                LeanTactic(content='rfl', indent=0) 
            ]), prefix='· '), 
            LeanHaveDecl(content='have h2 : 0 = 0 ∨ 0 > 0', indent=8, name='h2', type_expr='0 = 0 ∨ 0 > 0', proof=LeanProof(is_by=True, is_inline=False, tactics=[
                LeanTactic(content='', indent=0), 
                LeanTactic(content='left', indent=10), 
                LeanTactic(content='exact h1', indent=10)
            ]), prefix=''), 
            LeanTactic(content='exact h2', indent=8), 
            LeanHaveDecl(content='have h3 : Nat.succ k > 0', indent=6, name='h3', type_expr='Nat.succ k > 0', proof=LeanProof(is_by=True, is_inline=False, tactics=[
                LeanTactic(content='', indent=0), 
                LeanTactic(content='exact Nat.succ_pos k', indent=10)
            ]), prefix='· '), 
            LeanHaveDecl(content='have h4 : Nat.succ k = 0 ∨ Nat.succ k > 0', indent=8, name='h4', type_expr='Nat.succ k = 0 ∨ Nat.succ k > 0', proof=LeanProof(is_by=True, is_inline=False, tactics=[
                LeanTactic(content='', indent=0), 
                LeanTactic(content='right', indent=10), 
                LeanTactic(content='exact h3', indent=10)
            ]), prefix=''), 
            LeanTactic(content='exact h4', indent=8), 
            LeanTactic(content='', indent=4) 
        ]), 
        kind=LeanTheoremKind.THEOREM
    )
    
    assert parsed == expected

def test_simple_theorem():
    code = "theorem simple (p q : Prop) (hp : p) : p := by exact hp"
    parsed = parse_lean_theorem(code)
    
    expected = LeanTheorem(
        name="simple",
        params=[
            LeanBinder(names=["p", "q"], type_expr="Prop", kind=LeanBinderKind.EXPLICIT),
            LeanBinder(names=["hp"], type_expr="p", kind=LeanBinderKind.EXPLICIT)
        ],
        return_type="p",
        proof=LeanProof(
            is_by=True,
            is_inline=True,
            tactics=[
                LeanTactic(content="exact hp", indent=0)
            ]
        ),
        kind=LeanTheoremKind.THEOREM
    )
    
    assert parsed == expected

def test_term_proof():
    code = "theorem term_proof (x : Nat) : Nat := x"
    parsed = parse_lean_theorem(code)
    
    expected = LeanTheorem(
        name="term_proof",
        params=[LeanBinder(names=["x"], type_expr="Nat", kind=LeanBinderKind.EXPLICIT)],
        return_type="Nat",
        proof=LeanProof(is_by=False, term="x"),
        kind=LeanTheoremKind.THEOREM
    )
    
    assert parsed == expected

def test_implicit_params():
    code = "theorem implicit {α : Type} [Inhabited α] (x : α) : x = x := by rfl"
    parsed = parse_lean_theorem(code)
    
    expected = LeanTheorem(
        name="implicit",
        params=[
            LeanBinder(names=["α"], type_expr="Type", kind=LeanBinderKind.IMPLICIT),
            LeanBinder(names=["Inhabited α"], type_expr="", kind=LeanBinderKind.INST_IMPLICIT),
            LeanBinder(names=["x"], type_expr="α", kind=LeanBinderKind.EXPLICIT)
        ],
        return_type="x = x",
        proof=LeanProof(is_by=True, is_inline=True, tactics=[
            LeanTactic(content="rfl", indent=0)
        ]),
        kind=LeanTheoremKind.THEOREM
    )
    assert parsed == expected

def test_let_binding():
    code = """
    theorem let_test : Nat := by
      let x := 5
      let y : Nat := 10
      exact x + y
    """
    parsed = parse_lean_theorem(code)
    
    expected = LeanTheorem(
        name="let_test",
        params=[],
        return_type="Nat",
        proof=LeanProof(is_by=True, is_inline=False, tactics=[
            LeanLetDecl(content="let x := 5", indent=6, name="x", value="5", prefix=""),
            LeanLetDecl(content="let y : Nat := 10", indent=6, name="y : Nat", value="10", prefix=""),
            LeanTactic(content="exact x + y", indent=6),
            LeanTactic(content="", indent=4)
        ]),
        kind=LeanTheoremKind.THEOREM
    )
    assert parsed == expected

def test_nested_have():
    code = """
    theorem nested : True := by
      have h1 : True := by
        have h2 : True := by trivial
        exact h2
      exact h1
    """
    parsed = parse_lean_theorem(code)
    
    expected = LeanTheorem(
        name="nested",
        params=[],
        return_type="True",
        proof=LeanProof(is_by=True, is_inline=False, tactics=[
            LeanHaveDecl(
                content="have h1 : True",
                indent=6,
                name="h1",
                type_expr="True",
                prefix="",
                proof=LeanProof(is_by=True, is_inline=False, tactics=[
                    LeanTactic(content="", indent=0), # Newline after := by
                    LeanHaveDecl(
                        content="have h2 : True",
                        indent=8,
                        name="h2",
                        type_expr="True",
                        prefix="",
                        proof=LeanProof(is_by=True, is_inline=True, tactics=[
                            LeanTactic(content="trivial", indent=0) # Inline!
                        ])
                    ),
                    LeanTactic(content="exact h2", indent=8)
                ])
            ),
            LeanTactic(content="exact h1", indent=6),
            LeanTactic(content="", indent=4) # Trailing newline
        ]),
        kind=LeanTheoremKind.THEOREM
    )
    assert parsed == expected

def test_lemma_keyword():
    code = "lemma my_lemma (p : Prop) : p → p := fun h => h"
    parsed = parse_lean_theorem(code)
    expected = LeanTheorem(
        name="my_lemma",
        params=[LeanBinder(names=["p"], type_expr="Prop", kind=LeanBinderKind.EXPLICIT)],
        return_type="p → p",
        proof=LeanProof(is_by=False, term="fun h => h"),
        kind=LeanTheoremKind.LEMMA
    )
    assert parsed == expected

def test_universe_param():
    code = "theorem universe_poly.{u} {α : Type u} (a : α) : a = a := rfl"
    parsed = parse_lean_theorem(code)
    expected = LeanTheorem(
        name="universe_poly.{u}",
        params=[
            LeanBinder(names=["α"], type_expr="Type u", kind=LeanBinderKind.IMPLICIT),
            LeanBinder(names=["a"], type_expr="α", kind=LeanBinderKind.EXPLICIT)
        ],
        return_type="a = a",
        proof=LeanProof(is_by=False, term="rfl"),
        kind=LeanTheoremKind.THEOREM
    )
    assert parsed == expected

def test_modifiers():
    code = "private noncomputable def my_def : Nat := 5"
    parsed = parse_lean_theorem(code)
    expected = LeanTheorem(
        name="my_def",
        params=[],
        return_type="Nat",
        proof=LeanProof(is_by=False, term="5"),
        kind=LeanTheoremKind.DEF
    )
    assert parsed == expected

def test_comments():
    code = """
    /- This is a file-level multi-line comment -/
    
    -- This is a single-line comment before the theorem
    private theorem my_theorem (n : Nat) : n = n := by
      -- This is a comment inside the proof block
      /- This is another multi-line comment -/
      rfl -- Tactic comment
    """
    parsed = parse_lean_theorem(code)
    
    expected = LeanTheorem(
        name="my_theorem",
        params=[LeanBinder(names=["n"], type_expr="Nat", kind=LeanBinderKind.EXPLICIT)],
        return_type="n = n",
        proof=LeanProof(is_by=True, is_inline=False, tactics=[
            LeanTactic(content="-- This is a comment inside the proof block", indent=6),
            LeanTactic(content="/- This is another multi-line comment -/", indent=6),
            LeanTactic(content="rfl -- Tactic comment", indent=6),
            LeanTactic(content="", indent=4)
        ]),
        kind=LeanTheoremKind.THEOREM
    )
    assert parsed == expected

def test_calc_block():
    code = """
    theorem calc_test (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
      calc
        a = b := h1
        _ = c := h2
    """
    parsed = parse_lean_theorem(code)
    expected = LeanTheorem(
        name="calc_test",
        params=[
             LeanBinder(names=["a", "b", "c"], type_expr="Nat", kind=LeanBinderKind.EXPLICIT),
             LeanBinder(names=["h1"], type_expr="a = b", kind=LeanBinderKind.EXPLICIT),
             LeanBinder(names=["h2"], type_expr="b = c", kind=LeanBinderKind.EXPLICIT)
        ],
        return_type="a = c",
        proof=LeanProof(is_by=True, is_inline=False, tactics=[
            LeanTactic(content="calc", indent=6),
            LeanTactic(content="a = b := h1", indent=8),
            LeanTactic(content="_ = c := h2", indent=8),
            LeanTactic(content="", indent=4)
        ]),
        kind=LeanTheoremKind.THEOREM
    )
    assert parsed == expected

def test_conv_block():
    code = """
    theorem conv_test (a b : Nat) : a + b = b + a := by
      conv =>
        lhs
        rw [Nat.add_comm]
    """
    parsed = parse_lean_theorem(code)
    expected = LeanTheorem(
        name="conv_test",
        params=[LeanBinder(names=["a", "b"], type_expr="Nat", kind=LeanBinderKind.EXPLICIT)],
        return_type="a + b = b + a",
        proof=LeanProof(is_by=True, is_inline=False, tactics=[
            LeanTactic(content="conv =>", indent=6),
            LeanTactic(content="lhs", indent=8),
            LeanTactic(content="rw [Nat.add_comm]", indent=8),
            LeanTactic(content="", indent=4)
        ]),
        kind=LeanTheoremKind.THEOREM
    )
    assert parsed == expected

def test_extract_declarations():
    code = """def foo : Nat := 1

method bar (x : Nat) : Nat :=
  x + 1

/-- Doc comment -/
@[simp]
theorem baz (p : Prop) : p → p := by
  intro h
  exact h

abbrev qux := foo
"""
    results = extract_declarations(code)
    names = [d.name for d in results]
    assert "foo" in names
    assert "qux" in names
    assert "baz" in names
    assert "bar" not in names
    
    foo = next(d for d in results if d.name == "foo")
    assert isinstance(foo, LeanDef)
    assert foo.kind == "def"
    assert "def foo : Nat := 1" in foo.content
    
    baz = next(d for d in results if d.name == "baz")
    assert isinstance(baz, LeanTheorem)
    assert baz.proof is not None
    assert baz.proof.is_by is True
    assert len(baz.proof.tactics) == 2
    assert baz.proof.tactics[0].content == "intro h"
    assert baz.proof.tactics[1].content == "exact h"

def test_extract_declarations_complex():
    code = """/-- Doc comment for structure -/
structure MyStruct where
  field : Nat

private def helper : Nat := 0

/--
  Multi-line doc comment
-/
@[simp]
lemma my_lemma (x : Nat) : x + 0 = x := by
  rw [Nat.add_zero]

-- Comment for skipped example
example : 1 = 1 := rfl

section
  variable (x : Nat)
  
  noncomputable def hard_def : Nat := 
    match x with
    | 0 => 1
    | _ => 2

  theorem inside_section : True := trivial
end

@[inline] abbrev alias := helper
"""
    results = extract_declarations(code)
    names = [d.name for d in results]
    
    assert "helper" in names
    assert "my_lemma" in names
    assert "hard_def" in names
    assert "inside_section" in names
    assert "alias" in names
    assert "MyStruct" not in names
    assert "example" not in names
    
    helper = next(d for d in results if d.name == "helper")
    assert isinstance(helper, LeanDef)
    assert "private def helper : Nat := 0" in helper.content
    
    my_lemma = next(d for d in results if d.name == "my_lemma")
    assert isinstance(my_lemma, LeanTheorem)
    assert my_lemma.proof is not None
    assert my_lemma.proof.is_by is True
    assert len(my_lemma.proof.tactics) == 1
    assert my_lemma.proof.tactics[0].content == "rw [Nat.add_zero]"
    
    hard_def = next(d for d in results if d.name == "hard_def")
    assert isinstance(hard_def, LeanDef)
    assert "match x with" in hard_def.content

def test_extract_declarations_refined():
    code = """
#eval 1 + 1

def good_def : Nat := 1

method bad_method : Nat := 2

/-- Doc comment -/
@[simp]
theorem good_theorem (p : Prop) : p → p := by
  -- Internal comment
  intro h
  exact h

#check good_def

abbrev good_abbrev := good_def

unknown_command foo

-- Top level comment
"""
    results = extract_declarations(code)
    names = [d.name for d in results]
    
    assert "good_def" in names
    assert "good_abbrev" in names
    assert "good_theorem" in names
    assert "bad_method" not in names
    assert "foo" not in names
    
    # Check content preservation including proof
    good_theorem = next(d for d in results if d.name == "good_theorem")
    assert isinstance(good_theorem, LeanTheorem)
    assert good_theorem.proof is not None
    assert good_theorem.proof.is_by is True
    # Tactics include comment (stripped), intro h, exact h
    tactic_contents = [t.content for t in good_theorem.proof.tactics]
    assert "intro h" in tactic_contents
    assert "exact h" in tactic_contents

def test_parse_lean_decls():
    code = """
def keep_me : Nat := 1
def drop_me : Nat := 2
theorem keep_thm : True := by trivial
theorem drop_thm : False := sorry
"""
    
    def my_filter(node):
        if node.name.startswith("drop"):
            return None
        if isinstance(node, LeanTheorem):
            # Custom formatting for theorems
            node.proof = LeanProof(
                is_by=True,          
                is_inline=True,     
                tactics=[LeanTactic(content="sorry")]
            )
            return node
        return node
        
    result = "\n\n".join(map(str,parse_lean_decls(code, my_filter)))
    
    assert "def keep_me : Nat := 1" in result
    assert "theorem keep_thm : True := by sorry" in result
    assert "drop_me" not in result
    assert "drop_thm" not in result

def test_parse_lean_decls_complex_program_sample():
    code = """
import Auto

open PartialCorrectness DemonicChoice Lean.Elab.Term.DoNames

set_option auto.smt.trust true

-- Convert a binary number to its decimal equivalent
-- Some comments that should be stripped

@[loomAbstractionSimp]
abbrev digitsReverseStr (s: String) : List Nat :=
  s.toList.reverse.map (λ c => if c = '0' then 0 else 1)

def binListToDecimalAcc (l : List Char) (acc : Nat) : Nat :=
  match l with
  | [] => acc
  | c :: rest =>
    let bit := if c = '1' then 1 else 0
    binListToDecimalAcc rest (acc * 2 + bit)

method BinaryStrToDecimal (binary: String)
  return (decimal: Nat)
  require isValidBinaryStr binary
  ensures decimal = binaryStrToDecimalValue binary
  do
  -- Some internal method comment
  let mut res := 0

theorem goal_0 (binary : String)
    (require_1 : isValidBinaryStr binary) : True := by sorry

theorem goal_2_h_res1_eq_bin (binary : String) (require_1 : isValidBinaryStr binary) : False := by sorry

def test_helper : Nat := 100

-- A comment about some other definition
abbrev test_alias := test_helper

#eval 1+1

unknown_command my_command (x : Nat) := x + 1
"""
    
    def custom_filter_map(node):
        # Filter out anything with "test" prefix
        if node.name.startswith("test"):
            return None
        
        # For theorems, print signature + custom proof strategy
        if isinstance(node, LeanTheorem):

            node.proof = LeanProof(
                is_by=True,          
                is_inline=True,     
                tactics=[LeanTactic(content="custom_proof")]
            )
            return str(node)
        
        # For definitions, print as is
        if isinstance(node, LeanDef):
            return str(node)
            
        return None 
        
    result = "\n".join(parse_lean_decls(code, custom_filter_map))
    
    # Assertions for expected included items
    expected_digitsReverseStr = textwrap.dedent("""@[loomAbstractionSimp]
abbrev digitsReverseStr (s: String) : List Nat :=
  s.toList.reverse.map (λ c => if c = '0' then 0 else 1)""")
    assert expected_digitsReverseStr in result

    expected_binListToDecimalAcc = textwrap.dedent("""def binListToDecimalAcc (l : List Char) (acc : Nat) : Nat :=
  match l with
  | [] => acc
  | c :: rest =>
    let bit := if c = '1' then 1 else 0
    binListToDecimalAcc rest (acc * 2 + bit)""")
    assert expected_binListToDecimalAcc in result

    assert "theorem goal_0 (binary : String) (require_1 : isValidBinaryStr binary) : True := by custom_proof" in result
    assert "theorem goal_2_h_res1_eq_bin (binary : String) (require_1 : isValidBinaryStr binary) : False := by custom_proof" in result
    
    # Assertions for expected excluded items
    assert "test_helper" not in result
    assert "test_alias" not in result
    assert "method BinaryStrToDecimal" not in result
    assert "#eval" not in result
    assert "unknown_command" not in result
    
    # Assert comments are stripped (assertion already correct)
    assert "Doc comment" not in result
    assert "Multi-line doc comment" not in result
    assert "Internal method comment" not in result
    assert "Some comments that should be stripped" not in result


# =============================================================================
# Additional Edge Case Tests for Robustness
# =============================================================================

class TestIndentationEdgeCases:
    """Tests for various indentation scenarios."""

    def test_no_indentation_theorem(self):
        """Theorem with no indentation at all."""
        code = """theorem no_indent : True := by
trivial"""
        parsed = parse_lean_theorem(code)
        assert parsed.name == "no_indent"
        assert parsed.return_type == "True"
        assert parsed.proof is not None
        assert len(parsed.proof.tactics) == 1
        assert parsed.proof.tactics[0].content == "trivial"

    def test_single_space_indentation(self):
        """Proof with single space indentation."""
        code = """theorem single_space : Nat := by
 let x := 1
 exact x"""
        parsed = parse_lean_theorem(code)
        assert parsed.name == "single_space"
        assert parsed.proof is not None
        assert len(parsed.proof.tactics) >= 2

    def test_deep_indentation(self):
        """Theorem with very deep indentation (16 spaces)."""
        code = """theorem deep_indent : True := by
                have h : True := by
                        trivial
                exact h"""
        parsed = parse_lean_theorem(code)
        assert parsed.name == "deep_indent"
        assert parsed.proof is not None
        # Should still parse the have block
        assert any(isinstance(t, LeanHaveDecl) for t in parsed.proof.tactics)

    def test_inconsistent_indentation(self):
        """Mixed indentation levels within proof."""
        code = """theorem mixed_indent : Nat := by
  let a := 1
    let b := 2
  exact a + b"""
        parsed = parse_lean_theorem(code)
        assert parsed.name == "mixed_indent"
        # Parser should handle this gracefully
        assert parsed.proof is not None

    def test_tab_indentation(self):
        """Theorem with tab indentation."""
        code = "theorem tab_indent : True := by\n\ttrivial"
        parsed = parse_lean_theorem(code)
        assert parsed.name == "tab_indent"
        assert parsed.proof is not None
        assert parsed.proof.tactics[0].content == "trivial"

    def test_mixed_tabs_and_spaces(self):
        """Mixed tabs and spaces in indentation."""
        code = "theorem mixed_ws : Nat := by\n\t  let x := 1\n  \texact x"
        parsed = parse_lean_theorem(code)
        assert parsed.name == "mixed_ws"
        assert parsed.proof is not None


class TestDeclarationExtraction:
    """Tests for extract_declarations with various file structures."""

    def test_consecutive_theorems_no_blank_lines(self):
        """Multiple theorems without blank lines between them."""
        code = """theorem th1 : True := trivial
theorem th2 : True := trivial
theorem th3 : True := trivial"""
        results = extract_declarations(code)
        names = [d.name for d in results]
        assert "th1" in names
        assert "th2" in names
        assert "th3" in names

    def test_theorem_immediately_after_def(self):
        """Theorem starting right after def ends."""
        code = """def mydef : Nat := 1
theorem mythm : True := trivial"""
        results = extract_declarations(code)
        names = [d.name for d in results]
        assert "mydef" in names
        assert "mythm" in names

    def test_nested_brackets_in_type(self):
        """Complex nested brackets in parameter types."""
        code = """theorem nested_brackets
  {α : Type}
  (f : (α → α) → α)
  (g : ((α → α) → α) → α)
  [inst : Inhabited ((α → α) → α)]
  : True := trivial"""
        results = extract_declarations(code)
        thm = next(d for d in results if d.name == "nested_brackets")
        assert isinstance(thm, LeanTheorem)
        assert len(thm.params) == 4

    def test_multiline_return_type(self):
        """Return type spanning multiple lines."""
        code = """theorem multiline_ret (n : Nat) :
  n = 0 ∨
  n > 0 := by
  omega"""
        parsed = parse_lean_theorem(code)
        assert parsed.name == "multiline_ret"
        assert parsed.return_type and ("n = 0 ∨" in parsed.return_type or "n > 0" in parsed.return_type)

    def test_def_with_where_clause(self):
        """Def with where clause should be captured."""
        code = """def with_where (n : Nat) : Nat := helper n
  where helper x := x + 1

theorem after_where : True := trivial"""
        results = extract_declarations(code)
        names = [d.name for d in results]
        assert "with_where" in names
        assert "after_where" in names

    def test_empty_params(self):
        """Theorem with no parameters."""
        code = """theorem no_params : 1 = 1 := rfl"""
        parsed = parse_lean_theorem(code)
        assert parsed.name == "no_params"
        assert parsed.params == []
        assert parsed.return_type == "1 = 1"

    def test_unicode_in_names_and_types(self):
        """Unicode characters in theorem names and types.

        Note: Parser currently doesn't support unicode in theorem names,
        but unicode in parameter types works fine.
        """
        # Unicode in name - currently not supported (documents limitation)
        code_unicode_name = """theorem α_β_γ {α : Type} (x : α) : α := x"""
        with pytest.raises(ValueError):
            parse_lean_theorem(code_unicode_name)

        # Unicode in types - this works
        code_unicode_types = """theorem unicode_types {α : Type} (x : α) : α := x"""
        parsed = parse_lean_theorem(code_unicode_types)
        assert parsed.name == "unicode_types"
        assert len(parsed.params) == 2

    def test_attributes_variations(self):
        """Various attribute formats."""
        code = """@[simp] theorem attr1 : True := trivial

@[simp, norm_cast] theorem attr2 : True := trivial

@[simp]
@[norm_cast]
theorem attr3 : True := trivial

@[deprecated "use something else"]
def attr_def : Nat := 1"""
        results = extract_declarations(code)
        names = [d.name for d in results]
        assert "attr1" in names
        assert "attr2" in names
        assert "attr3" in names
        assert "attr_def" in names

    def test_doc_comment_variations(self):
        """Various doc comment formats."""
        code = """/-- Simple doc -/
theorem doc1 : True := trivial

/--
Multi
line
doc
-/
theorem doc2 : True := trivial

/-- Doc with `code` and **bold** -/
def doc_def : Nat := 1"""
        results = extract_declarations(code)
        names = [d.name for d in results]
        assert "doc1" in names
        assert "doc2" in names
        assert "doc_def" in names


class TestProofParsing:
    """Tests for proof block parsing edge cases."""

    def test_empty_proof_block(self):
        """Proof with just 'by' and nothing else."""
        code = """theorem empty_proof : True := by
    trivial"""
        parsed = parse_lean_theorem(code)
        assert parsed.proof is not None
        assert parsed.proof.is_by == True

    def test_inline_complex_tactic(self):
        """Inline proof with complex tactic."""
        code = """theorem inline_complex : True := by exact (by trivial : True)"""
        parsed = parse_lean_theorem(code)
        assert parsed.proof is not None
        assert parsed.proof.is_inline == True
        assert "exact" in parsed.proof.tactics[0].content

    def test_multiple_have_same_line(self):
        """Multiple have statements at same indentation."""
        code = """theorem multi_have : Nat := by
    have h1 : Nat := 1
    have h2 : Nat := 2
    have h3 : Nat := 3
    exact h1 + h2 + h3"""
        parsed = parse_lean_theorem(code)
        assert parsed.proof is not None
        have_count = sum(1 for t in parsed.proof.tactics if isinstance(t, LeanHaveDecl))
        assert have_count == 3

    def test_have_with_complex_type(self):
        """Have with complex type including arrows and brackets."""
        code = """theorem have_complex_type : True := by
    have h : (∀ x : Nat, x = x) → True := by
     intro _
     trivial
    exact h (fun x => rfl)"""
        parsed = parse_lean_theorem(code)
        assert parsed.proof is not None
        have_decls = [t for t in parsed.proof.tactics if isinstance(t, LeanHaveDecl)]
        assert len(have_decls) == 1
        assert "∀ x : Nat" in have_decls[0].type_expr or "→ True" in have_decls[0].type_expr

    def test_bullet_points_various(self):
        """Various bullet point styles."""
        code = """theorem bullets : True ∨ True := by
  constructor
  · trivial
  · trivial"""
        parsed = parse_lean_theorem(code)
        assert parsed.proof is not None
        # Should have tactics including bullet points
        tactic_contents = [t.content for t in parsed.proof.tactics]
        assert "constructor" in tactic_contents

    def test_case_tactic(self):
        """Case tactic with subcases."""
        code = """theorem case_test (n : Nat) : n = n := by
  cases n with
  | zero => rfl
  | succ m => rfl"""
        parsed = parse_lean_theorem(code)
        assert parsed.proof is not None
        tactic_contents = [t.content for t in parsed.proof.tactics]
        assert any("cases n" in c for c in tactic_contents)

    def test_focus_tactic(self):
        """Focus/all_goals tactics."""
        code = """theorem focus_test (a b : Nat) : a = a ∧ b = b := by
  constructor
  all_goals rfl"""
        parsed = parse_lean_theorem(code)
        assert parsed.proof is not None
        tactic_contents = [t.content for t in parsed.proof.tactics]
        assert any("all_goals" in c for c in tactic_contents)

    def test_simp_with_lemmas(self):
        """Simp with list of lemmas."""
        code = """theorem simp_lemmas (n : Nat) : n + 0 = n := by
  simp only [Nat.add_zero, Nat.zero_add]"""
        parsed = parse_lean_theorem(code)
        assert parsed.proof is not None
        tactic_contents = [t.content for t in parsed.proof.tactics]
        assert any("simp only" in c for c in tactic_contents)


class TestSpecialCases:
    """Tests for special/unusual cases."""

    def test_theorem_named_keyword(self):
        """Theorem with name that could conflict with keywords."""
        code = """theorem by_test : True := trivial"""
        parsed = parse_lean_theorem(code)
        assert parsed.name == "by_test"

    def test_very_long_name(self):
        """Theorem with very long name."""
        long_name = "a" * 100
        code = f"""theorem {long_name} : True := trivial"""
        parsed = parse_lean_theorem(code)
        assert parsed.name == long_name

    def test_numeric_suffix_name(self):
        """Theorem name with numeric suffix."""
        code = """theorem test_123_456 : True := trivial"""
        parsed = parse_lean_theorem(code)
        assert parsed.name == "test_123_456"

    def test_prime_in_name(self):
        """Theorem name with prime symbol."""
        code = """theorem test' : True := trivial"""
        parsed = parse_lean_theorem(code)
        assert parsed.name == "test'"

    def test_dotted_name(self):
        """Theorem with dotted namespace name."""
        code = """theorem Foo.Bar.baz : True := trivial"""

        # Both should work with full dotted name
        results = extract_declarations(code)
        assert len(results) == 1
        assert results[0].name == "Foo.Bar.baz"

        parsed = parse_lean_theorem(code)
        assert parsed.name == "Foo.Bar.baz"

    def test_instance_declaration(self):
        """Instance declaration parsing.

        Note: Anonymous instances (no name) are not supported by the parser.
        Named instances work fine.
        """
        # Anonymous instance - not supported
        code_anon = """instance : Inhabited Nat := ⟨0⟩"""
        with pytest.raises(ValueError):
            parse_lean_theorem(code_anon)

        # Named instance - works
        code_named = """instance myInst : Inhabited Nat := ⟨0⟩"""
        parsed = parse_lean_theorem(code_named)
        assert parsed.kind == LeanTheoremKind.INSTANCE
        assert parsed.name == "myInst"

    def test_example_declaration(self):
        """Example declaration (no name).

        Note: Examples have no name, which the parser doesn't handle.
        This documents the limitation.
        """
        code = """example : 1 = 1 := rfl"""
        # Examples have no name - parser expects a name after the keyword
        with pytest.raises(ValueError):
            parse_lean_theorem(code)

    def test_strict_implicit_binder(self):
        """Strict implicit binder {{...}}."""
        code = """theorem strict_impl {{α : Type}} (x : α) : α := x"""
        parsed = parse_lean_theorem(code)
        assert any(p.kind == LeanBinderKind.STRICT_IMPLICIT for p in parsed.params)

    def test_inst_implicit_no_type(self):
        """Instance implicit without explicit type."""
        code = """theorem inst_no_type [Decidable p] (p : Prop) : p ∨ ¬p := by decide"""
        parsed = parse_lean_theorem(code)
        inst_params = [p for p in parsed.params if p.kind == LeanBinderKind.INST_IMPLICIT]
        assert len(inst_params) >= 1


class TestErrorRecovery:
    """Tests for graceful handling of edge cases."""

    def test_trailing_whitespace(self):
        """Theorem with trailing whitespace."""
        code = """theorem trailing : True := trivial   \n   """
        parsed = parse_lean_theorem(code)
        assert parsed.name == "trailing"

    def test_multiple_blank_lines(self):
        """Multiple blank lines in proof."""
        code = """theorem blanks : True := by


  trivial


"""
        parsed = parse_lean_theorem(code)
        assert parsed.name == "blanks"
        assert parsed.proof is not None
        # Should still find trivial tactic
        non_empty = [t for t in parsed.proof.tactics if t.content.strip()]
        assert any("trivial" in t.content for t in non_empty)

    def test_comment_only_lines_in_proof(self):
        """Proof with comment-only lines."""
        code = """theorem comment_lines : True := by
  -- Step 1
  -- Step 2
  -- Step 3
  trivial"""
        parsed = parse_lean_theorem(code)
        assert parsed.name == "comment_lines"

    def test_windows_line_endings(self):
        """File with Windows line endings (CRLF)."""
        code = "theorem windows : True := by\r\n  trivial\r\n"
        parsed = parse_lean_theorem(code)
        assert parsed.name == "windows"


class TestExtractDeclarationsRobustness:
    """Additional robustness tests for extract_declarations."""

    def test_file_starting_with_theorem(self):
        """File that starts immediately with theorem."""
        code = """theorem first : True := trivial"""
        results = extract_declarations(code)
        assert len(results) == 1
        assert results[0].name == "first"

    def test_file_ending_without_newline(self):
        """File that ends without trailing newline."""
        code = """theorem no_newline : True := trivial"""
        results = extract_declarations(code)
        assert len(results) == 1

    def test_only_comments_between_decls(self):
        """Only comments between declarations."""
        code = """def a : Nat := 1
-- comment 1
-- comment 2
/- block comment -/
def b : Nat := 2"""
        results = extract_declarations(code)
        names = [d.name for d in results]
        assert "a" in names
        assert "b" in names

    def test_hash_commands_scattered(self):
        """Hash commands scattered throughout."""
        code = """#check Nat
def a : Nat := 1
#eval 1 + 1
theorem b : True := trivial
#print a"""
        results = extract_declarations(code)
        names = [d.name for d in results]
        assert "a" in names
        assert "b" in names
        assert len(names) == 2  # Only def and theorem, not hash commands

    def test_open_and_variable_statements(self):
        """Open and variable statements should not break parsing."""
        code = """open Nat in
variable (n : Nat)

theorem uses_var : n = n := rfl"""
        results = extract_declarations(code)
        # Should find the theorem despite open/variable
        names = [d.name for d in results]
        assert "uses_var" in names

    def test_namespace_section_blocks(self):
        """Namespace and section blocks."""
        code = """namespace Foo

def inner : Nat := 1

section Bar

theorem inner_thm : True := trivial

end Bar

end Foo

def outer : Nat := 2"""
        results = extract_declarations(code)
        names = [d.name for d in results]
        assert "inner" in names
        assert "inner_thm" in names
        assert "outer" in names


class TestDefWithoutReturnType:
    """Tests for def declarations without explicit return type annotations.

    This class tests the fix for a bug where `def foo (x : T) := ...` (no return type)
    was being incorrectly parsed. The parser was mistaking the `:` in `:=` for a
    return type annotation, causing parsing failures.
    """

    def test_def_without_return_type_simple(self):
        """Simple def without return type annotation."""
        code = """def precondition (text : String) :=
  True"""
        parsed = parse_lean_theorem(code)
        assert parsed.name == "precondition"
        assert parsed.kind == LeanTheoremKind.DEF
        assert len(parsed.params) == 1
        assert parsed.params[0].names == ["text"]
        assert parsed.params[0].type_expr == "String"
        assert parsed.return_type is None
        assert parsed.proof is not None
        assert parsed.proof.term == "True"

    def test_def_without_return_type_multiple_params(self):
        """Def with multiple params but no return type."""
        code = """def postcondition (text : String) (res : Array String) :=
  ensures1 text res"""
        parsed = parse_lean_theorem(code)
        assert parsed.name == "postcondition"
        assert parsed.kind == LeanTheoremKind.DEF
        assert len(parsed.params) == 2
        assert parsed.params[0].names == ["text"]
        assert parsed.params[1].names == ["res"]
        assert parsed.return_type is None

    def test_def_with_return_type(self):
        """Def with explicit return type (should still work)."""
        code = """def wordsOf (text : String) : List String :=
  text.split Char.isWhitespace"""
        parsed = parse_lean_theorem(code)
        assert parsed.name == "wordsOf"
        assert parsed.kind == LeanTheoremKind.DEF
        assert len(parsed.params) == 1
        assert parsed.return_type == "List String"

    def test_def_no_params_no_return_type(self):
        """Def with no params and no return type."""
        code = """def myConst := 42"""
        parsed = parse_lean_theorem(code)
        assert parsed.name == "myConst"
        assert parsed.params == []
        assert parsed.return_type is None
        assert parsed.proof is not None
        assert parsed.proof.term == "42"

    def test_def_no_params_with_return_type(self):
        """Def with no params but with return type."""
        code = """def myConst : Nat := 42"""
        parsed = parse_lean_theorem(code)
        assert parsed.name == "myConst"
        assert parsed.params == []
        assert parsed.return_type == "Nat"
        assert parsed.proof is not None
        assert parsed.proof.term == "42"

    def test_def_multiline_body_no_return_type(self):
        """Def without return type but with multiline body."""
        code = """def ensures1 (text : String) (res : Array String) :=
  (∀ i : Nat, i < res.size → (res[i]!).length >= 4) ∧
  res.toList.Sublist (wordsOf text)"""
        parsed = parse_lean_theorem(code)
        assert parsed.name == "ensures1"
        assert parsed.return_type is None
        assert len(parsed.params) == 2

    def test_extract_declarations_def_without_return_type(self):
        """extract_declarations should handle defs without return types."""
        code = """section Specs

def precondition (text : String) :=
  True

def postcondition (text : String) (res : Array String) :=
  ensures1 text res

end Specs"""
        results = extract_declarations(code)
        defs = [d for d in results if isinstance(d, LeanDef)]
        names = [d.name for d in defs]

        assert "precondition" in names
        assert "postcondition" in names

        precond = next(d for d in defs if d.name == "precondition")
        assert "def precondition" in precond.content

    def test_theorem_still_requires_return_type(self):
        """Theorems still require return type (goal statement)."""
        code = """theorem foo (x : Nat) : x = x := by rfl"""
        parsed = parse_lean_theorem(code)
        assert parsed.name == "foo"
        assert parsed.return_type == "x = x"
        assert parsed.proof is not None
        assert parsed.proof.is_by == True
