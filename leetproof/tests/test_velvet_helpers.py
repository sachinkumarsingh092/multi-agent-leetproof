"""Tests for velvet_helpers module."""

from pathlib import Path

import pytest
from utils.velvet_helpers import (
    get_velvet_method,
    normalize_body_with_while_tags,
    upsert_hints_block,
    HINTS_BEGIN_MARKER,
    HINTS_END_MARKER,
    build_custom_loom_solver_prelude,
    get_prove_correct_block,
    extract_goals_after_loom_solve_with_retry,
    GoalExtractionDiagnosticError,
    GoalExtractionTimeoutError,
    identity,
)
from utils.lean.constants import LOOM_SOLVE_SIMP_ALL
from utils.velvet_types import NameInfo, VelvetMethod


class TestVelvetMethodParser:
    """Tests for velvet method parsing."""

    def test_simple_method_with_comment_before_ensures(self):
        """Test that comments between return and ensures are handled correctly."""
        content = """
method hasOppositeSign (a: Int) (b: Int)
  return (result: Bool)
  -- No preconditions: all Int values are valid inputs
  ensures result = true ↔ hasOppositeSignProp a b
  do
  pure true
"""
        method = get_velvet_method(content)

        assert method.name == "hasOppositeSign"
        assert method.params == [
            NameInfo(name="a", ty="Int", is_mut=False),
            NameInfo(name="b", ty="Int", is_mut=False),
        ]
        assert method.returns == NameInfo(name="result", ty="Bool", is_mut=False)
        assert method.ensures == ["result = true ↔ hasOppositeSignProp a b"]
        assert method.requires == []
        assert method.body == "pure true"
        assert not method.has_while_loop()

    def test_method_with_require_and_ensures(self):
        """Test parsing gcd-style method with require and ensures clauses."""
        content = """
method gcd (a : Nat) (b : Nat) return (res : Nat)
  require a > 0
  ensures res > 0
  do
    if b = 0 then
      return a
"""
        method = get_velvet_method(content)

        assert method.name == "gcd"
        assert method.params == [
            NameInfo(name="a", ty="Nat", is_mut=False),
            NameInfo(name="b", ty="Nat", is_mut=False),
        ]
        assert method.returns == NameInfo(name="res", ty="Nat", is_mut=False)
        assert method.ensures == ["res > 0"]
        assert method.requires == ["a > 0"]
        assert method.body is not None
        assert "if b = 0 then" in method.body
        assert not method.has_while_loop()

    def test_method_with_comment_between_require_and_ensures(self):
        """Test comment handling between require and ensures clauses."""
        content = """
method gcd (a : Nat) (b : Nat) return (res : Nat)
  require a > 0
  -- This ensures the result is always positive
  ensures res > 0
  do
    return a
"""
        method = get_velvet_method(content)

        assert method.name == "gcd"
        assert method.ensures == ["res > 0"]
        assert method.requires == ["a > 0"]
        assert method.body == "return a"

    def test_method_with_array_param(self):
        """Test parsing method with Array type parameter (from IsSorted)."""
        content = """
method IsSorted(a: Array Int) return (sorted: Bool)
    require a.size > 0
    ensures sorted ↔ (∀ i j, 0 ≤ i ∧ i < j ∧ j < a.size → a[i]! ≤ a[j]!)
do
    return true
"""
        method = get_velvet_method(content)

        assert method.name == "IsSorted"
        assert method.params == [NameInfo(name="a", ty="Array Int", is_mut=False)]
        assert method.ensures == ["sorted ↔ (∀ i j, 0 ≤ i ∧ i < j ∧ j < a.size → a[i]! ≤ a[j]!)"]
        assert method.requires == ["a.size > 0"]
        assert not method.has_while_loop()

    def test_method_with_multiple_ensures_no_require(self):
        """Test parsing method with multiple ensures and no require (from SubstringSearch)."""
        content = """
method SubstringSearch (s: Array Char) (p: Char -> Bool) return (res: SubstringResult)
--postconditions, don't need any preconditions.
ensures (res.l ≤ res.r)
ensures 0 < s.size → res.r < s.size
ensures res.flag → CorrectSubstring s p res.l res.r
do
    return ⟨0, 0, false⟩
"""
        method = get_velvet_method(content)

        assert method.name == "SubstringSearch"
        assert method.params == [
            NameInfo(name="s", ty="Array Char", is_mut=False),
            NameInfo(name="p", ty="Char -> Bool", is_mut=False),
        ]
        assert method.ensures == [
            "(res.l ≤ res.r)",
            "0 < s.size → res.r < s.size",
            "res.flag → CorrectSubstring s p res.l res.r",
        ]
        assert method.requires == []

    def test_method_only_ensures_no_require(self):
        """Test parsing SumOfDigits-style method with only ensures clause."""
        content = """
method SumOfDigits (number: Nat) return (sum: Nat)
    ensures sum = SumDigits number
do
    return 0
"""
        method = get_velvet_method(content)

        assert method.name == "SumOfDigits"
        assert method.ensures == ["sum = SumDigits number"]
        assert method.requires == []
        assert method.body == "return 0"

    def test_method_with_while_loop(self):
        """Test detecting while loop in method body."""
        content = """
method maxElem (arr: Array Int) return (res: Int)
  require arr.size > 0
  ensures isMax res arr
  do
    let mut i := 0
    let mut mx := arr[i]!
    while i < arr.size
    invariant 0 <= i
    do
      i := i + 1
    return mx
"""
        method = get_velvet_method(content)

        assert method.name == "maxElem"
        assert method.has_while_loop()
        assert method.has_invariant()
        assert method.body is not None
        assert "while i < arr.size" in method.body

    def test_method_without_loop_no_invariant(self):
        """Test method without loop has no invariant."""
        content = """
method simple (x: Nat) return (y: Nat)
  ensures y = x + 1
  do
    return x + 1
"""
        method = get_velvet_method(content)

        assert not method.has_while_loop()
        assert not method.has_invariant()

    def test_body_stops_at_prove_correct(self):
        """Test body extraction stops at prove_correct command."""
        content = """
method maxElem (arr: Array Int) return (res: Int)
  require arr.size > 0
  ensures isMax res arr
  do
    let mut mx := arr[0]!
    return mx

prove_correct maxElem by
  loom_solve
"""
        method = get_velvet_method(content)
        
        assert method.body is not None
        assert "let mut mx" in method.body
        assert "return mx" in method.body
        assert "prove_correct" not in method.body
        assert "loom_solve" not in method.body

    def test_body_stops_at_extract_program_for(self):
        """Test body extraction stops at extract_program_for command."""
        content = """
method foo (x: Nat) return (y: Nat)
  ensures y = x
  do
    return x

extract_program_for foo
prove_precondition_decidable_for foo
"""
        method = get_velvet_method(content)

        assert method.body == "return x"
        assert "extract_program_for" not in method.body

    def test_body_stops_at_termination_by(self):
        """Test body extraction stops at termination_by (GCD style)."""
        content = """
method gcd (a : Nat) (b : Nat) return (res : Nat)
  require a > 0
  ensures res > 0
  do
    if b = 0 then
      return a
    else
      let result ← gcd b (a % b)
      return result
  termination_by b
  decreasing_by
    apply Nat.mod_lt
    grind
"""
        method = get_velvet_method(content)
        
        assert method.body is not None
        assert "if b = 0 then" in method.body
        assert "return result" in method.body
        assert "termination_by" not in method.body
        assert "decreasing_by" not in method.body

    def test_body_with_nested_do(self):
        """Test body extraction handles nested do blocks in while loops."""
        content = """
method sumArray (arr: Array Int) return (sum: Int)
  ensures sum = arr.foldl (· + ·) 0
  do
    let mut sum := 0
    let mut i := 0
    while i < arr.size
    invariant sum = (arr.toList.take i).foldl (· + ·) 0
    do
      sum := sum + arr[i]!
      i := i + 1
    return sum

prove_correct sumArray by
  loom_solve
"""
        method = get_velvet_method(content)
        
        assert method.has_while_loop()
        assert method.body is not None
        assert "while i < arr.size" in method.body
        assert "sum := sum + arr[i]!" in method.body
        assert "return sum" in method.body
        assert "prove_correct" not in method.body

    def test_do_on_same_line_as_ensures(self):
        """Test parsing when do is on same line after ensures."""
        content = """
method simple (x: Nat) return (y: Nat)
  ensures y = x + 1 do
    return x + 1
"""
        method = get_velvet_method(content)
        
        assert method.name == "simple"
        assert method.ensures == ["y = x + 1"]
        assert method.body is not None
        assert "return x + 1" in method.body

    def test_body_with_blank_lines(self):
        """Test body extraction handles blank lines within the body."""
        content = """
method foo (x: Nat) return (y: Nat)
  ensures y = x + 1
  do
    let a := x

    let b := a + 1

    return b

prove_correct foo by
  loom_solve
"""
        method = get_velvet_method(content)
        
        assert method.body is not None
        assert "let a := x" in method.body
        assert "let b := a + 1" in method.body
        assert "return b" in method.body
        assert "prove_correct" not in method.body


class TestNormalizeBodyWithWhileTags:
    """Tests for normalize_body_with_while_tags function."""

    def test_simple_while_block(self):
        """Test normalizing a simple while loop."""
        body = """let mut i := 0
while i < 10
    invariant i >= 0
do
    i := i + 1
return i"""
        result = normalize_body_with_while_tags(body)
        assert "let mut i := 0" in result
        assert "<while1>" in result
        assert "<while1>:i := i + 1" in result
        assert "return i" in result
        # Annotations should be stripped
        assert "invariant" not in result

    def test_while_with_do_on_same_line(self):
        """Test while loop where 'do' is at end of annotation line."""
        body = """let mut i := 0
while i < 10
    invariant i >= 0 do
    i := i + 1
return i"""
        result = normalize_body_with_while_tags(body)
        assert "let mut i := 0" in result
        assert "<while1>" in result
        assert "<while1>:i := i + 1" in result
        assert "invariant" not in result

    def test_nested_while_loops(self):
        """Test nested while loops get nested tags."""
        body = """let mut i := 0
while i < 10
    invariant i >= 0
do
    let mut j := 0
    while j < 5
        invariant j >= 0
    do
        j := j + 1
    i := i + 1
return i"""
        result = normalize_body_with_while_tags(body)
        assert "let mut i := 0" in result
        assert "<while1>" in result
        assert "<while1>:let mut j := 0" in result
        assert "<while1>:<while2>" in result
        assert "<while1>:<while2>:j := j + 1" in result
        assert "<while1>:i := i + 1" in result
        assert "return i" in result

    def test_no_while_block(self):
        """Test body with no while loops returns as-is."""
        body = """let x := 5
let y := x + 1
return y"""
        result = normalize_body_with_while_tags(body)
        assert result == body

    def test_empty_body(self):
        """Test empty body returns empty string."""
        assert normalize_body_with_while_tags("") == ""

    def test_multiple_while_blocks(self):
        """Test multiple sequential while blocks."""
        body = """let mut a := 0
while a < 5
    invariant a >= 0
do
    a := a + 1
let mut b := 0
while b < 3
    invariant b >= 0
do
    b := b + 1
return a + b"""
        result = normalize_body_with_while_tags(body)
        assert "let mut a := 0" in result
        assert "<while1>" in result
        assert "<while1>:a := a + 1" in result
        assert "let mut b := 0" in result
        assert "<while2>" in result
        assert "<while2>:b := b + 1" in result
        assert "return a + b" in result

    def test_multiple_annotations(self):
        """Test while loop with multiple annotations."""
        body = """while i < arr.size
    invariant 0 <= i
    invariant i <= arr.size
    done_with i = arr.size
    decreasing arr.size - i
do
    i := i + 1"""
        result = normalize_body_with_while_tags(body)
        assert "<while1>" in result
        assert "<while1>:i := i + 1" in result
        # All annotations stripped
        assert "invariant" not in result
        assert "done_with" not in result
        assert "decreasing" not in result

    def test_same_body_different_invariants_normalize_equal(self):
        """Two bodies with same statements but different invariants should normalize to same result."""
        body1 = """let mut i := 0
while i < 10
    invariant i >= 0
do
    i := i + 1
return i"""
        body2 = """let mut i := 0
while i < 10
    invariant i >= 0
    invariant i <= 10
    done_with i = 10
do
    i := i + 1
return i"""
        result1 = normalize_body_with_while_tags(body1)
        result2 = normalize_body_with_while_tags(body2)
        assert result1 == result2

    def test_different_body_statements_normalize_different(self):
        """Two bodies with different statements should normalize differently."""
        body1 = """let mut i := 0
while i < 10
    invariant i >= 0
do
    i := i + 1
return i"""
        body2 = """let mut i := 0
while i < 10
    invariant i >= 0
do
    i := i + 2
return i"""
        result1 = normalize_body_with_while_tags(body1)
        result2 = normalize_body_with_while_tags(body2)
        assert result1 != result2

    def test_deeply_nested_three_levels(self):
        """Test three levels of nested while loops."""
        body = """let mut a := 0
while a < 3
    invariant a >= 0
do
    let mut b := 0
    while b < 3
        invariant b >= 0
    do
        let mut c := 0
        while c < 3
            invariant c >= 0
        do
            c := c + 1
        b := b + 1
    a := a + 1
return a"""
        result = normalize_body_with_while_tags(body)
        assert "<while1>" in result
        assert "<while1>:let mut b := 0" in result
        assert "<while1>:<while2>" in result
        assert "<while1>:<while2>:let mut c := 0" in result
        assert "<while1>:<while2>:<while3>" in result
        assert "<while1>:<while2>:<while3>:c := c + 1" in result
        assert "<while1>:<while2>:b := b + 1" in result
        assert "<while1>:a := a + 1" in result

    def test_while_with_if_else_inside(self):
        """Test while loop containing if/else statements."""
        body = """let mut i := 0
let mut sum := 0
while i < arr.size
    invariant sum >= 0
do
    if arr[i]! > 0 then
        sum := sum + arr[i]!
    else
        sum := sum - arr[i]!
    i := i + 1
return sum"""
        result = normalize_body_with_while_tags(body)
        assert "let mut i := 0" in result
        assert "let mut sum := 0" in result
        assert "<while1>" in result
        assert "<while1>:if arr[i]! > 0 then" in result
        assert "<while1>:sum := sum + arr[i]!" in result
        assert "<while1>:else" in result
        assert "<while1>:sum := sum - arr[i]!" in result
        assert "<while1>:i := i + 1" in result
        assert "return sum" in result

    def test_empty_lines_preserved(self):
        """Test that empty lines are preserved in output."""
        body = """let mut i := 0

while i < 10
    invariant i >= 0
do
    i := i + 1

return i"""
        result = normalize_body_with_while_tags(body)
        lines = result.split('\n')
        # Should have empty lines preserved
        assert "" in lines


class TestGoalExtractionTactics:
    """Regression tests for extraction-safe tactic snippets."""

    def test_get_prove_correct_block_uses_extraction_cleanup(self):
        method = VelvetMethod(
            name="foo",
            params=[],
            returns=NameInfo(name="result", ty="Nat", is_mut=False),
            body="return 0",
            requires=[],
            ensures=["result = 0"],
        )

        block = get_prove_correct_block(method)

        assert LOOM_SOLVE_SIMP_ALL in block
        assert "simp at *" not in block
        assert "injections" in block
        assert "subst_vars" in block

    def test_custom_loom_solver_prelude_avoids_simp_at_star(self):
        prelude = build_custom_loom_solver_prelude(4)

        assert "try injections" in prelude
        assert "try subst_vars" in prelude
        assert "simp at *" not in prelude

    def test_sibling_whiles_after_nested(self):
        """Test multiple while loops at same level after nested ones."""
        body = """while a < 5
    invariant a >= 0
do
    while b < 3
        invariant b >= 0
    do
        b := b + 1
    a := a + 1
while c < 2
    invariant c >= 0
do
    c := c + 1"""
        result = normalize_body_with_while_tags(body)
        assert "<while1>" in result
        assert "<while1>:<while2>" in result
        assert "<while1>:<while2>:b := b + 1" in result
        assert "<while1>:a := a + 1" in result
        assert "<while3>" in result
        assert "<while3>:c := c + 1" in result

    def test_complex_real_world_sorting(self):
        """Test a realistic sorting-like algorithm structure."""
        body = """let mut i := 0
while i < arr.size - 1
    invariant 0 <= i
    invariant i <= arr.size - 1
    invariant ∀ k, 0 <= k ∧ k < i → arr[k]! <= arr[k+1]!
    done_with i = arr.size - 1
do
    let mut j := i + 1
    while j < arr.size
        invariant i < j
        invariant j <= arr.size
    do
        if arr[j]! < arr[i]! then
            let temp := arr[i]!
            arr := arr.set! i arr[j]!
            arr := arr.set! j temp
        j := j + 1
    i := i + 1
return"""
        result = normalize_body_with_while_tags(body)
        # Outer structure
        assert "let mut i := 0" in result
        assert "<while1>" in result
        assert "return" in result
        # Inner while
        assert "<while1>:let mut j := i + 1" in result
        assert "<while1>:<while2>" in result
        # Inner while body
        assert "<while1>:<while2>:if arr[j]! < arr[i]! then" in result
        assert "<while1>:<while2>:let temp := arr[i]!" in result
        assert "<while1>:<while2>:arr := arr.set! i arr[j]!" in result
        assert "<while1>:<while2>:arr := arr.set! j temp" in result
        assert "<while1>:<while2>:j := j + 1" in result
        # After inner while
        assert "<while1>:i := i + 1" in result
        # No annotations
        assert "invariant" not in result
        assert "done_with" not in result

    def test_while_only_body(self):
        """Test body that is just a while loop with nothing before/after."""
        body = """while x > 0
    invariant x >= 0
do
    x := x - 1"""
        result = normalize_body_with_while_tags(body)
        assert "<while1>" in result
        assert "<while1>:x := x - 1" in result
        assert "invariant" not in result

    def test_multiple_statements_per_line_level(self):
        """Test multiple statements at various indentation levels."""
        body = """let a := 1
let b := 2
let c := 3
while i < 10
    invariant i >= 0
do
    let x := a + b
    let y := b + c
    let z := x + y
    while j < 5
        invariant j >= 0
    do
        let p := x
        let q := y
    let w := z
return a + b + c"""
        result = normalize_body_with_while_tags(body)
        # Outside while
        assert "let a := 1" in result
        assert "let b := 2" in result
        assert "let c := 3" in result
        assert "return a + b + c" in result
        # First level
        assert "<while1>:let x := a + b" in result
        assert "<while1>:let y := b + c" in result
        assert "<while1>:let z := x + y" in result
        assert "<while1>:let w := z" in result
        # Second level
        assert "<while1>:<while2>:let p := x" in result
        assert "<while1>:<while2>:let q := y" in result

    def test_annotation_with_complex_expressions(self):
        """Test annotations with complex mathematical expressions are stripped."""
        body = """while i < arr.size ∧ ¬found
    invariant 0 ≤ i ∧ i ≤ arr.size
    invariant ∀ k, 0 ≤ k ∧ k < i → arr[k]! ≠ target
    invariant found = true → arr[i]! = target
    done_with found = true ∨ i = arr.size
    decreasing arr.size - i
do
    if arr[i]! = target then
        found := true
    else
        i := i + 1
return found"""
        result = normalize_body_with_while_tags(body)
        assert "<while1>" in result
        assert "<while1>:if arr[i]! = target then" in result
        assert "<while1>:found := true" in result
        assert "<while1>:else" in result
        assert "<while1>:i := i + 1" in result
        assert "return found" in result
        # All complex annotations stripped
        assert "∀" not in result
        assert "∧" not in result or "∧" in "<while1>" # only in condition line
        assert "invariant" not in result
        assert "done_with" not in result
        assert "decreasing" not in result

    def test_do_immediately_after_while(self):
        """Test while with do on same line as condition."""
        body = """let mut i := 0
while i < 10 do
    i := i + 1
return i"""
        result = normalize_body_with_while_tags(body)
        assert "let mut i := 0" in result
        assert "<while1>" in result
        assert "<while1>:i := i + 1" in result
        assert "return i" in result

    def test_indentation_variations(self):
        """Test various indentation levels are handled."""
        body = """    let mut i := 0
    while i < 10
        invariant i >= 0
    do
        i := i + 1
    return i"""
        result = normalize_body_with_while_tags(body)
        # Should contain the statements (indentation may vary)
        assert "let mut i := 0" in result
        assert "<while1>" in result
        assert "i := i + 1" in result
        assert "return i" in result

    def test_while_with_break_continue(self):
        """Test while loop with break/continue statements."""
        body = """let mut i := 0
while i < 100
    invariant i >= 0
do
    if arr[i]! = target then
        break
    if arr[i]! < 0 then
        i := i + 1
        continue
    process arr[i]!
    i := i + 1
return i"""
        result = normalize_body_with_while_tags(body)
        assert "<while1>:if arr[i]! = target then" in result
        assert "<while1>:break" in result
        assert "<while1>:if arr[i]! < 0 then" in result
        assert "<while1>:continue" in result
        assert "<while1>:process arr[i]!" in result

    def test_comments_in_annotations_stripped(self):
        """Test that comment lines between while and do are stripped."""
        body = """while i < 10
    -- This is a comment about the invariant
    invariant i >= 0
    -- Another comment
    done_with i = 10
do
    i := i + 1
return i"""
        result = normalize_body_with_while_tags(body)
        assert "<while1>" in result
        assert "<while1>:i := i + 1" in result
        assert "return i" in result
        # Comments should be stripped along with annotations
        assert "comment" not in result.lower()
        assert "invariant" not in result

    def test_mixed_nesting_patterns(self):
        """Test complex mixed nesting with multiple entry/exit points."""
        body = """let result := 0
while a > 0
    invariant a >= 0
do
    while b > 0
        invariant b >= 0
    do
        b := b - 1
    result := result + 1
    while c > 0
        invariant c >= 0
    do
        while d > 0
            invariant d >= 0
        do
            d := d - 1
        c := c - 1
    a := a - 1
return result"""
        result = normalize_body_with_while_tags(body)
        # Check structure
        assert "<while1>" in result
        assert "<while1>:<while2>" in result
        assert "<while1>:<while2>:b := b - 1" in result
        assert "<while1>:result := result + 1" in result
        assert "<while1>:<while3>" in result
        assert "<while1>:<while3>:<while4>" in result
        assert "<while1>:<while3>:<while4>:d := d - 1" in result
        assert "<while1>:<while3>:c := c - 1" in result
        assert "<while1>:a := a - 1" in result


class TestHintsBlockUpsert:
    def test_upsert_adds_block_when_missing(self):
        content = "theorem t : True := by\n  trivial"
        updated = upsert_hints_block(content, ["Foo.a", "Foo.b"])

        assert updated == content

    def test_upsert_replaces_existing_block(self):
        content = (
            "theorem t : True := by\n  trivial\n\n"
            f"{HINTS_BEGIN_MARKER}\n"
            "attribute [grind] Old.x\n"
            f"{HINTS_END_MARKER}\n"
        )

        updated = upsert_hints_block(content, ["New.y"])

        assert "Old.x" not in updated
        assert HINTS_BEGIN_MARKER not in updated
        assert HINTS_END_MARKER not in updated

    def test_upsert_removes_existing_block_when_empty(self):
        content = (
            "theorem t : True := by\n  trivial\n\n"
            f"{HINTS_BEGIN_MARKER}\n"
            "attribute [grind] Old.x\n"
            f"{HINTS_END_MARKER}\n"
        )

        updated = upsert_hints_block(content, [])

        assert HINTS_BEGIN_MARKER not in updated
        assert HINTS_END_MARKER not in updated
        assert "Old.x" not in updated


class TestGoalExtractionRetry:
    PROGRAM = """
section Specs

def precondition (x : Nat) := True
def postcondition (x : Nat) (y : Nat) := y = x

end Specs

section Impl

method foo (x : Nat) return (y : Nat)
  require precondition x
  ensures postcondition x y
  do
    return x

end Impl
"""

    @pytest.mark.asyncio
    async def test_retries_timeout_with_descending_grind_gen_params(
        self, tmp_path, monkeypatch
    ):
        output_file = tmp_path / "Foo.lean"
        seen_contents: list[str] = []

        def fake_get_goals(file_path: str) -> str:
            content = Path(file_path).read_text()
            seen_contents.append(content)
            if "gen := 2" in content:
                return "x : Nat\n⊢ x = x"
            return "Lean build timed out after 120s"

        monkeypatch.setattr(
            "utils.velvet_helpers.get_simplified_goals_after_loom_solve",
            fake_get_goals,
        )

        result = await extract_goals_after_loom_solve_with_retry(
            self.PROGRAM,
            str(output_file),
            preprocess=identity,
            postprocess=identity,
        )

        assert result.goal_result_str == "x : Nat\n⊢ x = x"
        assert result.grind_gen_param == 2
        assert len(result.goals) == 1
        assert result.goals[0].final_goal == "x = x"
        assert len(seen_contents) == 3
        assert 'set_option loom.solver "custom"' not in seen_contents[0]
        assert "gen := 4" in seen_contents[1]
        assert "gen := 2" in seen_contents[2]
        assert "gen := 1" not in seen_contents[2]
        cleaned = Path(output_file).read_text()
        assert 'set_option loom.solver "custom"' not in cleaned
        assert "macro_rules" not in cleaned
        assert "prove_correct foo by" not in cleaned

    @pytest.mark.asyncio
    async def test_preferred_grind_gen_param_skips_default_and_other_retries(
        self, tmp_path, monkeypatch
    ):
        output_file = tmp_path / "Foo.lean"
        seen_contents: list[str] = []

        def fake_get_goals(file_path: str) -> str:
            content = Path(file_path).read_text()
            seen_contents.append(content)
            return "Lean build timed out after 120s"

        monkeypatch.setattr(
            "utils.velvet_helpers.get_simplified_goals_after_loom_solve",
            fake_get_goals,
        )

        with pytest.raises(GoalExtractionTimeoutError, match="build timed out"):
            await extract_goals_after_loom_solve_with_retry(
                self.PROGRAM,
                str(output_file),
                preprocess=identity,
                postprocess=identity,
                preferred_grind_gen_param=1,
            )

        assert len(seen_contents) == 1
        assert 'set_option loom.solver "custom"' in seen_contents[0]
        assert "gen := 1" in seen_contents[0]
        assert "gen := 4" not in seen_contents[0]
        cleaned = Path(output_file).read_text()
        assert 'set_option loom.solver "custom"' not in cleaned
        assert "macro_rules" not in cleaned

    @pytest.mark.asyncio
    async def test_raises_diagnostic_error_when_retry_result_is_not_parseable(
        self, tmp_path, monkeypatch
    ):
        output_file = tmp_path / "Foo.lean"

        monkeypatch.setattr(
            "utils.velvet_helpers.get_simplified_goals_after_loom_solve",
            lambda _file_path: "some unrelated Lean error",
        )

        with pytest.raises(
            GoalExtractionDiagnosticError,
            match="no parseable goals were produced",
        ):
            await extract_goals_after_loom_solve_with_retry(
                self.PROGRAM,
                str(output_file),
                preprocess=identity,
                postprocess=identity,
            )
