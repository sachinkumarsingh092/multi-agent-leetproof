import Velvet.Std
import Loom.SMT
import Batteries.Data.String.Matcher

set_option loom.solver.smt.default "cvc5"

open Lean Elab Tactic Meta

initialize
  registerTraceClass `extensions.smt.smart

/-! ## List Indexing Lemmas for SMT Solvers

This file demonstrates how to add lemmas for list indexing operations that are
otherwise translated as uninterpreted functions in SMT.

### The Problem
When using `smt'`/`auto'`, list indexing operations like `List.getElem!`, `List.get?`,
etc. are translated to uninterpreted functions. Without axioms, the SMT solver
has no knowledge of their properties.

### The Solution
Define lemmas as direct equations (avoiding pattern matching) and mark them with
`[solverHint]` attribute.
-/

-- ========== Lemmas for Option.getD ==========
-- attribute [solverHint] Option.getD_none Option.getD_some

-- ========== Lemmas for List ==========
-- attribute [solverHint] List.getElem?_cons_zero List.getElem?_cons_succ List.getElem?_nil

-- attribute [solverHint] List.getElem!_eq_getElem?_getD

-- attribute [solverHint] List.getD_cons_zero List.getD_cons_succ List.getD_nil
-- attribute [solverHint] List.getD_eq_getElem?_getD

-- ========== Examples moved to end ==========

-- ========== Lemmas for Array ==========

theorem array_setIfInBound_access_eq {α: Type} [Inhabited α](arr: Array α) (i: Nat) (v: α) (h: i < arr.size) :
  (arr.setIfInBounds i v)[i]! = v := by grind

theorem array_setIfInBound_access_neq {α: Type} [Inhabited α](arr: Array α) (i: Nat) (j: Nat) (v: α):
  i < arr.size →
  j < arr.size →
  i ≠ j →
  (arr.setIfInBounds i v)[j]! = arr[j]! := by grind

-- ========== Lemmas for Mem ==========

theorem list_mem_first {α: Type} (x: α) (xs : List α) : x ∈ (x :: xs) := by simp

-- attribute [solverHint] List.not_mem_nil List.mem_cons

-- ========== Smart Solver Hints with Meta-Programming ==========

-- Check if an expression contains Array operations (similar to SpecDSL.lean's containsForbiddenFunction)
partial def containsArrayOps (e : Expr) : Bool :=
  match e with
  | Expr.app f arg =>
    -- Check if this is an Array operation
    if f.isConst then
      let name := f.constName!
      let nameStr := name.toString
      (nameStr.startsWith "Array." || nameStr.containsSubstr "Array".toSubstring) ||
      containsArrayOps f || containsArrayOps arg
    else
      containsArrayOps f || containsArrayOps arg
  | Expr.const name _ =>
    let nameStr := name.toString
    nameStr.startsWith "Array." || nameStr.containsSubstr "Array".toSubstring
  | Expr.lam _ _ body _ => containsArrayOps body
  | Expr.forallE _ domain body _ => containsArrayOps domain || containsArrayOps body
  | Expr.letE _ _ value body _ => containsArrayOps value || containsArrayOps body
  | _ => false

-- Check if an expression contains List operations
partial def containsListOps (e : Expr) : Bool :=
  match e with
  | Expr.app f arg =>
    if f.isConst then
      let name := f.constName!
      let nameStr := name.toString
      (nameStr.startsWith "List." || nameStr.containsSubstr "List".toSubstring) ||
      containsListOps f || containsListOps arg
    else
      containsListOps f || containsListOps arg
  | Expr.const name _ =>
    let nameStr := name.toString
    nameStr.startsWith "List." || nameStr.containsSubstr "List".toSubstring
  | Expr.lam _ _ body _ => containsListOps body
  | Expr.forallE _ domain body _ => containsListOps domain || containsListOps body
  | Expr.letE _ _ value body _ => containsListOps value || containsListOps body
  | _ => false

-- Check if an expression contains membership operations
partial def containsMemOps (e : Expr) : Bool :=
  match e with
  | Expr.app f arg =>
    if f.isConst then
      let name := f.constName!
      (name == `Membership.mem || name.toString.containsSubstr "mem".toSubstring) ||
      containsMemOps f || containsMemOps arg
    else
      containsMemOps f || containsMemOps arg
  | Expr.const name _ =>
    name == `Membership.mem || name.toString.containsSubstr "mem".toSubstring
  | Expr.lam _ _ body _ => containsMemOps body
  | Expr.forallE _ domain body _ => containsMemOps domain || containsMemOps body
  | Expr.letE _ _ value body _ => containsMemOps value || containsMemOps body
  | _ => false

-- Check if an expression contains Append operations (similar to SpecDSL.lean's containsForbiddenFunction)
partial def containsAppendOps (e : Expr) : Bool :=
  match e with
  | Expr.app f arg =>
    if f.isConst then
      let name := f.constName!
      let nameStr := name.toString
      (nameStr.startsWith "List.append" || nameStr.containsSubstr "append".toSubstring ||
       nameStr.containsSubstr "++".toSubstring || nameStr.containsSubstr "HAppend".toSubstring ||
       name == `HAppend.hAppend || name == `List.append) ||
      containsAppendOps f || containsAppendOps arg
    else
      containsAppendOps f || containsAppendOps arg
  | Expr.const name _ =>
    let nameStr := name.toString
    nameStr.startsWith "List.append" || nameStr.containsSubstr "append".toSubstring ||
    nameStr.containsSubstr "HAppend".toSubstring || name == `HAppend.hAppend || name == `List.append
  | Expr.lam _ _ body _ => containsAppendOps body
  | Expr.forallE _ domain body _ => containsAppendOps domain || containsAppendOps body
  | Expr.letE _ _ value body _ => containsAppendOps value || containsAppendOps body
  | _ => false

-- Check if an expression contains Option operations
partial def containsOptionOps (e : Expr) : Bool :=
  match e with
  | Expr.app f arg =>
    if f.isConst then
      let name := f.constName!
      let nameStr := name.toString
      (nameStr.startsWith "Option." || nameStr.containsSubstr "Option".toSubstring) ||
      containsOptionOps f || containsOptionOps arg
    else
      containsOptionOps f || containsOptionOps arg
  | Expr.const name _ =>
    let nameStr := name.toString
    nameStr.startsWith "Option." || nameStr.containsSubstr "Option".toSubstring
  | Expr.lam _ _ body _ => containsOptionOps body
  | Expr.forallE _ domain body _ => containsOptionOps domain || containsOptionOps body
  | Expr.letE _ _ value body _ => containsOptionOps value || containsOptionOps body
  | _ => false

/-- Smart SMT tactic that analyzes goal and context to select appropriate hints -/
syntax (name := smtPrime) "smt'" : tactic

@[tactic smtPrime] def elabSmtPrime : Tactic := fun _ => do
  Lean.Elab.Tactic.withMainContext do
    let goal ← Tactic.getMainTarget
    let lctx ← getLCtx

    -- Collect all expressions to analyze
    let mut allExprs : List Expr := [goal]
    for decl in lctx do
      unless decl.isImplementationDetail do
        allExprs := decl.type :: allExprs

    -- Check for patterns in all expressions
    let hasArray := allExprs.any containsArrayOps
    let hasList := allExprs.any containsListOps
    let hasMem := allExprs.any containsMemOps
    let hasOption := allExprs.any containsOptionOps
    let hasAppend := allExprs.any containsAppendOps

    -- Build hints array based on detected patterns
    let mut hints : Array (TSyntax `Auto.hintelem) := #[]

    -- Add all solverHints registered in the environment (matching base solver behavior)
    let ctx := solverHints.getState (← getEnv)
    for c in ctx do
      hints := hints.push (← `(Auto.hintelem| $(mkIdent c):ident))

    -- Always add wildcard (matching base solver behavior)
    hints := hints.push (← `(Auto.hintelem| *))

    -- Add Option hints if detected
    if hasOption then
      trace[extensions.smt.smart] "Option found"
      hints := hints.push (← `(Auto.hintelem| Option.getD_none))
      hints := hints.push (← `(Auto.hintelem| Option.getD_some))

    -- Add List hints if detected
    if hasList then
      trace[extensions.smt.smart] "List found"
      hints := hints.push (← `(Auto.hintelem| List.getElem!_eq_getElem?_getD))
      hints := hints.push (← `(Auto.hintelem| List.getElem?_cons_zero))
      hints := hints.push (← `(Auto.hintelem| List.getElem?_cons_succ))
      hints := hints.push (← `(Auto.hintelem| List.getElem?_nil))
      hints := hints.push (← `(Auto.hintelem| List.getD_eq_getElem?_getD))
      hints := hints.push (← `(Auto.hintelem| List.getD_cons_zero))
      hints := hints.push (← `(Auto.hintelem| List.getD_cons_succ))
      hints := hints.push (← `(Auto.hintelem| List.getD_nil))

    -- Add Array hints if detected
    if hasArray then
      trace[extensions.smt.smart] "Array found"
      hints := hints.push (← `(Auto.hintelem| Array.setIfInBounds_eq_of_size_le))
      hints := hints.push (← `(Auto.hintelem| array_setIfInBound_access_eq))
      hints := hints.push (← `(Auto.hintelem| array_setIfInBound_access_neq))
      hints := hints.push (← `(Auto.hintelem| Array.set_push))
      hints := hints.push (← `(Auto.hintelem| Array.set_pop))
      hints := hints.push (← `(Auto.hintelem| Array.size_push))

    -- Add Mem hints if detected
    if hasMem then
      trace[extensions.smt.smart] "Mem found"
      hints := hints.push (← `(Auto.hintelem| List.not_mem_nil))
      hints := hints.push (← `(Auto.hintelem| List.mem_cons))

    -- Add Append hints if detected
    if hasAppend then
      trace[extensions.smt.smart] "Append found"
      hints := hints.push (← `(Auto.hintelem| List.append_nil))
      hints := hints.push (← `(Auto.hintelem| List.nil_append))
      hints := hints.push (← `(Auto.hintelem| List.append_assoc))
      hints := hints.push (← `(Auto.hintelem| List.getElem_append_left))
      hints := hints.push (← `(Auto.hintelem| List.getElem_append_right))
      hints := hints.push (← `(Auto.hintelem| List.length_append))

    -- Run smart SMT with discovered hints
    let tacticStx ← `(tactic| try (try simp only [loomAbstractionSimp] at *); (try simp only [Array.set!] at *); loom_smt [$hints,*])
    for hint in hints do
      trace[extensions.smt.smart] "Hint: {hint}"
    Tactic.evalTactic tacticStx

-- Friendly aliases
syntax (name := autoPrime) "auto'" : tactic

macro_rules
  | `(tactic| auto') => `(tactic| smt')

