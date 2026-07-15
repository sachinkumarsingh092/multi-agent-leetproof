/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: a6b3c918-1eeb-4d24-87eb-7b74b56384f4

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem correctness_goal (intervals : Array Interval) (h_precond : precondition intervals) : postcondition intervals (implementation (intervals))

At Harmonic, we use a modified version of the `generalize_proofs` tactic.
For compatibility, we include this tactic at the start of the file.
If you add the comment "-- Harmonic `generalize_proofs` tactic" to your file, we will not do this.
-/

import Lean

import Mathlib.Tactic


import Mathlib.Tactic.GeneralizeProofs

namespace Harmonic.GeneralizeProofs
-- Harmonic `generalize_proofs` tactic

open Lean Meta Elab Parser.Tactic Elab.Tactic Mathlib.Tactic.GeneralizeProofs
def mkLambdaFVarsUsedOnly' (fvars : Array Expr) (e : Expr) : MetaM (Array Expr × Expr) := do
  let mut e := e
  let mut fvars' : List Expr := []
  for i' in [0:fvars.size] do
    let fvar := fvars[fvars.size - i' - 1]!
    e ← mkLambdaFVars #[fvar] e (usedOnly := false) (usedLetOnly := false)
    match e with
    | .letE _ _ v b _ => e := b.instantiate1 v
    | .lam _ _ _b _ => fvars' := fvar :: fvars'
    | _ => unreachable!
  return (fvars'.toArray, e)

partial def abstractProofs' (e : Expr) (ty? : Option Expr) : MAbs Expr := do
  if (← read).depth ≤ (← read).config.maxDepth then MAbs.withRecurse <| visit (← instantiateMVars e) ty?
  else return e
where
  visit (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    if (← read).config.debug then
      if let some ty := ty? then
        unless ← isDefEq (← inferType e) ty do
          throwError "visit: type of{indentD e}\nis not{indentD ty}"
    if e.isAtomic then
      return e
    else
      checkCache (e, ty?) fun _ ↦ do
        if ← isProof e then
          visitProof e ty?
        else
          match e with
          | .forallE n t b i =>
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              mkForallFVars #[x] (← visit (b.instantiate1 x) none) (usedOnly := false) (usedLetOnly := false)
          | .lam n t b i => do
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              let ty'? ←
                if let some ty := ty? then
                  let .forallE _ _ tyB _ ← pure ty
                    | throwError "Expecting forall in abstractProofs .lam"
                  pure <| some <| tyB.instantiate1 x
                else
                  pure none
              mkLambdaFVars #[x] (← visit (b.instantiate1 x) ty'?) (usedOnly := false) (usedLetOnly := false)
          | .letE n t v b _ =>
            let t' ← visit t none
            withLetDecl n t' (← visit v t') fun x ↦ MAbs.withLocal x do
              mkLetFVars #[x] (← visit (b.instantiate1 x) ty?) (usedLetOnly := false)
          | .app .. =>
            e.withApp fun f args ↦ do
              let f' ← visit f none
              let argTys ← appArgExpectedTypes f' args ty?
              let mut args' := #[]
              for arg in args, argTy in argTys do
                args' := args'.push <| ← visit arg argTy
              return mkAppN f' args'
          | .mdata _ b  => return e.updateMData! (← visit b ty?)
          | .proj _ _ b => return e.updateProj! (← visit b none)
          | _           => unreachable!
  visitProof (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    let eOrig := e
    let fvars := (← read).fvars
    let e := e.withApp' fun f args => f.beta args
    if e.withApp' fun f args => f.isAtomic && args.all fvars.contains then return e
    let e ←
      if let some ty := ty? then
        if (← read).config.debug then
          unless ← isDefEq ty (← inferType e) do
            throwError m!"visitProof: incorrectly propagated type{indentD ty}\nfor{indentD e}"
        mkExpectedTypeHint e ty
      else pure e
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← getLCtx) e do
        throwError m!"visitProof: proof{indentD e}\nis not well-formed in the current context\n\
          fvars: {fvars}"
    let (fvars', pf) ← mkLambdaFVarsUsedOnly' fvars e
    if !(← read).config.abstract && !fvars'.isEmpty then
      return eOrig
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← read).initLCtx pf do
        throwError m!"visitProof: proof{indentD pf}\nis not well-formed in the initial context\n\
          fvars: {fvars}\n{(← mkFreshExprMVar none).mvarId!}"
    let pfTy ← instantiateMVars (← inferType pf)
    let pfTy ← abstractProofs' pfTy none
    if let some pf' ← MAbs.findProof? pfTy then
      return mkAppN pf' fvars'
    MAbs.insertProof pfTy pf
    return mkAppN pf fvars'
partial def withGeneralizedProofs' {α : Type} [Inhabited α] (e : Expr) (ty? : Option Expr)
    (k : Array Expr → Array Expr → Expr → MGen α) :
    MGen α := do
  let propToFVar := (← get).propToFVar
  let (e, generalizations) ← MGen.runMAbs <| abstractProofs' e ty?
  let rec
    go [Inhabited α] (i : Nat) (fvars pfs : Array Expr)
        (proofToFVar propToFVar : ExprMap Expr) : MGen α := do
      if h : i < generalizations.size then
        let (ty, pf) := generalizations[i]
        let ty := (← instantiateMVars (ty.replace proofToFVar.get?)).cleanupAnnotations
        withLocalDeclD (← mkFreshUserName `pf) ty fun fvar => do
          go (i + 1) (fvars := fvars.push fvar) (pfs := pfs.push pf)
            (proofToFVar := proofToFVar.insert pf fvar)
            (propToFVar := propToFVar.insert ty fvar)
      else
        withNewLocalInstances fvars 0 do
          let e' := e.replace proofToFVar.get?
          modify fun s => { s with propToFVar }
          k fvars pfs e'
  go 0 #[] #[] (proofToFVar := {}) (propToFVar := propToFVar)

partial def generalizeProofsCore'
    (g : MVarId) (fvars rfvars : Array FVarId) (target : Bool) :
    MGen (Array Expr × MVarId) := go g 0 #[]
where
  go (g : MVarId) (i : Nat) (hs : Array Expr) : MGen (Array Expr × MVarId) := g.withContext do
    let tag ← g.getTag
    if h : i < rfvars.size then
      let fvar := rfvars[i]
      if fvars.contains fvar then
        let tgt ← instantiateMVars <| ← g.getType
        let ty := (if tgt.isLet then tgt.letType! else tgt.bindingDomain!).cleanupAnnotations
        if ← pure tgt.isLet <&&> Meta.isProp ty then
          let tgt' := Expr.forallE tgt.letName! ty tgt.letBody! .default
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .app g' tgt.letValue!
          return ← go g'.mvarId! i hs
        if let some pf := (← get).propToFVar.get? ty then
          let tgt' := tgt.bindingBody!.instantiate1 pf
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .lam tgt.bindingName! tgt.bindingDomain! g' tgt.bindingInfo!
          return ← go g'.mvarId! (i + 1) hs
        match tgt with
        | .forallE n t b bi =>
          let prop ← Meta.isProp t
          withGeneralizedProofs' t none fun hs' pfs' t' => do
            let t' := t'.cleanupAnnotations
            let tgt' := Expr.forallE n t' b bi
            let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
            g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
            let (fvar', g') ← g'.mvarId!.intro1P
            g'.withContext do Elab.pushInfoLeaf <|
              .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
            if prop then
              MGen.insertFVar t' (.fvar fvar')
            go g' (i + 1) (hs ++ hs')
        | .letE n t v b _ =>
          withGeneralizedProofs' t none fun hs' pfs' t' => do
            withGeneralizedProofs' v t' fun hs'' pfs'' v' => do
              let tgt' := Expr.letE n t' v' b false
              let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
              g.assign <| mkAppN (← mkLambdaFVars (hs' ++ hs'') g' (usedOnly := false) (usedLetOnly := false)) (pfs' ++ pfs'')
              let (fvar', g') ← g'.mvarId!.intro1P
              g'.withContext do Elab.pushInfoLeaf <|
                .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
              go g' (i + 1) (hs ++ hs' ++ hs'')
        | _ => unreachable!
      else
        let (fvar', g') ← g.intro1P
        g'.withContext do Elab.pushInfoLeaf <|
          .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
        go g' (i + 1) hs
    else if target then
      withGeneralizedProofs' (← g.getType) none fun hs' pfs' ty' => do
        let g' ← mkFreshExprSyntheticOpaqueMVar ty' tag
        g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
        return (hs ++ hs', g'.mvarId!)
    else
      return (hs, g)

end GeneralizeProofs

open Lean Elab Parser.Tactic Elab.Tactic Mathlib.Tactic.GeneralizeProofs
partial def generalizeProofs'
    (g : MVarId) (fvars : Array FVarId) (target : Bool) (config : Config := {}) :
    MetaM (Array Expr × MVarId) := do
  let (rfvars, g) ← g.revert fvars (clearAuxDeclsInsteadOfRevert := true)
  g.withContext do
    let s := { propToFVar := ← initialPropToFVar }
    GeneralizeProofs.generalizeProofsCore' g fvars rfvars target |>.run config |>.run' s

elab (name := generalizeProofsElab'') "generalize_proofs" config?:(Parser.Tactic.config)?
    hs:(ppSpace colGt binderIdent)* loc?:(location)? : tactic => withMainContext do
  let config ← elabConfig (mkOptionalNode config?)
  let (fvars, target) ←
    match expandOptLocation (Lean.mkOptionalNode loc?) with
    | .wildcard => pure ((← getLCtx).getFVarIds, true)
    | .targets t target => pure (← getFVarIds t, target)
  liftMetaTactic1 fun g => do
    let (pfs, g) ← generalizeProofs' g fvars target config
    g.withContext do
      let mut lctx ← getLCtx
      for h in hs, fvar in pfs do
        if let `(binderIdent| $s:ident) := h then
          lctx := lctx.setUserName fvar.fvarId! s.getId
        Expr.addLocalVarInfoForBinderIdent fvar h
      Meta.withLCtx lctx (← Meta.getLocalInstances) do
        let g' ← Meta.mkFreshExprSyntheticOpaqueMVar (← g.getType) (← g.getTag)
        g.assign g'
        return g'.mvarId!

end Harmonic

set_option maxHeartbeats 10000000

section Specs

-- Never add new imports here

set_option maxHeartbeats 10000000

set_option pp.coercions false

/- Problem Description
    MergeIntervals: merge all overlapping closed intervals in a sorted array.
    Natural language breakdown:
    1. The input is an array of intervals, each interval is a pair (start, end) of integers.
    2. Each interval is interpreted as a closed interval [start, end].
    3. Valid intervals satisfy start ≤ end.
    4. The input is sorted lexicographically by (start, end) in nondecreasing order.
    5. Two intervals overlap if the next start is ≤ the previous end (touching at a point counts as overlap).
    6. The output is an array of intervals that are pairwise non-overlapping (separated) and sorted.
    7. The output intervals cover exactly the same set of integer points as the input intervals.
    8. The output is a canonical merging: it is non-overlapping and each interval is maximal (cannot be extended without losing correctness).
    Your algorithm should run in **O(n)** time and **O(n)** extra space.
-/

-- An interval is a pair (start, end).
abbrev Interval := Int × Int

-- Accessors (keep specs readable)
def istart (iv : Interval) : Int := iv.1

def iend (iv : Interval) : Int := iv.2

-- Membership of an integer point in a closed interval
-- Uses Int inequalities; we reason over integer points only.
def InInterval (x : Int) (iv : Interval) : Prop :=
  istart iv ≤ x ∧ x ≤ iend iv

-- An array is lex-sorted by (start, end)
-- We use adjacent-pair monotonicity, which is simple and decidable.
def LexSortedIntervals (a : Array Interval) : Prop :=
  ∀ (i : Nat), i + 1 < a.size →
    (istart a[i]! < istart a[i+1]! ) ∨
    (istart a[i]! = istart a[i+1]! ∧ iend a[i]! ≤ iend a[i+1]! ) ∨
    (istart a[i]! = istart a[i+1]! ∧ iend a[i]! = iend a[i+1]! )

-- Validity: every interval has start ≤ end
-- (Input may be empty; then this is trivially true.)
def AllValid (a : Array Interval) : Prop :=
  ∀ (i : Nat), i < a.size → istart a[i]! ≤ iend a[i]!

-- Output property: intervals are strictly separated (no overlap, no touching)
-- i.e., end_i < start_{i+1}
def StrictlyNonOverlapping (a : Array Interval) : Prop :=
  ∀ (i : Nat), i + 1 < a.size → iend a[i]! < istart a[i+1]!

-- Output is sorted by starts (and ends as tiebreaker is vacuous under strict separation,
-- but we also require nondecreasing starts for robustness).
def NondecreasingStarts (a : Array Interval) : Prop :=
  ∀ (i : Nat), i + 1 < a.size → istart a[i]! ≤ istart a[i+1]!

-- Coverage equivalence over integer points.
-- x is covered by an array iff it is in some interval of the array.
def CoveredBy (x : Int) (a : Array Interval) : Prop :=
  ∃ (i : Nat), i < a.size ∧ InInterval x a[i]!

-- Maximality / canonical merge: no interval in the result can be extended while preserving
-- non-overlap and coverage equivalence.
-- We phrase this as: for each resulting interval, its start is the minimum covered point within
-- its connected component and its end is the maximum covered point within that component.
-- A simpler characterization that avoids heavy connected-component reasoning:
--   - Every result interval's start is covered by the input.
--   - Every result interval's end is covered by the input.
--   - Every integer point between start and end is covered by the input.
-- Together with strict non-overlap, this pins down the unique merged output.
def IntervalIsTight (input : Array Interval) (iv : Interval) : Prop :=
  CoveredBy (istart iv) input ∧
  CoveredBy (iend iv) input ∧
  (∀ (x : Int), istart iv ≤ x ∧ x ≤ iend iv → CoveredBy x input)

-- Preconditions and postconditions

def precondition (intervals : Array Interval) : Prop :=
  AllValid intervals ∧ LexSortedIntervals intervals

def postcondition (intervals : Array Interval) (result : Array Interval) : Prop :=
  AllValid result ∧
  NondecreasingStarts result ∧
  StrictlyNonOverlapping result ∧
  -- exact coverage equivalence
  (∀ (x : Int), CoveredBy x result ↔ CoveredBy x intervals) ∧
  -- canonical/tight intervals (prevents splitting into smaller disjoint intervals)
  (∀ (i : Nat), i < result.size → IntervalIsTight intervals result[i]!)

end Specs

section Impl

def implementation (intervals : Array Interval) : Array Interval :=
  -- Standard linear merge over an already lex-sorted array.
  -- Avoid using any helper functions from the Specs section (e.g. `istart`, `iend`).
  intervals.foldl
    (fun acc iv =>
      match acc.size with
      | 0 => acc.push iv
      | _ + 1 =>
        let lastIdx := acc.size - 1
        let last := acc[lastIdx]!
        let s : Int := iv.1
        let e : Int := iv.2
        let ls : Int := last.1
        let le : Int := last.2
        if s ≤ le then
          let newEnd : Int := if le < e then e else le
          acc.set! lastIdx (ls, newEnd)
        else
          acc.push iv)
    #[]

end Impl

section TestCases

-- Test case 1: Example 1 from prompt
-- intervals = [[1,3],[2,6],[8,10],[15,18]] -> [[1,6],[8,10],[15,18]]
def test1_intervals : Array Interval := #[(1,3),(2,6),(8,10),(15,18)]

def test1_Expected : Array Interval := #[(1,6),(8,10),(15,18)]

-- Test case 2: Example 2 from prompt (touching counts as overlap)
def test2_intervals : Array Interval := #[(1,4),(4,5)]

def test2_Expected : Array Interval := #[(1,5)]

-- Test case 3: Empty input

def test3_intervals : Array Interval := #[]

def test3_Expected : Array Interval := #[]

-- Test case 4: Single interval

def test4_intervals : Array Interval := #[(7,7)]

def test4_Expected : Array Interval := #[(7,7)]

-- Test case 5: Already non-overlapping (strictly separated)

def test5_intervals : Array Interval := #[(1,2),(4,4),(6,9)]

def test5_Expected : Array Interval := #[(1,2),(4,4),(6,9)]

-- Test case 6: Chain of overlaps that collapses into one

def test6_intervals : Array Interval := #[(1,3),(2,4),(4,8),(8,9)]

def test6_Expected : Array Interval := #[(1,9)]

-- Test case 7: Same start, increasing ends (lex sorted) merges

def test7_intervals : Array Interval := #[(1,2),(1,3),(1,10)]

def test7_Expected : Array Interval := #[(1,10)]

-- Test case 8: Negative coordinates

def test8_intervals : Array Interval := #[(-10,-5),(-6,-1),(0,0)]

def test8_Expected : Array Interval := #[(-10,-1),(0,0)]

-- Test case 9: Nested intervals

def test9_intervals : Array Interval := #[(1,10),(2,3),(4,5),(6,7)]

def test9_Expected : Array Interval := #[(1,10)]

end TestCases

section Proof

noncomputable section AristotleLemmas

/-
Extracts the step function of the fold in `implementation` into a separate definition `mergeStep` and proves that `implementation` is equivalent to folding `mergeStep`.
-/
def mergeStep (acc : Array Interval) (iv : Interval) : Array Interval :=
  match acc.size with
  | 0 => acc.push iv
  | _ + 1 =>
    let lastIdx := acc.size - 1
    let last := acc[lastIdx]!
    if iv.1 ≤ last.2 then
      acc.set! lastIdx (last.1, if last.2 < iv.2 then iv.2 else last.2)
    else
      acc.push iv

theorem implementation_eq (intervals : Array Interval) :
  implementation intervals = intervals.foldl mergeStep #[] := by
  congr! 2

/-
Proves that if intervals are valid and strictly non-overlapping, they are sorted by start time.
-/
lemma strictly_implies_nondecreasing (a : Array Interval) (h_valid : AllValid a) (h_strict : StrictlyNonOverlapping a) :
  NondecreasingStarts a := by
  exact fun i hi => le_of_lt <| lt_of_le_of_lt ( h_valid _ <| by linarith ) ( h_strict _ hi )

/-
Proves that if the result has equivalent coverage to the input and is valid, then every interval in the result is tight (covered by input).
-/
lemma tight_of_covered_equiv (intervals result : Array Interval)
  (h_valid : AllValid result)
  (h_strict : StrictlyNonOverlapping result)
  (h_equiv : ∀ x, CoveredBy x result ↔ CoveredBy x intervals) :
  ∀ i, i < result.size → IntervalIsTight intervals result[i]! := by
  intro i hi
  constructor;
  · rw [ ← h_equiv ];
    exact ⟨ i, hi, by unfold InInterval; exact ⟨ by unfold istart; aesop, by unfold iend; exact ( h_valid i hi ) ⟩ ⟩;
  · constructor;
    · exact h_equiv _ |>.1 ⟨ i, hi, ⟨ by linarith [ h_valid i hi ], by linarith [ h_valid i hi ] ⟩ ⟩;
    · exact fun x hx => h_equiv x |>.1 ⟨ i, hi, hx ⟩

/-
Defines the loop invariant `MergeInv`. It asserts validity, strict separation, coverage equivalence, and a condition relating the last interval of the accumulator to the last processed interval (crucial for sortedness).
-/
def MergeInv (processed : List Interval) (acc : Array Interval) : Prop :=
  AllValid acc ∧
  StrictlyNonOverlapping acc ∧
  (∀ x, CoveredBy x acc ↔ CoveredBy x processed.toArray) ∧
  (acc.size > 0 → ∃ last, processed.getLast? = some last ∧ acc[acc.size-1]!.1 ≤ last.1)

/-
Proves that `mergeStep` preserves the `AllValid` property.
-/
lemma step_preserves_valid (acc : Array Interval) (iv : Interval)
  (h_acc_valid : AllValid acc)
  (h_iv_valid : iv.1 ≤ iv.2) :
  AllValid (mergeStep acc iv) := by
  unfold mergeStep;
  rcases n : acc.size <;> simp_all +decide [ AllValid ];
  · exact h_iv_valid;
  · split_ifs <;> simp_all +decide [ Array.setIfInBounds ];
    · intro i hi; by_cases hi' : i = ‹_› <;> simp_all +decide [ Array.set ] ;
      by_cases hi' : i = ‹_› <;> simp_all +decide [ List.getElem_set ];
      split_ifs <;> simp_all +decide [ istart, iend ];
      linarith [ h_acc_valid i ( by linarith ) ];
    · intro i hi; rcases lt_or_eq_of_le ( Nat.le_of_lt_succ hi ) with h | rfl <;> simp_all +decide [ Array.getElem_push ] ;
      exact?

/-
Proves that `mergeStep` preserves the `StrictlyNonOverlapping` property.
-/
lemma step_preserves_strict (acc : Array Interval) (iv : Interval)
  (h_strict : StrictlyNonOverlapping acc)
  (h_iv_valid : iv.1 ≤ iv.2) :
  StrictlyNonOverlapping (mergeStep acc iv) := by
  intro i hi;
  unfold mergeStep at hi ⊢;
  rcases acc with ⟨ ⟨ l ⟩ ⟩ <;> simp_all +decide [ StrictlyNonOverlapping ];
  split_ifs <;> simp_all +decide [ List.getElem_append ];
  · convert h_strict i hi using 1;
    · rw [ List.getElem?_set ] ; aesop;
    · rw [ List.getElem_set ] ; aesop;
  · cases lt_or_eq_of_le ( Nat.le_of_lt_succ hi ) <;> simp_all +decide [ List.getElem?_append ];
    · grind;
    · simp_all +decide [ List.getElem?_append, List.getElem?_cons ];
      cases ‹List Interval› <;> aesop

/-
Proves that `mergeStep` updates the coverage correctly: the new coverage is the union of the old coverage and the new interval.
-/
lemma step_preserves_coverage (acc : Array Interval) (iv : Interval)
  (h_acc_valid : AllValid acc)
  (h_iv_valid : iv.1 ≤ iv.2)
  (h_last_le : acc.size > 0 → istart acc[acc.size-1]! ≤ istart iv) :
  ∀ x, CoveredBy x (mergeStep acc iv) ↔ CoveredBy x acc ∨ InInterval x iv := by
  -- Unfold the definition of `mergeStep` to split into cases based on the size of `acc`.
  unfold mergeStep;
  rcases n : acc.size with ( _ | n ) <;> simp_all +decide [ CoveredBy, InInterval ];
  intro x; split_ifs <;> simp_all +decide [ Array.setIfInBounds, Array.push ] ;
  · constructor <;> intro h;
    · rcases h with ⟨ i, hi, hi', hi'' ⟩ ; rcases eq_or_lt_of_le ( Nat.le_of_lt_succ hi ) with rfl | hi <;> simp_all +decide [ Array.set ] ;
      · by_cases h_cases : x ≤ acc[i].2;
        · exact Or.inl ⟨ i, Nat.lt_succ_self _, by simpa [ show acc[i]! = acc[i] from by { exact? } ] using hi', by simpa [ show acc[i]! = acc[i] from by { exact? } ] using h_cases ⟩;
        · exact Or.inr ⟨ by linarith! [ show istart ( acc[i].1, iv.2 ) = acc[i].1 from rfl ], by linarith! [ show iend ( acc[i].1, iv.2 ) = iv.2 from rfl ] ⟩;
      · rw [ List.getElem_set ] at hi' hi'' ; aesop;
    · rcases h with ( ⟨ i, hi, hi', hi'' ⟩ | ⟨ hi, hi' ⟩ );
      · use i;
        cases lt_or_eq_of_le ( Nat.le_of_lt_succ hi ) <;> simp_all +decide [ Array.set ];
        · grind;
        · exact ⟨ hi', by linarith! ⟩;
      · use ‹_›; simp_all +decide [ Array.set ] ;
        exact ⟨ by linarith! [ h_last_le ], by linarith! [ hi' ] ⟩;
  · intro hx₁ hx₂; use ‹_›; simp_all +decide [ istart, iend ] ;
    constructor <;> linarith;
  · constructor <;> intro h;
    · grind;
    · rcases h with ( ⟨ i, hi, hi' ⟩ | ⟨ hi, hi' ⟩ ) <;> [ exact ⟨ i, by linarith, by
        rw [ List.getElem?_append ] ; aesop ⟩ ; exact ⟨ acc.size, by linarith, by
        aesop ⟩ ]

/-
Proves that `mergeStep` maintains the condition that the last interval in the accumulator starts no later than the last processed interval.
-/
lemma step_preserves_last_start (acc : Array Interval) (processed : List Interval) (iv : Interval)
  (h_inv_last : acc.size > 0 → ∃ last, processed.getLast? = some last ∧ acc[acc.size-1]!.1 ≤ last.1)
  (h_sorted : ∀ last, processed.getLast? = some last → last.1 ≤ iv.1) :
  (mergeStep acc iv).size > 0 → ∃ last, (processed ++ [iv]).getLast? = some last ∧ (mergeStep acc iv)[(mergeStep acc iv).size-1]!.1 ≤ last.1 := by
  cases h : acc.size <;> simp_all +decide [ mergeStep ];
  grind +ring

/-
Proves that `mergeStep` maintains the invariant `MergeInv` by combining the previously proved preservation lemmas.
-/
lemma step_preserves_Inv (acc : Array Interval) (processed : List Interval) (iv : Interval)
  (h_inv : MergeInv processed acc)
  (h_sorted : ∀ last, processed.getLast? = some last → last.1 ≤ iv.1)
  (h_iv_valid : iv.1 ≤ iv.2) :
  MergeInv (processed ++ [iv]) (mergeStep acc iv) := by
  refine' ⟨ _, _, _, _ ⟩;
  · exact step_preserves_valid acc iv h_inv.1 h_iv_valid;
  · exact step_preserves_strict acc iv h_inv.2.1 h_iv_valid;
  · intro x;
    convert step_preserves_coverage acc iv h_inv.1 h_iv_valid _ using 1;
    · constructor;
      · intro h x; exact step_preserves_coverage acc iv h_inv.1 h_iv_valid (by
        intro h_pos
        obtain ⟨last, h_last⟩ := h_inv.2.2.2 h_pos
        have h_last_le : last.1 ≤ iv.1 := by
          exact h_sorted last h_last.1
        exact h_last_le.trans' (by
        exact h_last.2)) x;
      · intro h;
        rw [ h, h_inv.2.2.1 ];
        simp +decide [ CoveredBy ];
        constructor <;> intro h;
        · rcases h with ( ⟨ i, hi, hi' ⟩ | hi' ) <;> [ exact ⟨ i, Nat.lt_succ_of_lt hi, by simpa [ List.getElem?_append, hi ] using hi' ⟩ ; exact ⟨ processed.length, Nat.lt_succ_self _, by simpa [ List.getElem?_append ] using hi' ⟩ ];
        · rcases h with ⟨ i, hi, hi' ⟩ ; cases lt_or_eq_of_le ( Nat.le_of_lt_succ hi ) <;> aesop;
    · exact fun h => le_trans ( h_inv.2.2.2 h |> Classical.choose_spec |> And.right ) ( h_sorted _ ( h_inv.2.2.2 h |> Classical.choose_spec |> And.left ) );
  · exact step_preserves_last_start acc processed iv h_inv.2.2.2 h_sorted

end AristotleLemmas

theorem correctness_goal (intervals : Array Interval) (h_precond : precondition intervals) : postcondition intervals (implementation (intervals)) := by
    have h_mergeStep_preserves_inv : ∀ (processed : List Interval) (acc : Array Interval), (∀ iv ∈ processed, iv.1 ≤ iv.2) → MergeInv processed acc → ∀ (iv : Interval), iv.1 ≤ iv.2 → (∀ last ∈ processed, last.1 ≤ iv.1) → MergeInv (processed ++ [iv]) (mergeStep acc iv) := by
      intros processed acc h_processed_valid h_merge_inv iv h_iv_valid h_iv_sorted
      apply step_preserves_Inv acc processed iv h_merge_inv (fun last h_last => by
        exact h_iv_sorted last ( List.mem_of_mem_getLast? h_last )) h_iv_valid;
    -- By induction on the list of intervals, we can show that the invariant holds for the final result.
    have h_induction : ∀ (processed : List Interval), (∀ iv ∈ processed, iv.1 ≤ iv.2) → (∀ i j : ℕ, i < j → j < processed.length → processed[i]!.1 ≤ processed[j]!.1) → MergeInv processed (processed.foldl mergeStep #[]) := by
      intro processed h_processed h_sorted;
      induction' processed using List.reverseRecOn with processed ih;
      · constructor <;> norm_num;
        · exact fun i hi => by contradiction;
        · exact fun i hi => by contradiction;
      · simp_all +decide [ List.foldl_append ];
        apply h_mergeStep_preserves_inv processed (List.foldl mergeStep #[] processed) (fun a b hab => h_processed a b (Or.inl hab)) (by
        apply_assumption;
        grind) ih.1 ih.2 (h_processed _ _ (Or.inr rfl)) (fun a b hab => by
          contrapose! h_sorted;
          obtain ⟨ i, hi ⟩ := List.mem_iff_get.mp hab;
          use i.val, processed.length;
          simp_all +decide [ List.getElem?_append, List.getElem?_eq_getElem ]);
    specialize h_induction intervals.toList (by
    simp +zetaDelta at *;
    intro a b hab;
    obtain ⟨ i, hi ⟩ := Array.mem_iff_getElem.mp hab;
    have := h_precond.1 i hi.1; aesop;) (by
    -- By definition of `LexSortedIntervals`, for any `i` and `j` with `i < j`, the interval at `i` is less than or equal to the interval at `j` in the start time.
    intros i j hij hj_lt_length
    have h_lex : ∀ i j : ℕ, i < j → j < intervals.size → intervals[i]!.1 ≤ intervals[j]!.1 := by
      intros i j hij hj_lt_length
      have h_lex : ∀ i : ℕ, i + 1 < intervals.size → intervals[i]!.1 ≤ intervals[i + 1]!.1 := by
        intros i hi; exact (by
        have := h_precond.2 i hi; rcases this with ( h | h | h ) <;> linarith!;)
      generalize_proofs at *; (
      -- By induction on $j - i$, we can show that the start time of the interval at $i$ is less than or equal to the start time of the interval at $j$.
      induction' hij with j hj ih; aesop; (
      exact le_trans ( ih ( Nat.lt_of_succ_lt hj_lt_length ) ) ( h_lex _ hj_lt_length )));
    grind +ring);
    constructor;
    · convert h_induction.1 using 1;
      convert implementation_eq intervals;
      exact?;
    · refine' ⟨ _, _, _, _ ⟩;
      · convert strictly_implies_nondecreasing _ h_induction.1 h_induction.2.1 using 1;
        convert implementation_eq intervals;
        exact?;
      · convert h_induction.2.1 using 1;
        convert implementation_eq intervals;
        exact?;
      · convert h_induction.2.2.1 using 1;
        unfold CoveredBy; aesop;
      · convert tight_of_covered_equiv intervals ( List.foldl mergeStep #[] intervals.toList ) _ _ _ using 1;
        · rw [ implementation_eq ];
          grind;
        · exact h_induction.1;
        · exact h_induction.2.1;
        · convert h_induction.2.2.1 using 1

end Proof