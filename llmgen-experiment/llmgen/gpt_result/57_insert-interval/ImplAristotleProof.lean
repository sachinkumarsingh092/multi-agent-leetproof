/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 21b065af-633a-4a0c-8088-1a69f5acac2b

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem goal_5 (intervals : Array Interval) (newInterval : Interval) (require_1 : precondition intervals newInterval) (curEnd : ℤ) (curStart : ℤ) (i : ℕ) (inserted : Bool) (res : Array Interval) (invariant_inv_i_bounds : i ≤ intervals.size) (invariant_inv_pending_wf : curStart ≤ curEnd) (invariant_inv_res_canonical : canonical res) (invariant_inv_last_before_next_input : i < intervals.size → res.size = OfNat.ofNat 0 ∨ iend res[res.size - OfNat.ofNat 1]! < istart intervals[i]!) (invariant_inv_last_before_pending : inserted = false → res.size = OfNat.ofNat 0 ∨ iend res[res.size - OfNat.ofNat 1]! < curStart) (invariant_inv_coverage : ∀ (x : ℤ), coveredBy x res ∨ inserted = false ∧ memInterval x (curStart, curEnd) ↔ coveredBy x (intervals.extract (OfNat.ofNat 0) i) ∨ memInterval x newInterval) (invariant_inv_inserted_has_pending : inserted = true → ∃ j < res.size, res[j]! = (curStart, curEnd)) (if_pos : i < intervals.size) (if_neg : ¬inserted = true) (if_neg_1 : ¬iend intervals[i]! < curStart) (if_neg_2 : ¬curEnd < istart intervals[i]!) (if_pos_1 : istart intervals[i]! < curStart) (if_pos_2 : curEnd < iend intervals[i]!) : ∀ (x : ℤ), coveredBy x res ∨ inserted = false ∧ memInterval x (istart intervals[i]!, iend intervals[i]!) ↔ coveredBy x (intervals.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) ∨ memInterval x newInterval

- theorem goal_6 (intervals : Array Interval) (newInterval : Interval) (require_1 : precondition intervals newInterval) (curEnd : ℤ) (curStart : ℤ) (i : ℕ) (inserted : Bool) (res : Array Interval) (invariant_inv_i_bounds : i ≤ intervals.size) (invariant_inv_pending_wf : curStart ≤ curEnd) (invariant_inv_res_canonical : canonical res) (invariant_inv_last_before_next_input : i < intervals.size → res.size = OfNat.ofNat 0 ∨ iend res[res.size - OfNat.ofNat 1]! < istart intervals[i]!) (invariant_inv_last_before_pending : inserted = false → res.size = OfNat.ofNat 0 ∨ iend res[res.size - OfNat.ofNat 1]! < curStart) (invariant_inv_coverage : ∀ (x : ℤ), coveredBy x res ∨ inserted = false ∧ memInterval x (curStart, curEnd) ↔ coveredBy x (intervals.extract (OfNat.ofNat 0) i) ∨ memInterval x newInterval) (invariant_inv_inserted_has_pending : inserted = true → ∃ j < res.size, res[j]! = (curStart, curEnd)) (if_pos : i < intervals.size) (if_neg : ¬inserted = true) (if_neg_1 : ¬iend intervals[i]! < curStart) (if_neg_2 : ¬curEnd < istart intervals[i]!) (if_pos_1 : istart intervals[i]! < curStart) (if_neg_3 : ¬curEnd < iend intervals[i]!) : ∀ (x : ℤ), coveredBy x res ∨ inserted = false ∧ memInterval x (istart intervals[i]!, curEnd) ↔ coveredBy x (intervals.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) ∨ memInterval x newInterval

- theorem goal_7 (intervals : Array Interval) (newInterval : Interval) (require_1 : precondition intervals newInterval) (curEnd : ℤ) (curStart : ℤ) (i : ℕ) (inserted : Bool) (res : Array Interval) (invariant_inv_i_bounds : i ≤ intervals.size) (invariant_inv_pending_wf : curStart ≤ curEnd) (invariant_inv_res_canonical : canonical res) (invariant_inv_last_before_next_input : i < intervals.size → res.size = OfNat.ofNat 0 ∨ iend res[res.size - OfNat.ofNat 1]! < istart intervals[i]!) (invariant_inv_last_before_pending : inserted = false → res.size = OfNat.ofNat 0 ∨ iend res[res.size - OfNat.ofNat 1]! < curStart) (invariant_inv_coverage : ∀ (x : ℤ), coveredBy x res ∨ inserted = false ∧ memInterval x (curStart, curEnd) ↔ coveredBy x (intervals.extract (OfNat.ofNat 0) i) ∨ memInterval x newInterval) (invariant_inv_inserted_has_pending : inserted = true → ∃ j < res.size, res[j]! = (curStart, curEnd)) (if_pos : i < intervals.size) (if_neg : ¬inserted = true) (if_neg_1 : ¬iend intervals[i]! < curStart) (if_neg_2 : ¬curEnd < istart intervals[i]!) (if_neg_3 : ¬istart intervals[i]! < curStart) (if_pos_1 : curEnd < iend intervals[i]!) : ∀ (x : ℤ), coveredBy x res ∨ inserted = false ∧ memInterval x (curStart, iend intervals[i]!) ↔ coveredBy x (intervals.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) ∨ memInterval x newInterval

- theorem goal_8 (intervals : Array Interval) (newInterval : Interval) (require_1 : precondition intervals newInterval) (curEnd : ℤ) (curStart : ℤ) (i : ℕ) (inserted : Bool) (res : Array Interval) (invariant_inv_i_bounds : i ≤ intervals.size) (invariant_inv_pending_wf : curStart ≤ curEnd) (invariant_inv_res_canonical : canonical res) (invariant_inv_last_before_next_input : i < intervals.size → res.size = OfNat.ofNat 0 ∨ iend res[res.size - OfNat.ofNat 1]! < istart intervals[i]!) (invariant_inv_last_before_pending : inserted = false → res.size = OfNat.ofNat 0 ∨ iend res[res.size - OfNat.ofNat 1]! < curStart) (invariant_inv_coverage : ∀ (x : ℤ), coveredBy x res ∨ inserted = false ∧ memInterval x (curStart, curEnd) ↔ coveredBy x (intervals.extract (OfNat.ofNat 0) i) ∨ memInterval x newInterval) (invariant_inv_inserted_has_pending : inserted = true → ∃ j < res.size, res[j]! = (curStart, curEnd)) (if_pos : i < intervals.size) (if_neg : ¬inserted = true) (if_neg_1 : ¬iend intervals[i]! < curStart) (if_neg_2 : ¬curEnd < istart intervals[i]!) (if_neg_3 : ¬istart intervals[i]! < curStart) (if_neg_4 : ¬curEnd < iend intervals[i]!) : ∀ (x : ℤ), coveredBy x res ∨ inserted = false ∧ memInterval x (curStart, curEnd) ↔ coveredBy x (intervals.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) ∨ memInterval x newInterval

- theorem goal_9 (intervals : Array Interval) (newInterval : Interval) (require_1 : precondition intervals newInterval) (i_1 : ℤ) (i_2 : ℤ) (i_3 : ℕ) (res_1 : Array Interval) (invariant_inv_pending_wf : i_2 ≤ i_1) (invariant_inv_i_bounds : i_3 ≤ intervals.size) (done_1 : ¬i_3 < intervals.size) (invariant_inv_res_canonical : canonical res_1) (invariant_inv_last_before_next_input : i_3 < intervals.size → res_1.size = OfNat.ofNat 0 ∨ iend res_1[res_1.size - OfNat.ofNat 1]! < istart intervals[i_3]!) (invariant_inv_last_before_pending : false = false → res_1.size = OfNat.ofNat 0 ∨ iend res_1[res_1.size - OfNat.ofNat 1]! < i_2) (invariant_inv_inserted_has_pending : false = true → ∃ j < res_1.size, res_1[j]! = (i_2, i_1)) (invariant_inv_coverage : ∀ (x : ℤ), coveredBy x res_1 ∨ false = false ∧ memInterval x (i_2, i_1) ↔ coveredBy x (intervals.extract (OfNat.ofNat 0) i_3) ∨ memInterval x newInterval) : postcondition intervals newInterval (res_1.push (i_2, i_1))

- theorem goal_10 (intervals : Array Interval) (newInterval : Interval) (require_1 : precondition intervals newInterval) (i_1 : ℤ) (i_2 : ℤ) (i_3 : ℕ) (i_4 : Bool) (res_1 : Array Interval) (if_neg : ¬i_4 = false) (invariant_inv_pending_wf : i_2 ≤ i_1) (invariant_inv_i_bounds : i_3 ≤ intervals.size) (done_1 : ¬i_3 < intervals.size) (invariant_inv_res_canonical : canonical res_1) (invariant_inv_last_before_next_input : i_3 < intervals.size → res_1.size = OfNat.ofNat 0 ∨ iend res_1[res_1.size - OfNat.ofNat 1]! < istart intervals[i_3]!) (invariant_inv_last_before_pending : i_4 = false → res_1.size = OfNat.ofNat 0 ∨ iend res_1[res_1.size - OfNat.ofNat 1]! < i_2) (invariant_inv_inserted_has_pending : i_4 = true → ∃ j < res_1.size, res_1[j]! = (i_2, i_1)) (invariant_inv_coverage : ∀ (x : ℤ), coveredBy x res_1 ∨ i_4 = false ∧ memInterval x (i_2, i_1) ↔ coveredBy x (intervals.extract (OfNat.ofNat 0) i_3) ∨ memInterval x newInterval) : postcondition intervals newInterval res_1

At Harmonic, we use a modified version of the `generalize_proofs` tactic.
For compatibility, we include this tactic at the start of the file.
If you add the comment "-- Harmonic `generalize_proofs` tactic" to your file, we will not do this.
-/

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

-- Never add new imports here

set_option maxHeartbeats 10000000

set_option pp.coercions false

/- Problem Description
    InsertInterval: insert a new closed interval into a sorted, non-overlapping array of closed intervals,
    merging overlaps, and return the resulting sorted, non-overlapping array.

    Natural language breakdown:
    1. Each interval is a pair (start, end) with start ≤ end.
    2. The input array `intervals` is sorted by start in nondecreasing order.
    3. The input array has no overlaps: every interval ends strictly before the next begins.
    4. A new interval `newInterval` is given and also satisfies start ≤ end.
    5. We must insert `newInterval` and merge any overlapping/touching intervals so the result has no overlaps.
    6. The result must remain sorted by start.
    7. Coverage semantics: the set of integer points covered by the result equals the union of coverage
       of the input intervals and the new interval.
    8. The result must be canonical: sorted, non-overlapping, and each interval has start ≤ end.
       (This uniqueness ensures the output is determined by the covered set.)
    Your algorithm should run in **O(n)** time and **O(n)** extra space.
-/

section Specs

-- Basic interval type: (start, end)
abbrev Interval := Int × Int

-- Accessors
abbrev istart (i : Interval) : Int := i.1

abbrev iend (i : Interval) : Int := i.2

-- Well-formed interval
@[simp] def wfInterval (i : Interval) : Prop := istart i ≤ iend i

-- Array is sorted by start (nondecreasing)
def sortedByStart (a : Array Interval) : Prop :=
  ∀ (i : Nat), i + 1 < a.size → istart a[i]! ≤ istart a[i+1]!

-- No overlaps between consecutive intervals in array
-- We use strict separation: end < next.start.
-- This matches the problem statement “non-overlapping” for closed intervals.
def noOverlapConsecutive (a : Array Interval) : Prop :=
  ∀ (i : Nat), i + 1 < a.size → iend a[i]! < istart a[i+1]!

-- Every interval in array is well-formed

def allWf (a : Array Interval) : Prop :=
  ∀ (i : Nat), i < a.size → wfInterval a[i]!

-- Membership of a point in a closed interval
@[simp] def memInterval (x : Int) (i : Interval) : Prop :=
  istart i ≤ x ∧ x ≤ iend i

-- Point coverage of an interval array
-- (Using an existential over indices is simple and decidable-friendly in SMT contexts.)
def coveredBy (x : Int) (a : Array Interval) : Prop :=
  ∃ (i : Nat), i < a.size ∧ memInterval x a[i]!

-- Canonical form for the output: sorted, no overlaps, and well-formed

def canonical (a : Array Interval) : Prop :=
  sortedByStart a ∧ noOverlapConsecutive a ∧ allWf a

-- Preconditions

def precondition (intervals : Array Interval) (newInterval : Interval) : Prop :=
  canonical intervals ∧ wfInterval newInterval

-- Postconditions

def postcondition (intervals : Array Interval) (newInterval : Interval) (result : Array Interval) : Prop :=
  canonical result ∧
  -- Coverage equivalence: result covers exactly the union of old coverage and new interval coverage
  (∀ (x : Int), coveredBy x result ↔ coveredBy x intervals ∨ memInterval x newInterval) ∧
  -- Minimality/canonicity already implies uniqueness for a given covered set; we add a simple anti-fragmentation:
  -- no two consecutive result intervals can be merged (i.e., they are strictly separated).
  (∀ (i : Nat), i + 1 < result.size → iend result[i]! < istart result[i+1]!)

end Specs

section TestCases

-- Test case 1: Example 1
-- intervals = [[1,3],[6,9]], newInterval = [2,5] => [[1,5],[6,9]]
def test1_intervals : Array Interval := #[(1, 3), (6, 9)]

def test1_newInterval : Interval := (2, 5)

def test1_Expected : Array Interval := #[(1, 5), (6, 9)]

-- Test case 2: Example 2
-- intervals = [[1,2],[3,5],[6,7],[8,10],[12,16]], newInterval = [4,8] => [[1,2],[3,10],[12,16]]
def test2_intervals : Array Interval := #[(1, 2), (3, 5), (6, 7), (8, 10), (12, 16)]

def test2_newInterval : Interval := (4, 8)

def test2_Expected : Array Interval := #[(1, 2), (3, 10), (12, 16)]

-- Test case 3: Empty intervals

def test3_intervals : Array Interval := #[]

def test3_newInterval : Interval := (2, 3)

def test3_Expected : Array Interval := #[(2, 3)]

-- Test case 4: New interval strictly before all, no overlap

def test4_intervals : Array Interval := #[(5, 7), (10, 12)]

def test4_newInterval : Interval := (1, 3)

def test4_Expected : Array Interval := #[(1, 3), (5, 7), (10, 12)]

-- Test case 5: New interval strictly after all, no overlap

def test5_intervals : Array Interval := #[(1, 2), (4, 5)]

def test5_newInterval : Interval := (7, 9)

def test5_Expected : Array Interval := #[(1, 2), (4, 5), (7, 9)]

-- Test case 6: New interval contained inside an existing interval (no change)

def test6_intervals : Array Interval := #[(1, 10)]

def test6_newInterval : Interval := (3, 4)

def test6_Expected : Array Interval := #[(1, 10)]

-- Test case 7: New interval overlaps multiple and merges all into one

def test7_intervals : Array Interval := #[(1, 2), (4, 6), (8, 9)]

def test7_newInterval : Interval := (2, 8)

def test7_Expected : Array Interval := #[(1, 9)]

-- Test case 8: Negative coordinates and merging across zero

def test8_intervals : Array Interval := #[(-10, -5), (-3, -1), (2, 4)]

def test8_newInterval : Interval := (-6, 3)

def test8_Expected : Array Interval := #[(-10, 4)]

-- Test case 9: Singleton intervals array where insertion creates a second interval

def test9_intervals : Array Interval := #[(0, 0)]

def test9_newInterval : Interval := (2, 2)

def test9_Expected : Array Interval := #[(0, 0), (2, 2)]

end TestCases

section Proof

theorem goal_5 (intervals : Array Interval) (newInterval : Interval) (require_1 : precondition intervals newInterval) (curEnd : ℤ) (curStart : ℤ) (i : ℕ) (inserted : Bool) (res : Array Interval) (invariant_inv_i_bounds : i ≤ intervals.size) (invariant_inv_pending_wf : curStart ≤ curEnd) (invariant_inv_res_canonical : canonical res) (invariant_inv_last_before_next_input : i < intervals.size → res.size = OfNat.ofNat 0 ∨ iend res[res.size - OfNat.ofNat 1]! < istart intervals[i]!) (invariant_inv_last_before_pending : inserted = false → res.size = OfNat.ofNat 0 ∨ iend res[res.size - OfNat.ofNat 1]! < curStart) (invariant_inv_coverage : ∀ (x : ℤ), coveredBy x res ∨ inserted = false ∧ memInterval x (curStart, curEnd) ↔ coveredBy x (intervals.extract (OfNat.ofNat 0) i) ∨ memInterval x newInterval) (invariant_inv_inserted_has_pending : inserted = true → ∃ j < res.size, res[j]! = (curStart, curEnd)) (if_pos : i < intervals.size) (if_neg : ¬inserted = true) (if_neg_1 : ¬iend intervals[i]! < curStart) (if_neg_2 : ¬curEnd < istart intervals[i]!) (if_pos_1 : istart intervals[i]! < curStart) (if_pos_2 : curEnd < iend intervals[i]!) : ∀ (x : ℤ), coveredBy x res ∨ inserted = false ∧ memInterval x (istart intervals[i]!, iend intervals[i]!) ↔ coveredBy x (intervals.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) ∨ memInterval x newInterval := by
    simp_all +decide [ memInterval ];
    -- By combining the results from invariant_inv_coverage and the properties of the new interval, we can conclude the proof.
    intros x
    constructor;
    · intro hx;
      cases' hx with hx hx;
      · exact Or.imp ( fun h => by
          obtain ⟨ j, hj₁, hj₂ ⟩ := h;
          use j;
          grind +ring ) id ( invariant_inv_coverage x |>.1 ( Or.inl hx ) );
      · refine' Or.inl ⟨ i, _, _ ⟩ <;> aesop;
    · intro hx;
      contrapose! invariant_inv_coverage;
      use x;
      cases hx <;> simp_all +decide [ coveredBy ];
      · rename_i h;
        obtain ⟨ j, hj₁, hj₂, hj₃ ⟩ := h;
        by_cases hj₄ : j < i;
        · refine' Or.inr ⟨ _, Or.inl ⟨ j, hj₄, _ ⟩ ⟩;
          · grind;
          · grind;
        · grind;
      · grind

theorem goal_6 (intervals : Array Interval) (newInterval : Interval) (require_1 : precondition intervals newInterval) (curEnd : ℤ) (curStart : ℤ) (i : ℕ) (inserted : Bool) (res : Array Interval) (invariant_inv_i_bounds : i ≤ intervals.size) (invariant_inv_pending_wf : curStart ≤ curEnd) (invariant_inv_res_canonical : canonical res) (invariant_inv_last_before_next_input : i < intervals.size → res.size = OfNat.ofNat 0 ∨ iend res[res.size - OfNat.ofNat 1]! < istart intervals[i]!) (invariant_inv_last_before_pending : inserted = false → res.size = OfNat.ofNat 0 ∨ iend res[res.size - OfNat.ofNat 1]! < curStart) (invariant_inv_coverage : ∀ (x : ℤ), coveredBy x res ∨ inserted = false ∧ memInterval x (curStart, curEnd) ↔ coveredBy x (intervals.extract (OfNat.ofNat 0) i) ∨ memInterval x newInterval) (invariant_inv_inserted_has_pending : inserted = true → ∃ j < res.size, res[j]! = (curStart, curEnd)) (if_pos : i < intervals.size) (if_neg : ¬inserted = true) (if_neg_1 : ¬iend intervals[i]! < curStart) (if_neg_2 : ¬curEnd < istart intervals[i]!) (if_pos_1 : istart intervals[i]! < curStart) (if_neg_3 : ¬curEnd < iend intervals[i]!) : ∀ (x : ℤ), coveredBy x res ∨ inserted = false ∧ memInterval x (istart intervals[i]!, curEnd) ↔ coveredBy x (intervals.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) ∨ memInterval x newInterval := by
    intro x;
    by_cases hx : memInterval x (istart intervals[i]!, iend intervals[i]!) <;> simp_all +decide [ memInterval ];
    · contrapose! invariant_inv_coverage;
      use x; simp_all +decide [ coveredBy ] ;
      rcases invariant_inv_coverage with ( ⟨ h₁, h₂, h₃ ⟩ | ⟨ h₁, h₂ ⟩ ) <;> simp_all +decide [ OfNat.ofNat ];
      · exact absurd ( h₂ i ( Nat.lt_succ_self _ ) if_pos hx.1 ) ( by linarith );
      · exact absurd h₁.2 ( by erw [ show iend ( istart intervals[i], curEnd ) = curEnd from rfl ] ; linarith );
    · convert invariant_inv_coverage x using 1;
      · constructor <;> intro h <;> cases h <;> simp_all +decide [ coveredBy ];
        · exact Or.inr ( by linarith! );
        · exact Or.inr ( by linarith! );
      · constructor <;> intro <;> simp_all +decide [ coveredBy ];
        · rcases ‹_› with ( ⟨ j, hj₁, hj₂, hj₃ ⟩ | hj₁ ) <;> simp_all +decide [ Array.getElem_extract ];
          by_cases hj : j < i;
          · refine Or.inl ⟨ j, hj, ?_, ?_ ⟩ <;> simp_all +decide [ Array.getElem_extract ];
          · grind;
        · -- If the first part of the disjunction is true, then there exists some i_1 such that i_1 < i and the interval at i_1 in the extracted array is covered by x. Since the extracted array is a subset of the original intervals, this should hold.
          cases' ‹_› with h h;
          · obtain ⟨ j, hj₁, hj₂, hj₃ ⟩ := h; use Or.inl ⟨ j, ⟨ by linarith, by linarith ⟩, ?_, ?_ ⟩ <;> simp_all +decide [ Array.getElem_extract ] ;
            · grind;
            · grind;
          · exact Or.inr h

theorem goal_7 (intervals : Array Interval) (newInterval : Interval) (require_1 : precondition intervals newInterval) (curEnd : ℤ) (curStart : ℤ) (i : ℕ) (inserted : Bool) (res : Array Interval) (invariant_inv_i_bounds : i ≤ intervals.size) (invariant_inv_pending_wf : curStart ≤ curEnd) (invariant_inv_res_canonical : canonical res) (invariant_inv_last_before_next_input : i < intervals.size → res.size = OfNat.ofNat 0 ∨ iend res[res.size - OfNat.ofNat 1]! < istart intervals[i]!) (invariant_inv_last_before_pending : inserted = false → res.size = OfNat.ofNat 0 ∨ iend res[res.size - OfNat.ofNat 1]! < curStart) (invariant_inv_coverage : ∀ (x : ℤ), coveredBy x res ∨ inserted = false ∧ memInterval x (curStart, curEnd) ↔ coveredBy x (intervals.extract (OfNat.ofNat 0) i) ∨ memInterval x newInterval) (invariant_inv_inserted_has_pending : inserted = true → ∃ j < res.size, res[j]! = (curStart, curEnd)) (if_pos : i < intervals.size) (if_neg : ¬inserted = true) (if_neg_1 : ¬iend intervals[i]! < curStart) (if_neg_2 : ¬curEnd < istart intervals[i]!) (if_neg_3 : ¬istart intervals[i]! < curStart) (if_pos_1 : curEnd < iend intervals[i]!) : ∀ (x : ℤ), coveredBy x res ∨ inserted = false ∧ memInterval x (curStart, iend intervals[i]!) ↔ coveredBy x (intervals.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) ∨ memInterval x newInterval := by
    intro x; specialize invariant_inv_coverage x; by_cases hx : memInterval x ( curStart, curEnd ) <;> by_cases hx' : memInterval x ( curStart, iend intervals[i]! ) <;> simp_all +decide ;
    · cases invariant_inv_coverage <;> simp_all +decide [ coveredBy ];
      obtain ⟨ j, hj₁, hj₂, hj₃ ⟩ := ‹_›; use Or.inl ⟨ j, ⟨ by linarith, by linarith ⟩, ?_, ?_ ⟩ <;> simp_all +decide [ Array.getElem_extract ] ;
      · grind;
      · grind +ring;
    · grind +ring;
    · -- If x is in the new interval, then it is covered by the intervals up to i+1.
      by_cases hx'' : x ≤ iend (curStart, curEnd) ∨ istart newInterval ≤ x ∧ x ≤ iend newInterval <;> simp_all +decide [ coveredBy ];
      · cases hx'' <;> simp_all +decide [ OfNat.ofNat ];
        cases invariant_inv_coverage <;> simp_all +decide [ Nat.lt_succ_iff ];
        rcases ‹_› with ⟨ j, hj₁, hj₂, hj₃ ⟩ ; use Or.inl ⟨ j, ⟨ by linarith, by linarith ⟩, ?_, ?_ ⟩ <;> simp_all +decide [ OfNat.ofNat ] ;
        · grind +ring;
        · grind;
      · refine Or.inl ⟨ i, ⟨ Nat.lt_succ_self _, if_pos ⟩, ?_, ?_ ⟩ <;> simp_all +decide [ Array.getElem_extract ];
        exact le_trans if_neg_2 hx''.1.le;
    · convert invariant_inv_coverage using 1 <;> simp +decide [ *, coveredBy ];
      · congr! 2;
        grind +ring;
      · constructor <;> intro h;
        · rcases h with ( ⟨ j, hj₁, hj₂, hj₃ ⟩ | hj₄ ) <;> simp_all +decide [ Nat.lt_succ_iff ];
          cases hj₁.1.eq_or_lt <;> simp_all +decide [ Nat.lt_succ_iff ];
          · exact absurd ( hx' ( by linarith! ) ) ( by linarith! );
          · refine Or.inl ⟨ j, by linarith, ?_, ?_ ⟩ <;> simp_all +decide [ Array.getElem_extract ];
        · -- If h is in the first part, then there's an index j less than i where the interval covers x. Since i is less than the size of the intervals array, j is also less than the size of the intervals array. Therefore, j is also less than i+1. So, the interval at j in the extracted intervals up to i+1 should also cover x.
          cases' h with h h;
          · obtain ⟨ j, hj₁, hj₂, hj₃ ⟩ := h; use Or.inl ⟨ j, ⟨ by linarith, by linarith ⟩, ?_, ?_ ⟩ <;> simp_all +decide [ Array.getElem_extract ] ;
            · grind +ring;
            · grind;
          · exact Or.inr h

theorem goal_8 (intervals : Array Interval) (newInterval : Interval) (require_1 : precondition intervals newInterval) (curEnd : ℤ) (curStart : ℤ) (i : ℕ) (inserted : Bool) (res : Array Interval) (invariant_inv_i_bounds : i ≤ intervals.size) (invariant_inv_pending_wf : curStart ≤ curEnd) (invariant_inv_res_canonical : canonical res) (invariant_inv_last_before_next_input : i < intervals.size → res.size = OfNat.ofNat 0 ∨ iend res[res.size - OfNat.ofNat 1]! < istart intervals[i]!) (invariant_inv_last_before_pending : inserted = false → res.size = OfNat.ofNat 0 ∨ iend res[res.size - OfNat.ofNat 1]! < curStart) (invariant_inv_coverage : ∀ (x : ℤ), coveredBy x res ∨ inserted = false ∧ memInterval x (curStart, curEnd) ↔ coveredBy x (intervals.extract (OfNat.ofNat 0) i) ∨ memInterval x newInterval) (invariant_inv_inserted_has_pending : inserted = true → ∃ j < res.size, res[j]! = (curStart, curEnd)) (if_pos : i < intervals.size) (if_neg : ¬inserted = true) (if_neg_1 : ¬iend intervals[i]! < curStart) (if_neg_2 : ¬curEnd < istart intervals[i]!) (if_neg_3 : ¬istart intervals[i]! < curStart) (if_neg_4 : ¬curEnd < iend intervals[i]!) : ∀ (x : ℤ), coveredBy x res ∨ inserted = false ∧ memInterval x (curStart, curEnd) ↔ coveredBy x (intervals.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) ∨ memInterval x newInterval := by
    simp_all +decide [ coveredBy ];
    intro x;
    constructor <;> intro h;
    · rcases h with ( ⟨ j, hj₁, hj₂, hj₃ ⟩ | ⟨ hj₂, hj₃ ⟩ );
      · refine Or.inl ⟨ j, ⟨ by linarith, by linarith ⟩, ?_, ?_ ⟩ <;> simp_all +decide [ Array.getElem?_eq_getElem ];
        · grind;
        · grind;
      · exact Or.inr ⟨ hj₂, hj₃ ⟩;
    · rcases h with ( ⟨ j, ⟨ hj₁, hj₂ ⟩, hj₃, hj₄ ⟩ | ⟨ hj₃, hj₄ ⟩ ) <;> simp_all +decide [ Nat.lt_succ_iff ];
      cases hj₁.eq_or_lt <;> simp_all +decide [ Nat.lt_succ_iff ];
      · exact invariant_inv_coverage x |>.1 ( Or.inr ⟨ by linarith, by linarith ⟩ );
      · refine' Or.inl ⟨ j, by linarith, _, _ ⟩ <;> simp_all +decide [ Array.getElem_extract ]

theorem goal_9 (intervals : Array Interval) (newInterval : Interval) (require_1 : precondition intervals newInterval) (i_1 : ℤ) (i_2 : ℤ) (i_3 : ℕ) (res_1 : Array Interval) (invariant_inv_pending_wf : i_2 ≤ i_1) (invariant_inv_i_bounds : i_3 ≤ intervals.size) (done_1 : ¬i_3 < intervals.size) (invariant_inv_res_canonical : canonical res_1) (invariant_inv_last_before_next_input : i_3 < intervals.size → res_1.size = OfNat.ofNat 0 ∨ iend res_1[res_1.size - OfNat.ofNat 1]! < istart intervals[i_3]!) (invariant_inv_last_before_pending : false = false → res_1.size = OfNat.ofNat 0 ∨ iend res_1[res_1.size - OfNat.ofNat 1]! < i_2) (invariant_inv_inserted_has_pending : false = true → ∃ j < res_1.size, res_1[j]! = (i_2, i_1)) (invariant_inv_coverage : ∀ (x : ℤ), coveredBy x res_1 ∨ false = false ∧ memInterval x (i_2, i_1) ↔ coveredBy x (intervals.extract (OfNat.ofNat 0) i_3) ∨ memInterval x newInterval) : postcondition intervals newInterval (res_1.push (i_2, i_1)) := by
    refine' ⟨ _, _, _ ⟩ <;> simp_all +decide [ postcondition ];
    · cases invariant_inv_last_before_pending <;> simp_all +decide [ canonical ];
      · unfold sortedByStart noOverlapConsecutive allWf; aesop;
      · refine' ⟨ _, _, _ ⟩ <;> simp_all +decide [ sortedByStart, noOverlapConsecutive, allWf ];
        · grind;
        · grind;
        · grind +ring;
    · -- By definition of `coveredBy`, we know that `coveredBy x (res_1.push (i_2, i_1))` is equivalent to `coveredBy x res_1 ∨ memInterval x (i_2, i_1)`.
      have h_covered_by_push : ∀ x, coveredBy x (res_1.push (i_2, i_1)) ↔ coveredBy x res_1 ∨ memInterval x (i_2, i_1) := by
        -- By definition of `coveredBy`, we can split into cases based on whether the index is in the original array or the new interval.
        intro x
        simp [coveredBy, Array.push];
        constructor <;> intro h <;> simp_all +decide [ List.getElem?_append ] ; (
        rcases h with ⟨ i, hi, hi' ⟩ ; split_ifs at hi' <;> simp_all +decide [ Nat.lt_succ_iff ] ;
        exact Or.inl ⟨ i, by assumption, by simpa [ Array.getElem?_eq_getElem, ‹i < res_1.size› ] using hi' ⟩);
        rcases h with ( ⟨ i, hi, hi' ⟩ | hi ) <;> [ exact ⟨ i, Nat.lt_succ_of_lt hi, by aesop ⟩ ; exact ⟨ res_1.size, Nat.lt_succ_self _, by aesop ⟩ ] ;
      generalize_proofs at *; (
      cases le_antisymm done_1 invariant_inv_i_bounds ; aesop ( simp_config := { singlePass := true } ) ;);
    · cases invariant_inv_last_before_pending <;> simp_all +decide [ Array.push ];
      intro i hi; by_cases hi' : i < res_1.size - 1 <;> simp_all +decide [ List.getElem?_append, Nat.lt_succ_iff ] ;
      · convert invariant_inv_res_canonical.2.1 i _ using 1 ; aesop;
        · grind;
        · exact Nat.lt_pred_iff.mp hi';
      · cases hi'.lt_or_eq <;> first | linarith | aesop;

theorem goal_10 (intervals : Array Interval) (newInterval : Interval) (require_1 : precondition intervals newInterval) (i_1 : ℤ) (i_2 : ℤ) (i_3 : ℕ) (i_4 : Bool) (res_1 : Array Interval) (if_neg : ¬i_4 = false) (invariant_inv_pending_wf : i_2 ≤ i_1) (invariant_inv_i_bounds : i_3 ≤ intervals.size) (done_1 : ¬i_3 < intervals.size) (invariant_inv_res_canonical : canonical res_1) (invariant_inv_last_before_next_input : i_3 < intervals.size → res_1.size = OfNat.ofNat 0 ∨ iend res_1[res_1.size - OfNat.ofNat 1]! < istart intervals[i_3]!) (invariant_inv_last_before_pending : i_4 = false → res_1.size = OfNat.ofNat 0 ∨ iend res_1[res_1.size - OfNat.ofNat 1]! < i_2) (invariant_inv_inserted_has_pending : i_4 = true → ∃ j < res_1.size, res_1[j]! = (i_2, i_1)) (invariant_inv_coverage : ∀ (x : ℤ), coveredBy x res_1 ∨ i_4 = false ∧ memInterval x (i_2, i_1) ↔ coveredBy x (intervals.extract (OfNat.ofNat 0) i_3) ∨ memInterval x newInterval) : postcondition intervals newInterval res_1 := by
    -- By definition of `postcondition`, we need to show that `res_1` is canonical and covers the union of the original intervals and the new interval.
    apply And.intro invariant_inv_res_canonical;
    -- By definition of `postcondition`, we need to show that `res_1` is canonical and covers the union of the original intervals and the new interval. We already have the coverage equivalence from `invariant_inv_coverage`.
    apply And.intro;
    · cases eq_or_lt_of_le invariant_inv_i_bounds <;> aesop;
    · exact invariant_inv_res_canonical.2.1

end Proof