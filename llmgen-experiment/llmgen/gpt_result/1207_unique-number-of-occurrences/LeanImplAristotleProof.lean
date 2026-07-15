/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: d527b685-09c9-4026-8145-70b591c63d70

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem correctness_goal_0_0 (arr : Array ℤ) (h_precond : precondition arr) : implementation.checkCounts
      (Array.foldl
        (fun freq x =>
          if h : (x + 1000).toNat < freq.size then freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
          else freq)
        (mkArray 2001 0) arr)
      0 (mkArray (arr.size + 1) false) =
    true ↔
  ∀ (i j : ℕ),
    i <
        (Array.foldl
            (fun freq x =>
              if h : (x + 1000).toNat < freq.size then freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
              else freq)
            (mkArray 2001 0) arr).size →
      j <
          (Array.foldl
              (fun freq x =>
                if h : (x + 1000).toNat < freq.size then
                  freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
                else freq)
              (mkArray 2001 0) arr).size →
        i ≠ j →
          (Array.foldl
                    (fun freq x =>
                      if h : (x + 1000).toNat < freq.size then
                        freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
                      else freq)
                    (mkArray 2001 0) arr).get!
                i ≠
              0 →
            (Array.foldl
                      (fun freq x =>
                        if h : (x + 1000).toNat < freq.size then
                          freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
                        else freq)
                      (mkArray 2001 0) arr).get!
                  j ≠
                0 →
              (Array.foldl
                      (fun freq x =>
                        if h : (x + 1000).toNat < freq.size then
                          freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
                        else freq)
                      (mkArray 2001 0) arr).get!
                  i ≠
                (Array.foldl
                      (fun freq x =>
                        if h : (x + 1000).toNat < freq.size then
                          freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
                        else freq)
                      (mkArray 2001 0) arr).get!
                  j

- theorem correctness_goal_0_1 (arr : Array ℤ) (h_precond : precondition arr) (h_checkCounts_spec : implementation.checkCounts
      (Array.foldl
        (fun freq x =>
          if h : (x + 1000).toNat < freq.size then freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
          else freq)
        (mkArray 2001 0) arr)
      0 (mkArray (arr.size + 1) false) =
    true ↔
  ∀ (i j : ℕ),
    i <
        (Array.foldl
            (fun freq x =>
              if h : (x + 1000).toNat < freq.size then freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
              else freq)
            (mkArray 2001 0) arr).size →
      j <
          (Array.foldl
              (fun freq x =>
                if h : (x + 1000).toNat < freq.size then
                  freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
                else freq)
              (mkArray 2001 0) arr).size →
        i ≠ j →
          (Array.foldl
                    (fun freq x =>
                      if h : (x + 1000).toNat < freq.size then
                        freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
                      else freq)
                    (mkArray 2001 0) arr).get!
                i ≠
              0 →
            (Array.foldl
                      (fun freq x =>
                        if h : (x + 1000).toNat < freq.size then
                          freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
                        else freq)
                      (mkArray 2001 0) arr).get!
                  j ≠
                0 →
              (Array.foldl
                      (fun freq x =>
                        if h : (x + 1000).toNat < freq.size then
                          freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
                        else freq)
                      (mkArray 2001 0) arr).get!
                  i ≠
                (Array.foldl
                      (fun freq x =>
                        if h : (x + 1000).toNat < freq.size then
                          freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
                        else freq)
                      (mkArray 2001 0) arr).get!
                  j) : (∀ (i j : ℕ),
    i <
        (Array.foldl
            (fun freq x =>
              if h : (x + 1000).toNat < freq.size then freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
              else freq)
            (mkArray 2001 0) arr).size →
      j <
          (Array.foldl
              (fun freq x =>
                if h : (x + 1000).toNat < freq.size then
                  freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
                else freq)
              (mkArray 2001 0) arr).size →
        i ≠ j →
          (Array.foldl
                    (fun freq x =>
                      if h : (x + 1000).toNat < freq.size then
                        freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
                      else freq)
                    (mkArray 2001 0) arr).get!
                i ≠
              0 →
            (Array.foldl
                      (fun freq x =>
                        if h : (x + 1000).toNat < freq.size then
                          freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
                        else freq)
                      (mkArray 2001 0) arr).get!
                  j ≠
                0 →
              (Array.foldl
                      (fun freq x =>
                        if h : (x + 1000).toNat < freq.size then
                          freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
                        else freq)
                      (mkArray 2001 0) arr).get!
                  i ≠
                (Array.foldl
                      (fun freq x =>
                        if h : (x + 1000).toNat < freq.size then
                          freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
                        else freq)
                      (mkArray 2001 0) arr).get!
                  j) ↔
  countsAreUnique arr

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
    1207. Unique Number of Occurrences: decide whether all element-frequency counts in an integer array are pairwise distinct.
    **Important: complexity should be O(n + R²) time and O(R) space**, where R = 2001 is the range of values.
    Natural language breakdown:
    1. Input is an array of integers.
    2. For each integer value v that appears in the array, define occ(v) as the number of indices i with arr[i] = v.
    3. The output is true exactly when for any two distinct values x and y that both appear in the array, occ(x) ≠ occ(y).
    4. Values that do not appear in the array are irrelevant to the uniqueness condition.
    5. The given constraints restrict each element to the range [-1000, 1000].
-/

-- Helper predicate for the stated input-range constraint.
def inProblemRange (x : Int) : Prop :=
  (-1000 ≤ x) ∧ (x ≤ 1000)

-- The core semantic property: occurrence counts are unique among values that appear.
def countsAreUnique (arr : Array Int) : Prop :=
  ∀ (x : Int) (y : Int), x ≠ y → x ∈ arr → y ∈ arr → arr.count x ≠ arr.count y

-- Preconditions
-- We adopt the problem's stated range constraint as an explicit precondition.
def precondition (arr : Array Int) : Prop :=
  ∀ (i : Nat), i < arr.size → inProblemRange (arr[i]!)

-- Postconditions
-- result is true iff the array has unique occurrence counts among all values that appear.
def postcondition (arr : Array Int) (result : Bool) : Prop :=
  (result = true ↔ countsAreUnique arr)

end Specs

section Impl

def implementation (arr : Array Int) : Bool :=
  -- Range size R = 2001 for values in [-1000, 1000].
  let R : Nat := 2001
  let offset : Int := 1000
  let idxOf (x : Int) : Nat := Int.toNat (x + offset)

  -- Update frequency table for one element.
  let updateFreq (freq : Array Nat) (x : Int) : Array Nat :=
    let i := idxOf x
    if h : i < freq.size then
      let c := freq[i] -- safe under `h`
      freq.set! i (c + 1)
    else
      freq

  let initFreq : Array Nat := Array.mkArray R 0
  let freq : Array Nat := arr.foldl updateFreq initFreq

  -- `seen[c] = true` means some value has occurred exactly `c` times.
  let seenSize : Nat := arr.size + 1

  let rec checkCounts (i : Nat) (seen : Array Bool) : Bool :=
    if h : i < freq.size then
      let c : Nat := freq[i]
      if c = 0 then
        checkCounts (i + 1) seen
      else
        -- Use `get!`/`set!` to avoid proof obligations (counts are always ≤ arr.size).
        if seen.get! c then
          false
        else
          checkCounts (i + 1) (seen.set! c true)
    else
      true

  checkCounts 0 (Array.mkArray seenSize false)

end Impl

section TestCases

-- Test case 1: Example 1
-- arr = [1,2,2,1,1,3] has counts: 1↦3, 2↦2, 3↦1 (all distinct)
def test1_arr : Array Int := #[1, 2, 2, 1, 1, 3]

def test1_Expected : Bool := true

-- Test case 2: Example 2
-- arr = [1,2] has counts 1↦1, 2↦1 (not unique)
def test2_arr : Array Int := #[1, 2]

def test2_Expected : Bool := false

-- Test case 3: Example 3
-- arr = [-3,0,1,-3,1,1,1,-3,10,0] has counts -3↦3, 0↦2, 1↦4, 10↦1 (all distinct)
def test3_arr : Array Int := #[-3, 0, 1, -3, 1, 1, 1, -3, 10, 0]

def test3_Expected : Bool := true

-- Test case 4: Empty array (vacuously unique)
def test4_arr : Array Int := #[]

def test4_Expected : Bool := true

-- Test case 5: Singleton array (vacuously unique)
def test5_arr : Array Int := #[0]

def test5_Expected : Bool := true

-- Test case 6: All same value (only one distinct value, so unique)
def test6_arr : Array Int := #[7, 7, 7, 7]

def test6_Expected : Bool := true

-- Test case 7: Two distinct values with the same count
-- counts: 1↦2, 2↦2
def test7_arr : Array Int := #[1, 1, 2, 2]

def test7_Expected : Bool := false

-- Test case 8: Three values where two share the same count
-- counts: 1↦2, 2↦1, 3↦2
def test8_arr : Array Int := #[1, 3, 1, 2, 3]

def test8_Expected : Bool := false

-- Test case 9: Boundary values within allowed range
-- counts: -1000↦1, 1000↦2, 0↦3 (all distinct)
def test9_arr : Array Int := #[-1000, 1000, 1000, 0, 0, 0]

def test9_Expected : Bool := true

-- Recommend to validate: test1_arr, test3_arr, test9_arr
end TestCases

section Proof

noncomputable section AristotleLemmas

/-
The helper function checkCounts returns true if and only if the remaining non-zero elements in freq are not in seen, and are pairwise distinct.
-/
def checkCounts_invariant (freq : Array Nat) (i : Nat) (seen : Array Bool) : Prop :=
  (∀ j, i ≤ j → j < freq.size → freq.get! j ≠ 0 → seen.get! (freq.get! j) = false) ∧
  (∀ j k, i ≤ j → j < freq.size → i ≤ k → k < freq.size → j ≠ k → freq.get! j ≠ 0 → freq.get! k ≠ 0 → freq.get! j ≠ freq.get! k)

theorem checkCounts_correct (freq : Array Nat) (i : Nat) (seen : Array Bool)
    (h_bound : ∀ k, k < freq.size → freq.get! k < seen.size) :
  implementation.checkCounts freq i seen = true ↔ checkCounts_invariant freq i seen := by
  -- By induction on `freq.size - i`, we can show that `checkCounts` and `checkCounts_invariant` are equivalent.
  induction' h : freq.size - i with n ih generalizing i seen;
  · unfold checkCounts_invariant;
    unfold implementation.checkCounts;
    grind;
  · unfold checkCounts_invariant;
    by_cases hi : i < freq.size <;> simp_all +decide [ Nat.sub_succ ];
    unfold implementation.checkCounts;
    split_ifs ; simp_all +decide [ Nat.sub_succ ];
    split_ifs <;> simp_all +decide [ Nat.sub_succ, checkCounts_invariant ];
    · constructor <;> intro h <;> simp_all +decide [ Nat.succ_le_iff ];
      · refine' ⟨ fun j hj₁ hj₂ hj₃ => _, fun j k hj₁ hj₂ hj₃ hj₄ hj₅ hj₆ hj₇ => _ ⟩;
        · cases lt_or_eq_of_le hj₁ <;> simp_all +decide [ Array.get! ];
        · cases lt_or_eq_of_le hj₁ <;> cases lt_or_eq_of_le hj₃ <;> simp_all +decide [ Array.get! ];
      · exact ⟨ fun j hj₁ hj₂ hj₃ => h.1 j hj₁.le hj₂ hj₃, fun j k hj₁ hj₂ hj₃ hj₄ hj₅ hj₆ hj₇ => h.2 j k hj₁.le hj₂ hj₃.le hj₄ hj₅ hj₆ hj₇ ⟩;
    · constructor <;> intro h' <;> simp_all +decide [ Array.get! ];
      · constructor <;> intros j hj <;> simp_all +decide [ Nat.succ_le_iff ];
        · grind +ring;
        · intro hj₁ hj₂ hj₃ hj₄ hj₅ hj₆ hj₇ hj₈; cases lt_or_eq_of_le hj₁ <;> cases lt_or_eq_of_le hj₃ <;> simp_all +decide ;
          · exact h'.2.2 _ _ ‹_› ‹_› ‹_› ‹_› hj₅ ( by aesop ) ( by aesop ) hj₈;
          · grind;
          · grind +ring;
      · constructor;
        · intro j hj₁ hj₂ hj₃; specialize h' ; have := h'.1 j ( by linarith ) hj₂ hj₃; simp_all +decide [ Array.getElem_setIfInBounds ] ;
          exact h'.2 i j ( by linarith ) ( by linarith ) ( by linarith ) ( by linarith ) ( by linarith ) ( by tauto ) ( by tauto );
        · exact fun j k hj hj' hk hk' hjk hjk' hjk'' => h'.2 j k ( by linarith ) hj' ( by linarith ) hk' hjk hjk' hjk''

end AristotleLemmas

theorem correctness_goal_0_0 (arr : Array ℤ) (h_precond : precondition arr) : implementation.checkCounts
      (Array.foldl
        (fun freq x =>
          if h : (x + 1000).toNat < freq.size then freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
          else freq)
        (mkArray 2001 0) arr)
      0 (mkArray (arr.size + 1) false) =
    true ↔
  ∀ (i j : ℕ),
    i <
        (Array.foldl
            (fun freq x =>
              if h : (x + 1000).toNat < freq.size then freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
              else freq)
            (mkArray 2001 0) arr).size →
      j <
          (Array.foldl
              (fun freq x =>
                if h : (x + 1000).toNat < freq.size then
                  freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
                else freq)
              (mkArray 2001 0) arr).size →
        i ≠ j →
          (Array.foldl
                    (fun freq x =>
                      if h : (x + 1000).toNat < freq.size then
                        freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
                      else freq)
                    (mkArray 2001 0) arr).get!
                i ≠
              0 →
            (Array.foldl
                      (fun freq x =>
                        if h : (x + 1000).toNat < freq.size then
                          freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
                        else freq)
                      (mkArray 2001 0) arr).get!
                  j ≠
                0 →
              (Array.foldl
                      (fun freq x =>
                        if h : (x + 1000).toNat < freq.size then
                          freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
                        else freq)
                      (mkArray 2001 0) arr).get!
                  i ≠
                (Array.foldl
                      (fun freq x =>
                        if h : (x + 1000).toNat < freq.size then
                          freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
                        else freq)
                      (mkArray 2001 0) arr).get!
                  j := by
    rw [ checkCounts_correct ];
    · refine' ⟨ fun h i j hi hj hij hi0 hj0 => h.2 i j ( Nat.zero_le _ ) hi ( Nat.zero_le _ ) hj hij hi0 hj0, fun h => ⟨ fun j hj₁ hj₂ hj₃ => _, fun j k hj₁ hj₂ hj₃ hj₄ hj₅ hj₆ hj₇ => _ ⟩ ⟩;
      · rw [ Array.get! ];
        rw [ Array.getD ] ; norm_num;
        exact fun h => Array.getElem_replicate ..;
      · exact h j k hj₂ hj₄ hj₅ hj₆ hj₇;
    · intro k hk_lt_size
      have h_count_le_size : ∀ (arr : Array ℤ), ∀ (k : ℕ), k < 2001 → (Array.foldl (fun (freq : Array ℕ) (x : ℤ) => if h : (x + 1000).toNat < freq.size then freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1) else freq) (Array.mkArray 2001 0) arr).get! k ≤ arr.size := by
        intro arr k hk_lt_size
        induction' arr with arr ih generalizing k;
        induction' arr using List.reverseRecOn with arr ih generalizing k;
        · native_decide +revert;
        · simp +zetaDelta at *;
          split_ifs <;> simp_all +decide [ Array.get! ];
          · grind;
          · exact le_trans ( by solve_by_elim ) ( Nat.le_succ _ );
      refine' lt_of_le_of_lt ( h_count_le_size arr k _ ) _;
      · refine' lt_of_lt_of_le hk_lt_size _;
        induction' arr using Array.recOn with arr ih;
        induction' arr using List.reverseRecOn with arr ih;
        · native_decide +revert;
        · induction' ( arr ++ [ ih ] ) using List.reverseRecOn with arr ih <;> norm_num [ Array.mkArray ] at *;
          split_ifs <;> simp +decide [ *, Array.size_setIfInBounds ];
      · simp +arith +decide [ Array.mkArray ]

noncomputable section AristotleLemmas

/-
Helper definition for the frequency array computed in the implementation.
-/
def computedFreq (arr : Array Int) : Array Nat :=
  Array.foldl
    (fun freq x =>
      if h : (x + 1000).toNat < freq.size then freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
      else freq)
    (mkArray 2001 0) arr

/-
The size of the computed frequency array is always 2001.
-/
theorem computedFreq_size (arr : Array Int) : (computedFreq arr).size = 2001 := by
  -- The size of the frequency array is determined by the initial array, which has 2001 elements.
  have h_size : ∀ (arr : Array Int), (Array.foldl (fun (freq : Array ℕ) (x : Int) => if h : (x + 1000).toNat < freq.size then freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1) else freq) (mkArray 2001 0) arr).size = 2001 := by
    intro arr
    induction' arr using Array.recOn with arr ih;
    induction' arr using List.reverseRecOn with arr ih;
    · native_decide +revert;
    · grind +ring;
  exact h_size arr

/-
Helper definition for the update function used in the fold.
-/
def updateFreqHelper (freq : Array Nat) (x : Int) : Array Nat :=
  if h : (x + 1000).toNat < freq.size then freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
  else freq

/-
computedFreq is equal to folding updateFreqHelper over the array.
-/
theorem computedFreq_eq_fold_updateFreqHelper (arr : Array Int) :
  computedFreq arr = arr.foldl updateFreqHelper (mkArray 2001 0) := by
  unfold computedFreq updateFreqHelper
  rfl

/-
Invariant: The frequency array correctly counts the occurrences of elements processed so far. Specifically, for each index k < 2001, the value at freq[k] equals the number of elements y in the processed list such that (y + 1000).toNat = k.
-/
def FreqCorrect (freq : Array Nat) (processed : List Int) : Prop :=
  freq.size = 2001 ∧
  ∀ k : Nat, k < 2001 → freq.get! k = processed.countP (fun y => (y + 1000).toNat = k)

/-
Base case: The initial frequency array (all zeros) is correct for the empty list of processed elements.
-/
theorem FreqCorrect_nil : FreqCorrect (mkArray 2001 0) [] := by
  constructor;
  · native_decide +revert;
  · native_decide +revert

/-
Inductive step: If the frequency array is correct for `processed`, and we add `x` (which is in range), the updated frequency array is correct for `processed ++ [x]`.
-/
theorem FreqCorrect_step (freq : Array Nat) (processed : List Int) (x : Int)
    (h_correct : FreqCorrect freq processed) (hx : -1000 ≤ x ∧ x ≤ 1000) :
    FreqCorrect (updateFreqHelper freq x) (processed ++ [x]) := by
      unfold updateFreqHelper;
      split_ifs <;> simp_all +decide [ FreqCorrect ];
      · intro k hk; split_ifs <;> simp_all +decide [ Array.get! ] ;
        · grind;
        · grind;
      · omega

/-
Lemma: The frequency array resulting from folding over a list `l` satisfies `FreqCorrect` with respect to `l`, provided all elements in `l` are in range.
-/
theorem FreqCorrect_foldl (l : List Int) (hl : ∀ x ∈ l, -1000 ≤ x ∧ x ≤ 1000) :
    FreqCorrect (l.foldl updateFreqHelper (mkArray 2001 0)) l := by
      induction' l using List.reverseRecOn with l ih;
      · exact FreqCorrect_nil;
      · simp +zetaDelta at *;
        exact FreqCorrect_step _ _ _ ( by apply_assumption; aesop ) ( hl _ ( Or.inr rfl ) )

/-
Lemma: For integers x and y in the valid range (>= -1000), (x + 1000).toNat = (y + 1000).toNat iff x = y.
-/
theorem range_toNat_inj {x y : Int} (hx : -1000 ≤ x) (hy : -1000 ≤ y) :
  (x + 1000).toNat = (y + 1000).toNat ↔ x = y := by
    grind +ring

/-
Lemma: The computed frequency array correctly stores the counts of elements in the input array, assuming the input elements are within the problem range.
-/
theorem computedFreq_eq_count (arr : Array Int) (h_range : ∀ y ∈ arr, -1000 ≤ y ∧ y ≤ 1000) (x : Int) (hx : -1000 ≤ x ∧ x ≤ 1000) :
    (computedFreq arr).get! (x + 1000).toNat = arr.count x := by
      convert FreqCorrect_foldl ( arr.toList ) ( by aesop ) |> And.right |> fun h => h _ _ using 1;
      convert rfl;
      · unfold computedFreq; aesop;
      · rw [ List.countP_eq_length_filter ];
        rw [ List.filter_congr ];
        rotate_right;
        use fun y => y = x;
        · grind;
        · grind;
      · linarith [ Int.toNat_of_nonneg ( by linarith : 0 ≤ x + 1000 ) ]

/-
Auxiliary definition of checkCounts to facilitate reasoning.
-/
def checkCounts_aux (freq : Array Nat) (seen : Array Bool) (i : Nat) : Bool :=
  if h : i < freq.size then
    let c := freq[i]
    if c = 0 then
      checkCounts_aux freq seen (i + 1)
    else
      if c < seen.size then
        if seen[c]! then
          false
        else
          checkCounts_aux freq (seen.set! c true) (i + 1)
      else
        checkCounts_aux freq seen (i + 1)
  else
    true
termination_by freq.size - i
decreasing_by all_goals (simp_wf; omega)

/-
Predicate stating that counts in `freq` starting from index `i` are unique and not in `seen`.
-/
def UniqueCountsFrom (freq : Array Nat) (seen : Array Bool) (i : Nat) : Prop :=
  (∀ j, i ≤ j → j < freq.size → freq[j]! ≠ 0 → seen.get! (freq[j]!) = false) ∧
  (∀ j k, i ≤ j → j < freq.size → i ≤ k → k < freq.size → j ≠ k → freq[j]! ≠ 0 → freq[k]! ≠ 0 → freq[j]! ≠ freq[k]!)

/-
Model of the checkCounts function.
-/
def checkCounts_spec (freq : Array Nat) (seen : Array Bool) (i : Nat) : Bool :=
  if h : i < freq.size then
    let c := freq[i]
    if c = 0 then
      checkCounts_spec freq seen (i + 1)
    else
      if c < seen.size then
        if seen[c]! then
          false
        else
          checkCounts_spec freq (seen.set! c true) (i + 1)
      else
        checkCounts_spec freq seen (i + 1)
  else
    true
termination_by freq.size - i
decreasing_by all_goals (simp_wf; omega)

/-
Theorem: checkCounts_spec returns true if and only if the counts starting from index i are unique and have not been seen before.
-/
theorem checkCounts_spec_iff (freq : Array Nat) (seen : Array Bool) (i : Nat)
  (h_bound : ∀ k, k < freq.size → freq[k]! < seen.size) :
  checkCounts_spec freq seen i = true ↔ UniqueCountsFrom freq seen i := by
  -- We'll use induction on the size of the frequency array to prove the equivalence.
  induction' h_ind : freq.size - i with n ih generalizing i seen;
  · unfold checkCounts_spec UniqueCountsFrom;
    grind;
  · unfold checkCounts_spec UniqueCountsFrom;
    split_ifs <;> simp_all +decide [ Nat.sub_succ ];
    split_ifs <;> simp_all +decide [ UniqueCountsFrom ];
    · constructor <;> intro h <;> constructor <;> intros j hj₁ hj₂;
      · cases hj₁.eq_or_lt <;> [ aesop; exact h.1 _ ( by linarith ) _ ‹_› ];
        exact h.1 j ( by linarith ) ( by linarith );
      · intro hj₃ hj₄ hj₅ hj₆ hj₇ hj₈ hj₉; cases lt_or_eq_of_le hj₂ <;> cases lt_or_eq_of_le hj₄ <;> simp_all +decide ;
        exact h.2 j hj₁ ( by linarith ) ( by linarith ) ( by linarith ) ( by linarith ) ( by tauto ) ( by aesop ) ( by aesop ) ( by aesop );
      · exact h.1 j ( by linarith ) hj₂;
      · exact fun _ _ _ _ _ _ => h.2 _ _ ( by linarith ) ( by linarith ) ( by linarith ) ( by linarith ) ( by tauto ) ( by tauto ) ( by tauto );
    · constructor <;> intro h;
      · constructor;
        · intro j hj₁ hj₂ hj₃; cases lt_or_eq_of_le hj₁ <;> simp_all +decide [ Array.get! ] ;
          grind;
        · intro j k hj a hk a_2 hjk hjk' hk';
          by_cases hj' : j = i <;> by_cases hk' : k = i <;> simp_all +decide [ Array.get! ];
          · grind;
          · grind +ring;
          · exact h.2.2 j k ( lt_of_le_of_ne hj ( Ne.symm hj' ) ) a ( lt_of_le_of_ne hk ( Ne.symm hk' ) ) a_2 hjk hjk' ‹_›;
      · simp_all +decide [ Array.get! ];
        constructor;
        · intro j hj₁ hj₂ hj₃; specialize h; have := h.1 j ( by linarith ) hj₂ hj₃; simp_all +decide [ Array.getElem_setIfInBounds ] ;
          exact h.2 i j ( by linarith ) ( by linarith ) ( by linarith ) ( by linarith ) ( by linarith ) ( by tauto ) ( by tauto );
        · exact fun j k hj hj' hk hk' hjk hjk' hjk'' => h.2 j k ( by linarith ) hj' ( by linarith ) hk' hjk hjk' hjk''

/-
Inspect the definition of implementation.checkCounts to understand its arguments and structure.
-/
#print implementation.checkCounts

/-
Inspect the underlying unary function for checkCounts.
-/
#print implementation.checkCounts._unary

/-
Lemma: implementation.checkCounts satisfies the expected recurrence relation.
-/
theorem implementation_checkCounts_eq_recurrence (freq : Array Nat) (seen : Array Bool) (i : Nat) :
  implementation.checkCounts freq i seen =
    if h : i < freq.size then
      let c := freq[i]
      if c = 0 then
        implementation.checkCounts freq (i + 1) seen
      else
        if c < seen.size then
          if seen[c]! then
            false
          else
            implementation.checkCounts freq (i + 1) (seen.set! c true)
        else
          implementation.checkCounts freq (i + 1) seen
    else
      true := by
        rw [implementation.checkCounts];
        split_ifs <;> simp_all +decide [ Array.get! ];
        grind

/-
Lemma: implementation.checkCounts satisfies the expected recurrence relation.
-/
theorem implementation_checkCounts_eq_recurrence_v2 (freq : Array Nat) (seen : Array Bool) (i : Nat) :
  implementation.checkCounts freq i seen =
    if h : i < freq.size then
      let c := freq[i]
      if c = 0 then
        implementation.checkCounts freq (i + 1) seen
      else
        if c < seen.size then
          if seen[c]! then
            false
          else
            implementation.checkCounts freq (i + 1) (seen.set! c true)
        else
          implementation.checkCounts freq (i + 1) seen
    else
      true := by
        exact?

/-
Lemma: implementation.checkCounts is equivalent to checkCounts_spec.
-/
theorem implementation_checkCounts_eq_spec (freq : Array Nat) (seen : Array Bool) (i : Nat) :
  implementation.checkCounts freq i seen = checkCounts_spec freq seen i := by
    induction' n : freq.size - i using Nat.strong_induction_on with n ih generalizing freq seen i;
    rw [ implementation_checkCounts_eq_recurrence, checkCounts_spec ];
    grind

/-
Lemma: implementation.checkCounts satisfies the recurrence relation (matching implementation structure).
-/
theorem implementation_checkCounts_eq_recurrence_correct (freq : Array Nat) (seen : Array Bool) (i : Nat) :
  implementation.checkCounts freq i seen =
    if h : i < freq.size then
      let c := freq[i]
      if c = 0 then
        implementation.checkCounts freq (i + 1) seen
      else
        if seen.get! c then
          false
        else
          implementation.checkCounts freq (i + 1) (seen.set! c true)
    else
      true := by
        exact?

/-
Lemma: All elements in the computed frequency array are bounded by `arr.size`.
-/
theorem computedFreq_bound (arr : Array Int) (h_precond : precondition arr) :
  ∀ k, k < (computedFreq arr).size → (computedFreq arr)[k]! < arr.size + 1 := by
    -- By definition of `computedFreq`, at each step the count is incremented by 1 and the initial value is 0.
    have h_count_bounds : ∀ (processed : List Int), (∀ y ∈ processed, -1000 ≤ y ∧ y ≤ 1000) → ∀ k < 2001, (processed.foldl updateFreqHelper (mkArray 2001 0)).get! k ≤ processed.length := by
      intros processed h_processed k hk
      have h_count_le : (processed.foldl updateFreqHelper (mkArray 2001 0)).get! k = processed.countP (fun y => (y + 1000).toNat = k) := by
        convert FreqCorrect_foldl processed h_processed |>.2 k hk using 1;
      grind;
    intros k hk
    have h_count : (computedFreq arr).get! k ≤ arr.size := by
      convert h_count_bounds arr.toList ( fun y hy => by
        obtain ⟨ i, hi ⟩ := List.mem_iff_get.mp hy; specialize h_precond i; aesop; ) k ( by
        exact hk.trans_le ( by rw [ computedFreq_size ] ) ) using 1;
      unfold computedFreq; aesop;
    convert Nat.lt_succ_of_le h_count using 1

/-
Lemma: If `seen` is effectively empty (all false), then `UniqueCountsFrom` reduces to checking uniqueness of non-zero counts.
-/
theorem UniqueCountsFrom_empty_seen (freq : Array Nat) (seen : Array Bool)
  (h_seen : ∀ k, seen.get! k = false) :
  UniqueCountsFrom freq seen 0 ↔
  ∀ j k, j < freq.size → k < freq.size → j ≠ k → freq[j]! ≠ 0 → freq[k]! ≠ 0 → freq[j]! ≠ freq[k]! := by
    unfold UniqueCountsFrom; aesop;

/-
Lemma: `UniqueCountsFrom` on the computed frequency array is equivalent to `countsAreUnique` on the original array.
-/
theorem final_equivalence (arr : Array Int) (h_precond : precondition arr) :
  UniqueCountsFrom (computedFreq arr) (mkArray (arr.size + 1) false) 0 ↔ countsAreUnique arr := by
    constructor <;> intro h <;> unfold countsAreUnique at *;
    · intro x y hxy hx hy; have := h.2; simp_all +decide [ UniqueCountsFrom ] ;
      -- By definition of `computedFreq`, we know that `(computedFreq arr)[(x + 1000).toNat]! = arr.count x` and `(computedFreq arr)[(y + 1000).toNat]! = arr.count y`.
      have h_counts : (computedFreq arr).get! (x + 1000).toNat = arr.count x ∧ (computedFreq arr).get! (y + 1000).toNat = arr.count y := by
        apply And.intro;
        · apply computedFreq_eq_count;
          · intro y hy; exact (by
            obtain ⟨ i, hi ⟩ := Array.getElem_of_mem hy; specialize h_precond i; aesop;);
          · obtain ⟨ i, hi ⟩ := Array.mem_iff_getElem.mp hx; specialize h_precond i; aesop;
        · apply computedFreq_eq_count;
          · intro y hy; obtain ⟨ i, hi ⟩ := Array.getElem_of_mem hy; specialize h_precond i; aesop;
          · obtain ⟨ i, hi ⟩ := Array.mem_iff_getElem.mp hy; specialize h_precond i; aesop;
      have h_neq : (x + 1000).toNat ≠ (y + 1000).toNat := by
        obtain ⟨ i, hi ⟩ := Array.mem_iff_getElem.mp hx; obtain ⟨ j, hj ⟩ := Array.mem_iff_getElem.mp hy; have := h_precond i; have := h_precond j; simp_all +decide [ inProblemRange ] ;
        grind +ring;
      have h_neq : (x + 1000).toNat < (computedFreq arr).size ∧ (y + 1000).toNat < (computedFreq arr).size := by
        have h_neq : ∀ z ∈ arr, (z + 1000).toNat < (computedFreq arr).size := by
          intros z hz
          have hz_range : -1000 ≤ z ∧ z ≤ 1000 := by
            have := h_precond ( Array.idxOf z arr ) ( by
              exact? )
            generalize_proofs at *;
            cases arr ; aesop
          have hz_toNat : (z + 1000).toNat < 2001 := by
            grind
          have hz_size : (computedFreq arr).size = 2001 := by
            exact?
          exact hz_size.symm ▸ hz_toNat;
        exact ⟨ h_neq x hx, h_neq y hy ⟩;
      simp_all +decide [ Array.get! ];
      exact h.2 _ _ h_neq.1 h_neq.2 ‹_› ( by linarith [ show 0 < Array.count x arr from by exact? ] ) ( by linarith [ show 0 < Array.count y arr from by exact? ] ) |> fun h => by aesop;
    · constructor;
      · intro j hj₁ hj₂ hj₃; rw [ Array.mkArray ] ; simp +decide [ hj₃ ] ;
        simp +decide [ Array.get! ];
        rw [ Array.getElem?_replicate ] ; aesop;
      · -- By definition of `computedFreq`, we know that `(computedFreq arr)[j]!` is the count of elements in `arr` that are equal to `j - 1000`.
        have h_count : ∀ j, j < (computedFreq arr).size → (computedFreq arr)[j]! = arr.count (j - 1000 : ℤ) := by
          intros j hj
          have h_count : (computedFreq arr)[j]! = arr.count (j - 1000 : ℤ) := by
            have h_range : -1000 ≤ (j - 1000 : ℤ) ∧ (j - 1000 : ℤ) ≤ 1000 := by
              constructor <;> linarith [ show ( computedFreq arr ).size = 2001 from computedFreq_size arr ]
            convert computedFreq_eq_count arr ( fun x hx => ?_ ) ( j - 1000 ) ⟨ by linarith, by linarith ⟩ using 1;
            · norm_num [ Int.toNat_sub_of_le ];
              exact?;
            · obtain ⟨ i, hi ⟩ := Array.getElem_of_mem hx; specialize h_precond i; aesop;
          exact h_count;
        simp_all +decide [ Array.count ]

end AristotleLemmas

theorem correctness_goal_0_1 (arr : Array ℤ) (h_precond : precondition arr) (h_checkCounts_spec : implementation.checkCounts
      (Array.foldl
        (fun freq x =>
          if h : (x + 1000).toNat < freq.size then freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
          else freq)
        (mkArray 2001 0) arr)
      0 (mkArray (arr.size + 1) false) =
    true ↔
  ∀ (i j : ℕ),
    i <
        (Array.foldl
            (fun freq x =>
              if h : (x + 1000).toNat < freq.size then freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
              else freq)
            (mkArray 2001 0) arr).size →
      j <
          (Array.foldl
              (fun freq x =>
                if h : (x + 1000).toNat < freq.size then
                  freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
                else freq)
              (mkArray 2001 0) arr).size →
        i ≠ j →
          (Array.foldl
                    (fun freq x =>
                      if h : (x + 1000).toNat < freq.size then
                        freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
                      else freq)
                    (mkArray 2001 0) arr).get!
                i ≠
              0 →
            (Array.foldl
                      (fun freq x =>
                        if h : (x + 1000).toNat < freq.size then
                          freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
                        else freq)
                      (mkArray 2001 0) arr).get!
                  j ≠
                0 →
              (Array.foldl
                      (fun freq x =>
                        if h : (x + 1000).toNat < freq.size then
                          freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
                        else freq)
                      (mkArray 2001 0) arr).get!
                  i ≠
                (Array.foldl
                      (fun freq x =>
                        if h : (x + 1000).toNat < freq.size then
                          freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
                        else freq)
                      (mkArray 2001 0) arr).get!
                  j) : (∀ (i j : ℕ),
    i <
        (Array.foldl
            (fun freq x =>
              if h : (x + 1000).toNat < freq.size then freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
              else freq)
            (mkArray 2001 0) arr).size →
      j <
          (Array.foldl
              (fun freq x =>
                if h : (x + 1000).toNat < freq.size then
                  freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
                else freq)
              (mkArray 2001 0) arr).size →
        i ≠ j →
          (Array.foldl
                    (fun freq x =>
                      if h : (x + 1000).toNat < freq.size then
                        freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
                      else freq)
                    (mkArray 2001 0) arr).get!
                i ≠
              0 →
            (Array.foldl
                      (fun freq x =>
                        if h : (x + 1000).toNat < freq.size then
                          freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
                        else freq)
                      (mkArray 2001 0) arr).get!
                  j ≠
                0 →
              (Array.foldl
                      (fun freq x =>
                        if h : (x + 1000).toNat < freq.size then
                          freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
                        else freq)
                      (mkArray 2001 0) arr).get!
                  i ≠
                (Array.foldl
                      (fun freq x =>
                        if h : (x + 1000).toNat < freq.size then
                          freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
                        else freq)
                      (mkArray 2001 0) arr).get!
                  j) ↔
  countsAreUnique arr := by
    have h_unique_counts : UniqueCountsFrom (computedFreq arr) (mkArray (arr.size + 1) false) 0 ↔ countsAreUnique arr := by
      exact?;
    rw [ ← h_unique_counts, UniqueCountsFrom_empty_seen ];
    · congr! 3;
    · intro k; by_cases hk : k < arr.size + 1 <;> simp +decide [ hk, Array.mkArray ] ;
      · simp +decide [ hk, Array.get! ];
      · simp +decide [ hk, Array.get! ]

end Proof