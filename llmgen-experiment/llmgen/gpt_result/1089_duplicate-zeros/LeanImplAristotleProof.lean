/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 87a071f5-3dca-4abf-ba01-d2da9a56a2c8

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem correctness_goal_1_1 (arr : Array ℤ) (h_precond : precondition arr) (j : ℕ) (hj : j < arr.size) (i : ℕ) (hi : i < arr.size ∧ producedLen arr i ≤ j ∧ j < producedLen arr (i + 1)) (hui : ∀ (y : ℕ), y < arr.size ∧ producedLen arr y ≤ j ∧ j < producedLen arr (y + 1) → y = i) : (implementation arr)[j]! = if arr[i]! = 0 then 0 else arr[i]!

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
    1089. Duplicate Zeros: duplicate each occurrence of 0 in a fixed-length integer array, shifting right and truncating.
    Natural language breakdown:
    1. Input is an array of integers with a fixed length n.
    2. We define a conceptual output stream obtained by scanning the input left-to-right.
    3. Each nonzero input element contributes exactly one output element equal to itself.
    4. Each zero input element contributes exactly two consecutive output elements, both equal to 0.
    5. The actual returned array is the first n elements of this conceptual output stream (truncate to length n).
    6. Because the original problem updates in-place and returns nothing, we model the modified array as a returned array.
    7. Therefore the result must have the same size as the input.
    8. Every output index j (0 ≤ j < n) is produced by a unique input index i, determined by how many output elements are produced by prefixes of the input.
    Your algorithm should run in **O(n)** time and **O(1)** extra space.
-/

-- Helper: producedLen arr k = number of conceptual output elements produced by the first k input elements.
-- Each nonzero produces 1; each zero produces 2.
-- We use foldl over a prefix (arr.take k) to avoid recursion.
-- Note: we use Int = 0 propositionally; this is fine (not Float).
def producedLen (arr : Array Int) (k : Nat) : Nat :=
  (arr.take k).foldl (fun (acc : Nat) (x : Int) => if x = 0 then acc + 2 else acc + 1) 0

-- Precondition: none.
def precondition (arr : Array Int) : Prop :=
  True

-- Postcondition: result is the length-preserving truncation of duplicating zeros.
-- We characterize the mapping index-wise using the prefix produced lengths.
-- For each output index j, there is a unique input index i < n such that
-- producedLen arr i ≤ j < producedLen arr (i+1). The output value equals arr[i], but if arr[i]=0 then it is 0.
def postcondition (arr : Array Int) (result : Array Int) : Prop :=
  result.size = arr.size ∧
  (∀ (j : Nat), j < arr.size →
    ∃! (i : Nat),
      i < arr.size ∧
      producedLen arr i ≤ j ∧
      j < producedLen arr (i + 1) ∧
      result[j]! = (if arr[i]! = 0 then (0 : Int) else arr[i]!))

end Specs

section Impl

def implementation (arr : Array Int) : Array Int :=
  let n := arr.size
  -- count zeros once (O(n))
  let zeros :=
    arr.foldl (fun acc x => if x = (0 : Int) then acc + 1 else acc) 0
  -- Walk from right to left, writing into `res` (initially `arr`).
  -- `j` is the conceptual index in the duplicated stream.
  let rec go (i : Nat) (j : Nat) (res : Array Int) : Array Int :=
    match i with
    | 0 =>
        res
    | i' + 1 =>
        let x := arr[i']!
        -- write x at (j-1) if it falls within bounds
        let res1 :=
          match j with
          | 0 => res
          | j1 + 1 =>
              if j1 < n then
                res.set! j1 x
              else
                res
        if x = (0 : Int) then
          -- write the duplicated zero at (j-2) if within bounds
          let res2 :=
            match j with
            | 0 => res1
            | 1 => res1
            | (j2 + 2) =>
                if j2 < n then
                  res1.set! j2 (0 : Int)
                else
                  res1
          go i' (j - 2) res2
        else
          go i' (j - 1) res1
  go n (n + zeros) arr

end Impl

section TestCases

-- Test case 1: Example 1
-- Input: [1,0,2,3,0,4,5,0]
-- Output: [1,0,0,2,3,0,0,4]
def test1_arr : Array Int := #[1, 0, 2, 3, 0, 4, 5, 0]

def test1_Expected : Array Int := #[1, 0, 0, 2, 3, 0, 0, 4]

-- Test case 2: Example 2 (no zeros)
def test2_arr : Array Int := #[1, 2, 3]

def test2_Expected : Array Int := #[1, 2, 3]

-- Test case 3: empty array
def test3_arr : Array Int := #[]

def test3_Expected : Array Int := #[]

-- Test case 4: single element zero
def test4_arr : Array Int := #[0]

def test4_Expected : Array Int := #[0]

-- Test case 5: single element nonzero
def test5_arr : Array Int := #[7]

def test5_Expected : Array Int := #[7]

-- Test case 6: all zeros (truncation preserves all zeros)
def test6_arr : Array Int := #[0, 0, 0]

def test6_Expected : Array Int := #[0, 0, 0]

-- Test case 7: zeros causing truncation of later elements
-- [1,0,0,2] -> conceptual: 1,0,0,0,0,2 -> take 4 => [1,0,0,0]
def test7_arr : Array Int := #[1, 0, 0, 2]

def test7_Expected : Array Int := #[1, 0, 0, 0]

-- Test case 8: negative values with zeros
-- [0,-1,0,2] -> conceptual: 0,0,-1,0,0,2 -> take 4 => [0,0,-1,0]
def test8_arr : Array Int := #[0, -1, 0, 2]

def test8_Expected : Array Int := #[0, 0, -1, 0]

-- Test case 9: trailing zero does not create a visible extra element after truncation
-- [1,2,0] -> conceptual: 1,2,0,0 -> take 3 => [1,2,0]
def test9_arr : Array Int := #[1, 2, 0]

def test9_Expected : Array Int := #[1, 2, 0]

-- Recommend to validate: boundary sizes (0/1), multiple zeros, truncation at end
end TestCases

section Proof

noncomputable section AristotleLemmas

/-
`go_model` is a standalone version of the inner loop of the implementation, parameterized by the array `arr`, the limit `limit` (usually `arr.size`), the current input index `i`, the current output index `j`, and the accumulator array `res`.
-/
def go_model (arr : Array Int) (limit : Nat) (i : Nat) (j : Nat) (res : Array Int) : Array Int :=
  match i with
  | 0 => res
  | i' + 1 =>
      let x := arr[i']!
      let res1 :=
        match j with
        | 0 => res
        | j1 + 1 =>
            if j1 < limit then res.set! j1 x else res
      if x = 0 then
        let res2 :=
          match j with
          | 0 => res1
          | 1 => res1
          | j2 + 2 =>
              if j2 < limit then res1.set! j2 0 else res1
        go_model arr limit i' (j - 2) res2
      else
        go_model arr limit i' (j - 1) res1

/-
The produced length for an empty prefix is 0.
-/
lemma producedLen_zero (arr : Array Int) : producedLen arr 0 = 0 := by
  -- By definition of `producedLen`, `producedLen arr 0` is the sum of the lengths of the individual outputs for the empty prefix.
  simp [producedLen]

/-
The produced length of the first `i+1` elements is the produced length of the first `i` elements plus the contribution of the `i`-th element (which is 2 if it's zero, and 1 otherwise).
-/
lemma producedLen_succ (arr : Array Int) (i : Nat) (h : i < arr.size) :
  producedLen arr (i + 1) = producedLen arr i + if arr[i]! = 0 then 2 else 1 := by
    unfold producedLen;
    rw [ show arr.take ( i + 1 ) = arr.take i ++ #[arr[i]!] from ?_, Array.foldl_append ] <;> aesop

/-
`producedLen` is a monotonic function of the index.
-/
lemma producedLen_mono (arr : Array Int) (i k : Nat) (h : i ≤ k) : producedLen arr i ≤ producedLen arr k := by
  induction' h with k hk ih;
  · rfl;
  · by_cases hk' : k < arr.size <;> simp_all +decide [ producedLen_succ ];
    · exact le_add_right ih;
    · -- Since `arr.size ≤ k`, we have `arr.take (k + 1) = arr.take k`.
      have h_take : arr.take (k + 1) = arr.take k := by
        grind +ring;
      unfold producedLen at *; aesop;

/-
`producedLen` is strictly monotonic for indices within the array bounds.
-/
lemma producedLen_strict_mono (arr : Array Int) (i k : Nat) (h_ik : i < k) (h_k : k ≤ arr.size) : producedLen arr i < producedLen arr k := by
  -- We proceed by induction on $k$.
  induction' h_ik with k ih;
  · rw [ producedLen_succ ] <;> aesop;
  · exact lt_of_lt_of_le ( by solve_by_elim [ Nat.le_of_succ_le ] ) ( by rw [ producedLen_succ _ _ ( by linarith ) ] ; split_ifs <;> simp_all +decide )

/-
`go_model` preserves the values of the array at indices greater than or equal to the current output pointer `j`.
-/
lemma go_model_preserves (arr : Array Int) (limit : Nat) (i : Nat) (j : Nat) (res : Array Int) (k : Nat) (hk : k ≥ j) :
  (go_model arr limit i j res)[k]! = res[k]! := by
    induction' i with i ih generalizing j res k;
    · rfl;
    · rcases j with ( _ | j ) <;> simp_all +decide [ go_model ];
      rcases j with ( _ | j ) <;> simp_all +decide [ Nat.succ_eq_add_one ];
      · grind;
      · grind

/-
`go_model` preserves the size of the accumulator array.
-/
lemma go_model_size (arr : Array Int) (limit : Nat) (i : Nat) (j : Nat) (res : Array Int) :
  (go_model arr limit i j res).size = res.size := by
    have h_ind : ∀ (i j : ℕ) (res : Array ℤ), (go_model arr limit i j res).size = res.size := by
      intro i j res; induction' i with i ih generalizing j res <;> simp +decide [ *, go_model ] ;
      rcases j with ( _ | _ | j ) <;> simp_all +decide [ Array.size_setIfInBounds ] ;
      · grind;
      · grind;
    exact h_ind i j res

/-
`go_model` correctly populates the array for indices less than the produced length, provided `i` is within bounds and `res` has the correct size.
-/
theorem go_model_correct_lt (arr : Array Int) (limit : Nat) (i : Nat) (hi : i ≤ arr.size) (res : Array Int) (h_res_size : res.size = limit) :
  let j := producedLen arr i
  let final := go_model arr limit i j res
  ∀ k < limit, k < j →
    ∃ i_k < i, producedLen arr i_k ≤ k ∧ k < producedLen arr (i_k+1) ∧
      final[k]! = (if arr[i_k]! = 0 then 0 else arr[i_k]!) := by
        -- We proceed by induction on `i`.
        induction' i with i ih generalizing res;
        · unfold producedLen; aesop;
        · -- Let's unfold the definition of `go_model` for the case `i + 1`.
          have h_go_model_succ : go_model arr limit (i + 1) (producedLen arr (i + 1)) res =
            let x := arr[i]!
            let j := producedLen arr (i + 1)
            let j_prev := producedLen arr i
            let res1 :=
              match j with
              | 0 => res
              | j' + 1 =>
                  if j' < limit then res.set! j' x else res
            if x = 0 then
              let res2 :=
                match j with
                | 0 => res1
                | 1 => res1
                | j'' + 2 =>
                    if j'' < limit then res1.set! j'' 0 else res1
              go_model arr limit i (j - 2) res2
            else
              go_model arr limit i (j - 1) res1 := by
                exact?;
          -- Let's consider the two cases: when `x` is zero and when `x` is not zero.
          by_cases hx : arr[i]! = 0;
          · -- By definition of `producedLen`, we know that `producedLen arr (i + 1) = producedLen arr i + 2`.
            have h_producedLen_succ : producedLen arr (i + 1) = producedLen arr i + 2 := by
              rw [ producedLen_succ ] <;> aesop;
            simp_all +decide [ Nat.add_comm, Nat.add_left_comm, Nat.add_assoc ];
            intro k hk₁ hk₂; rcases lt_or_ge k ( producedLen arr i ) with hk₃ | hk₃ <;> simp_all +decide [ Nat.lt_succ_iff ] ;
            · specialize ih ( Nat.le_of_succ_le hi ) ( if producedLen arr i < limit then ( if producedLen arr i + 1 < limit then res.setIfInBounds ( producedLen arr i + 1 ) 0 else res ).setIfInBounds ( producedLen arr i ) 0 else if producedLen arr i + 1 < limit then res.setIfInBounds ( producedLen arr i + 1 ) 0 else res ) ( by
                grind ) k hk₁ hk₃
              generalize_proofs at *;
              exact ⟨ ih.choose, Nat.le_of_lt ih.choose_spec.1, ih.choose_spec.2.1, ih.choose_spec.2.2.1, ih.choose_spec.2.2.2 ⟩;
            · rcases hk₂ with ( _ | hk₂ ) <;> simp_all +decide [ Nat.lt_succ_iff ];
              · use i; simp_all +decide [ Nat.lt_succ_iff ] ;
                convert go_model_preserves _ _ _ _ _ _ _ using 1 ; aesop;
                linarith;
              · use i; simp_all +decide [ Nat.le_antisymm hk₂ hk₃ ] ;
                rw [ go_model_preserves ] ; aesop;
                norm_num +zetaDelta at *;
          · -- Since `arr[i]!` is not zero, we have `producedLen arr (i + 1) = producedLen arr i + 1`.
            have h_producedLen_succ : producedLen arr (i + 1) = producedLen arr i + 1 := by
              rw [ producedLen_succ ] <;> aesop;
            simp_all +decide [ Nat.lt_succ_iff ];
            intro k hk₁ hk₂;
            by_cases hk₃ : k < producedLen arr i;
            · obtain ⟨ i_k, hi_k₁, hi_k₂, hi_k₃, hi_k₄ ⟩ := ih ( Nat.le_of_succ_le hi ) ( if producedLen arr i < limit then res.setIfInBounds ( producedLen arr i ) arr[i]! else res ) ( by
                split_ifs <;> simp_all +decide [ Array.size_setIfInBounds ] ) k hk₁ hk₃;
              exact ⟨ i_k, le_of_lt hi_k₁, hi_k₂, hi_k₃, hi_k₄ ⟩;
            · use i;
              split_ifs <;> simp_all +decide [ Nat.lt_succ_iff ];
              · convert go_model_preserves arr limit i ( producedLen arr i ) ( res.setIfInBounds ( producedLen arr i ) arr[i]! ) ( producedLen arr i ) _ using 1;
                · rw [ le_antisymm hk₂ hk₃ ];
                · rw [ Array.setIfInBounds ] ; aesop;
                · grind;
              · linarith

/-
`go_model` correctly populates the array: elements before `j` are determined by the input prefix, and elements after `j` are preserved.
-/
theorem go_model_correct (arr : Array Int) (limit : Nat) (i : Nat) (hi : i ≤ arr.size) (res : Array Int) (h_res_size : res.size = limit) :
  let j := producedLen arr i
  let final := go_model arr limit i j res
  ∀ k < limit,
    (k < j → ∃ i_k < i, producedLen arr i_k ≤ k ∧ k < producedLen arr (i_k+1) ∧ final[k]! = (if arr[i_k]! = 0 then 0 else arr[i_k]!)) ∧
    (k ≥ j → final[k]! = res[k]!) := by
      intros j final k hk
      constructor;
      · apply go_model_correct_lt arr limit i hi res h_res_size k hk;
      · exact?

/-
The produced length of the entire array is equal to the array size plus the number of zeros.
-/
lemma producedLen_eq_size_plus_zeros (arr : Array Int) :
  producedLen arr arr.size = arr.size + arr.foldl (fun acc x => if x = 0 then acc + 1 else acc) 0 := by
    -- We can prove this by induction on the array using the definition of ` producedLen`.
    have h_ind : ∀ (xs : List ℤ), (List.foldl (fun (acc : ℕ) (x : ℤ) => if x = 0 then acc + 2 else acc + 1) 0 xs) = xs.length + (List.foldl (fun (acc : ℕ) (x : ℤ) => if x = 0 then acc + 1 else acc) 0 xs) := by
      intro xs;
      induction' xs using List.reverseRecOn with xs ih;
      · exact?;
      · grind +ring;
    convert h_ind arr.toList using 1;
    · unfold producedLen;
      simp +zetaDelta at *;
    · aesop

/-
The `implementation` function is equivalent to `go_model` initialized with the array size and the total produced length.
-/
lemma implementation_eq_go_model (arr : Array Int) :
  implementation arr = go_model arr arr.size arr.size (producedLen arr arr.size) arr := by
    simp +decide [ implementation, producedLen_eq_size_plus_zeros ];
    convert rfl using 1;
    -- By definition of `go_model` and `implementation.go`, we can see that they are structurally identical.
    have h_eq : ∀ (arr : Array ℤ) (limit : ℕ) (i : ℕ) (j : ℕ) (res : Array ℤ), go_model arr limit i j res = implementation.go arr limit i j res := by
      intros arr limit i j res; exact (by
      induction' i with i ih generalizing j res <;> simp +decide [ *, go_model, implementation.go ]);
    exact h_eq _ _ _ _ _

end AristotleLemmas

theorem correctness_goal_1_1 (arr : Array ℤ) (h_precond : precondition arr) (j : ℕ) (hj : j < arr.size) (i : ℕ) (hi : i < arr.size ∧ producedLen arr i ≤ j ∧ j < producedLen arr (i + 1)) (hui : ∀ (y : ℕ), y < arr.size ∧ producedLen arr y ≤ j ∧ j < producedLen arr (y + 1) → y = i) : (implementation arr)[j]! = if arr[i]! = 0 then 0 else arr[i]! := by
    convert ( go_model_correct arr arr.size arr.size ( le_rfl ) arr ( by simp ) ) j ( by linarith ) |>.1 _;
    · rw [ implementation_eq_go_model ];
      grind +ring;
    · refine' hi.2.2.trans_le _;
      apply producedLen_mono;
      linarith

end Proof