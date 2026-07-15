/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 353f9d6a-ec81-4d94-b15e-abb625b16c73

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem correctness_goal (nums1 : Array Int) (nums2 : Array Int) (h_precond : precondition nums1 nums2) : postcondition nums1 nums2 (implementation nums1 nums2)

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
    MergeSortedArrays: Merge two sorted integer arrays into a new sorted array.
    Natural language breakdown:
    1. Inputs are two arrays of integers, `nums1` and `nums2`.
    2. Each input array is sorted in non-decreasing order.
    3. The output is a new array whose length is `nums1.size + nums2.size`.
    4. The output is sorted in non-decreasing order.
    5. The output contains exactly the multiset union of elements of `nums1` and `nums2`:
       for every integer value, its number of occurrences in the output equals the sum of its
       occurrences in the two inputs.
    6. Edge cases include empty inputs, singleton inputs, duplicates, and negative values.
    Your algorithm should run in **O(m+n)** time and **O(m+n)** extra space, where m = nums1.size and n = nums2.size.
-/

-- Helper predicate: an array is sorted in non-decreasing order.
-- We use adjacent comparisons (local sortedness) for a simple, index-based formulation.
def sortedNondecreasing (a : Array Int) : Prop :=
  ∀ (i : Nat), i + 1 < a.size → a[i]! ≤ a[i + 1]!

-- Helper function: count occurrences of a value in an array.
def countInArray (a : Array Int) (v : Int) : Nat :=
  a.toList.count v

-- Preconditions: both input arrays are sorted in non-decreasing order.
def precondition (nums1 : Array Int) (nums2 : Array Int) : Prop :=
  sortedNondecreasing nums1 ∧ sortedNondecreasing nums2

-- Postconditions: result has the correct size, is sorted, and contains exactly all elements.
def postcondition (nums1 : Array Int) (nums2 : Array Int) (result : Array Int) : Prop :=
  result.size = nums1.size + nums2.size ∧
  sortedNondecreasing result ∧
  ∀ v : Int, countInArray result v = countInArray nums1 v + countInArray nums2 v

end Specs

section Impl

def implementation (nums1 : Array Int) (nums2 : Array Int) : Array Int :=
  -- Pure functional linear-time merge using index recursion.
  let rec go (i j : Nat) (acc : Array Int) : Array Int :=
    if hi : i < nums1.size then
      if hj : j < nums2.size then
        let x := nums1[i]!
        let y := nums2[j]!
        if x ≤ y then
          go (i + 1) j (acc.push x)
        else
          go i (j + 1) (acc.push y)
      else
        -- nums2 exhausted; drain the rest of nums1
        let rec drain1 (k : Nat) (acc : Array Int) : Array Int :=
          if hk : k < nums1.size then
            drain1 (k + 1) (acc.push (nums1[k]!))
          else
            acc
        drain1 i acc
    else
      if hj : j < nums2.size then
        -- nums1 exhausted; drain the rest of nums2
        let rec drain2 (k : Nat) (acc : Array Int) : Array Int :=
          if hk : k < nums2.size then
            drain2 (k + 1) (acc.push (nums2[k]!))
          else
            acc
        drain2 j acc
      else
        acc
  go 0 0 #[]
termination_by
  (nums1.size - i) + (nums2.size - j)

end Impl

section TestCases

-- Test case 1: Example 1
-- nums1 = [1,2,3], nums2 = [2,5,6] => [1,2,2,3,5,6]
def test1_nums1 : Array Int := #[1, 2, 3]

def test1_nums2 : Array Int := #[2, 5, 6]

def test1_Expected : Array Int := #[1, 2, 2, 3, 5, 6]

-- Test case 2: Example 2
-- nums1 = [1], nums2 = [] => [1]
def test2_nums1 : Array Int := #[1]

def test2_nums2 : Array Int := #[]

def test2_Expected : Array Int := #[1]

-- Test case 3: Example 3
-- nums1 = [], nums2 = [1] => [1]
def test3_nums1 : Array Int := #[]

def test3_nums2 : Array Int := #[1]

def test3_Expected : Array Int := #[1]

-- Test case 4: Both empty
-- [] and [] => []
def test4_nums1 : Array Int := #[]

def test4_nums2 : Array Int := #[]

def test4_Expected : Array Int := #[]

-- Test case 5: Duplicates across both arrays
-- [1,1,1] and [1,1] => [1,1,1,1,1]
def test5_nums1 : Array Int := #[1, 1, 1]

def test5_nums2 : Array Int := #[1, 1]

def test5_Expected : Array Int := #[1, 1, 1, 1, 1]

-- Test case 6: Negative values and mix
-- [-3,-1,2] and [-2,0,3] => [-3,-2,-1,0,2,3]
def test6_nums1 : Array Int := #[-3, -1, 2]

def test6_nums2 : Array Int := #[-2, 0, 3]

def test6_Expected : Array Int := #[-3, -2, -1, 0, 2, 3]

-- Test case 7: Already separated ranges
-- [1,2,3] and [4,5] => [1,2,3,4,5]
def test7_nums1 : Array Int := #[1, 2, 3]

def test7_nums2 : Array Int := #[4, 5]

def test7_Expected : Array Int := #[1, 2, 3, 4, 5]

-- Test case 8: Interleaving with equal boundary values and many duplicates
-- [0,2,2,2] and [2,2,3] => [0,2,2,2,2,2,3]
def test8_nums1 : Array Int := #[0, 2, 2, 2]

def test8_nums2 : Array Int := #[2, 2, 3]

def test8_Expected : Array Int := #[0, 2, 2, 2, 2, 2, 3]

-- Test case 9: Singleton + singleton with ordering
-- [0] and [1] => [0,1]
def test9_nums1 : Array Int := #[0]

def test9_nums2 : Array Int := #[1]

def test9_Expected : Array Int := #[0, 1]

end TestCases

section Proof

theorem correctness_goal (nums1 : Array Int) (nums2 : Array Int) (h_precond : precondition nums1 nums2) : postcondition nums1 nums2 (implementation nums1 nums2) := by
    -- By definition of `implementation`, the resulting array is the merge of `nums1` and `nums2`.
    have h_merge : (implementation nums1 nums2).toList = List.merge nums1.toList nums2.toList := by
      -- By definition of `implementation.go`, the resulting list is the merge of `nums1.toList` and `nums2.toList`.
      have h_merge : ∀ (i j : Nat) (acc : Array Int), (implementation.go nums1 nums2 i j acc).toList = acc.toList ++ List.merge (List.drop i nums1.toList) (List.drop j nums2.toList) := by
        intros i j acc
        induction' h : (nums1.size - i) + (nums2.size - j) using Nat.strong_induction_on with h ih generalizing i j acc;
        unfold implementation.go;
        split_ifs <;> simp_all +decide [ List.drop_eq_nil_of_le ];
        · split_ifs <;> simp_all +decide [ List.drop_eq_getElem_cons ];
          · rw [ ih _ _ _ _ _ rfl ];
            · simp +decide [ List.drop_eq_getElem_cons, * ];
            · omega;
          · rw [ ih _ _ _ _ _ rfl ];
            · simp +decide [ List.drop_eq_getElem_cons, * ];
            · omega;
        · -- By definition of `drain1`, we can prove this by induction on the size of `nums1`.
          have h_drain1_induction : ∀ (i : ℕ) (acc : Array ℤ), i ≤ nums1.size → (implementation.go.drain1 nums1 i acc).toList = acc.toList ++ List.drop i nums1.toList := by
            intros i acc hi;
            induction' h : nums1.size - i with k ih generalizing i acc;
            · -- Since `i = nums1.size`, the drain1 function returns the accumulator `acc`.
              have h_drain1_base : implementation.go.drain1 nums1 nums1.size acc = acc := by
                unfold implementation.go.drain1; aesop;
              rw [ Nat.sub_eq_iff_eq_add ] at h <;> aesop;
            · unfold implementation.go.drain1;
              split_ifs <;> simp_all +decide [ Nat.sub_succ ];
              convert ih ( i + 1 ) ( acc.push nums1[i] ) ( by linarith ) ( by omega ) using 1;
              rw [ List.drop_eq_getElem_cons ];
              all_goals simp +decide [ *, Array.toList ];
          exact h_drain1_induction i acc ( le_of_lt ‹_› );
        · -- By definition of `drain2`, we can prove this by induction on the number of elements left to drain.
          have h_drain2_ind : ∀ (k : Nat) (acc : Array Int), k ≤ nums2.size → (implementation.go.drain2 nums2 k acc).toList = acc.toList ++ List.drop k nums2.toList := by
            intros k acc hk;
            induction' hk : nums2.size - k with m ih generalizing k acc;
            · -- Since $k = \text{nums2.size}$, the drain2 function returns the accumulator as is.
              have h_k_eq_size : k = nums2.size := by
                omega;
              unfold implementation.go.drain2; aesop;
            · unfold implementation.go.drain2;
              split_ifs <;> simp_all +decide [ List.drop_eq_getElem_cons ];
              convert ih ( k + 1 ) ( acc.push nums2[k] ) ( by linarith ) ( by omega ) using 1;
              simp +decide [ Array.toList ];
          exact h_drain2_ind _ _ ( by linarith );
      aesop;
    refine' ⟨ _, _, _ ⟩;
    · replace h_merge := congr_arg List.length h_merge ; aesop;
    · -- Since `nums1` and `nums2` are sorted, their merge is also sorted.
      have h_sorted : List.Sorted (· ≤ ·) (nums1.toList.merge nums2.toList) := by
        have h_sorted : List.Sorted (· ≤ ·) nums1.toList ∧ List.Sorted (· ≤ ·) nums2.toList := by
          -- Since `nums1` and `nums2` are sorted, their toList representations are also sorted.
          have h_sorted : ∀ (a : Array ℤ), sortedNondecreasing a → List.Sorted (· ≤ ·) a.toList := by
            -- If the array is sorted, then the list obtained by converting the array to a list is also sorted.
            intros a ha
            have h_adj : ∀ i, i + 1 < a.size → a[i]! ≤ a[i + 1]! := by
              exact ha;
            have h_sorted : ∀ i j, i < j → i < a.size → j < a.size → a[i]! ≤ a[j]! := by
              -- By induction on $j - i$, we can show that $a[i]! \leq a[j]!$ for any $i < j$.
              intros i j hij hi hj
              induction' hij with j hj ih;
              · exact h_adj i hj;
              · exact le_trans ( ih ( Nat.lt_of_succ_lt hj ) ) ( h_adj _ hj );
            refine' List.pairwise_iff_get.mpr _;
            aesop;
          exact ⟨ h_sorted nums1 h_precond.1, h_sorted nums2 h_precond.2 ⟩;
        -- Apply the fact that the merge of two sorted lists is also sorted.
        apply List.Sorted.merge; exact h_sorted.left; exact h_sorted.right;
      rw [ List.Sorted ] at h_sorted;
      rw [ List.pairwise_iff_get ] at h_sorted;
      -- Apply the hypothesis `h_sorted` to the indices `i` and `i + 1`.
      intros i hi
      specialize h_sorted ⟨i, by
        grind⟩ ⟨i + 1, by
        grind +ring⟩ (Nat.lt_succ_self i)
      generalize_proofs at *;
      grind +ring;
    · -- By definition of `countInArray`, we can rewrite the goal in terms of the counts in the original lists.
      intro v
      simp [countInArray, h_merge];
      have h_count_merge : ∀ (l1 l2 : List ℤ), List.count v (List.merge l1 l2 (fun a b => a ≤ b)) = List.count v l1 + List.count v l2 := by
        intros l1 l2; induction' l1 with a l1 ih generalizing l2 <;> induction' l2 with b l2 ih' <;> simp +decide [ *, List.merge ] ;
        grind +ring;
      grind

end Proof