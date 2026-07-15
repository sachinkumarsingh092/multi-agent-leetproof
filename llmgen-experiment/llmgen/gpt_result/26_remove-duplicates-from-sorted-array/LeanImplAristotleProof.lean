/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 04f8f0b2-fcd6-4107-b2e2-690d1f76cc31

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem correctness_goal_0_0 (nums : Array ℤ) (h_precond : precondition nums) (h0 : ¬nums.size = 0) : postcondition nums
  (have n

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
    RemoveDuplicatesFromSortedArray: Remove duplicates from a sorted integer array in-place and return the number of unique elements.
    Natural language breakdown:
    1. The input is an array of integers `nums` that is sorted in non-decreasing order.
    2. We return a natural number `k` that equals the number of distinct values appearing in `nums`.
    3. We also return an output array `out` of the same size as `nums`.
    4. The first `k` elements of `out` contain each distinct value from `nums` exactly once.
    5. These first `k` elements are in the same order as they appear in `nums` (stability).
    6. Since `nums` is sorted, the `out` prefix of length `k` is strictly increasing.
    7. Elements of `out` at indices ≥ k are unspecified and can be ignored.
    8. Edge cases: empty array (k = 0), singleton (k = 1), all equal (k = 1), already strictly increasing (k = nums.size).
    Your algorithm should run in **O(n)** time and **O(1)** extra space.
-/

-- Helper: sorted (non-decreasing) predicate on arrays, phrased with Nat indices.
def ArraySortedLe (a : Array Int) : Prop :=
  ∀ (i : Nat), i + 1 < a.size → a[i]! ≤ a[i + 1]!

-- Helper: prefix is strictly increasing (hence no duplicates in the prefix).
def PrefixStrictIncreasing (a : Array Int) (k : Nat) : Prop :=
  k ≤ a.size ∧ ∀ (i : Nat), i + 1 < k → a[i]! < a[i + 1]!

-- Helper: membership agreement between input and the produced unique prefix.
-- Every value appearing anywhere in nums appears in the first k cells of out, and vice-versa.
def PrefixSameMembers (nums : Array Int) (k : Nat) (out : Array Int) : Prop :=
  k ≤ out.size ∧
    ∀ (x : Int), x ∈ nums ↔ (∃ (i : Nat), i < k ∧ out[i]! = x)

-- Helper: stability/order. There exists a strictly increasing index map f selecting the prefix
-- elements from nums in order. Additionally, each selected index is the first occurrence of that value.
def PrefixOccursInOrderFirst (nums : Array Int) (out : Array Int) (k : Nat) : Prop :=
  ∃ (f : Nat → Nat),
    (∀ (i : Nat), i < k → f i < nums.size ∧ out[i]! = nums[f i]!) ∧
    (∀ (i : Nat) (j : Nat), i < j → j < k → f i < f j) ∧
    (∀ (i : Nat), i < k → ∀ (j : Nat), j < f i → nums[j]! ≠ out[i]!)

-- Precondition: input is sorted in non-decreasing order.
def precondition (nums : Array Int) : Prop :=
  ArraySortedLe nums

-- Postcondition: result k is the number of unique elements; out is same size as nums;
-- first k positions are unique values in stable order; rest is irrelevant.
def postcondition (nums : Array Int) (result : Nat × Array Int) : Prop :=
  result.snd.size = nums.size ∧
    PrefixStrictIncreasing result.snd result.fst ∧
    PrefixSameMembers nums result.fst result.snd ∧
    PrefixOccursInOrderFirst nums result.snd result.fst

end Specs

section Impl

def implementation (nums : Array Int) : Nat × Array Int :=
  let n := nums.size
  if h0 : n = 0 then
    (0, nums)
  else
    -- Scan left-to-right, writing uniques into the front of `out`.
    -- Afterwards, overwrite the unused tail with zeros using a second pass
    -- implemented by primitive recursion (O(1) extra space).
    let rec go (i : Nat) (k : Nat) (last : Int) (out : Array Int) : Nat × Array Int :=
      if hi : i < n then
        let x := nums[i]!
        if x = last then
          go (i + 1) k last out
        else
          let out' := out.set! k x
          go (i + 1) (k + 1) x out'
      else
        -- zero out tail [k, n)
        let rec fill (j : Nat) (out : Array Int) : Array Int :=
          if hj : j < n then
            fill (j + 1) (out.set! j 0)
          else
            out
        termination_by n - j
        (k, fill k out)
    termination_by n - i

    let first := nums[0]!
    let out0 := nums.set! 0 first
    go 1 1 first out0

end Impl

section TestCases

-- Test case 1: Example 1
-- Input: nums = [1,1,2]
-- Output: k = 2, prefix = [1,2]
def test1_nums : Array Int := #[1, 1, 2]

def test1_Expected : Nat × Array Int := (2, #[1, 2, 0])

-- Test case 2: Example 2
-- Input: nums = [0,0,1,1,1,2,2,3,3,4]
-- Output: k = 5, prefix = [0,1,2,3,4]
def test2_nums : Array Int := #[0, 0, 1, 1, 1, 2, 2, 3, 3, 4]

def test2_Expected : Nat × Array Int := (5, #[0, 1, 2, 3, 4, 0, 0, 0, 0, 0])

-- Test case 3: Empty array
-- Output: k = 0, out empty
def test3_nums : Array Int := #[]

def test3_Expected : Nat × Array Int := (0, #[])

-- Test case 4: Singleton array
-- Output: k = 1, prefix = [7]
def test4_nums : Array Int := #[7]

def test4_Expected : Nat × Array Int := (1, #[7])

-- Test case 5: All equal elements
-- Output: k = 1, prefix = [2]
def test5_nums : Array Int := #[2, 2, 2, 2]

def test5_Expected : Nat × Array Int := (1, #[2, 0, 0, 0])

-- Test case 6: Already strictly increasing
-- Output: k = size, out may equal input
def test6_nums : Array Int := #[1, 2, 3, 4]

def test6_Expected : Nat × Array Int := (4, #[1, 2, 3, 4])

-- Test case 7: Includes negative values and duplicates
-- Input: [-3,-3,-1,-1,0,2,2] -> uniques [-3,-1,0,2]
def test7_nums : Array Int := #[-3, -3, -1, -1, 0, 2, 2]

def test7_Expected : Nat × Array Int := (4, #[-3, -1, 0, 2, 0, 0, 0])

-- Test case 8: Duplicates at the beginning only
-- Input: [0,0,0,1,2,3] -> uniques [0,1,2,3]
def test8_nums : Array Int := #[0, 0, 0, 1, 2, 3]

def test8_Expected : Nat × Array Int := (4, #[0, 1, 2, 3, 0, 0])

-- Test case 9: Duplicates at the end only
-- Input: [1,2,3,4,4,4] -> uniques [1,2,3,4]
def test9_nums : Array Int := #[1, 2, 3, 4, 4, 4]

def test9_Expected : Nat × Array Int := (4, #[1, 2, 3, 4, 0, 0])

-- Recommend to validate: precondition, postcondition, RemoveDuplicatesFromSortedArray
end TestCases

section Proof

noncomputable section AristotleLemmas

/-
A helper function modeling the tail-filling loop of the implementation.
-/
def fill_model (n : Nat) (j : Nat) (out : Array Int) : Array Int :=
  if hj : j < n then
    fill_model n (j + 1) (out.set! j 0)
  else
    out
termination_by n - j

/-
Correctness lemma for `fill_model`: it preserves size, preserves elements before `j`, and zeroes elements from `j` to `n`.
-/
theorem fill_model_correct (n : Nat) (j : Nat) (out : Array Int)
  (h_out_size : out.size = n) :
  let res := fill_model n j out
  res.size = n ∧
  (∀ i, i < j → res[i]! = out[i]!) ∧
  (∀ i, j ≤ i → i < n → res[i]! = 0) := by
  -- By induction on `n - j`, we can show that `fill_model` preserves the size and the elements before `j`.
  induction' h : n - j with k ih generalizing n j out;
  · unfold fill_model;
    grind;
  · by_cases hj : j < n <;> simp_all +decide [ Nat.sub_succ ];
    unfold fill_model; simp +decide [ hj, h_out_size ] ;
    specialize ih n ( j + 1 ) ( out.setIfInBounds j 0 ) ; simp_all +decide [ Nat.sub_succ ];
    grind

/-
Definitions for loop invariants: `PartialSameMembers` checks if the first `i` elements of `nums` contain the same set of values as the first `k` elements of `out`. `PartialOccursInOrderFirst` checks if the first `k` elements of `out` appear in `nums` (within the first `i` elements) in the correct order and are the first occurrences.
-/
def PartialSameMembers (nums : Array Int) (i : Nat) (out : Array Int) (k : Nat) : Prop :=
  ∀ (x : Int), (∃ idx < i, nums[idx]! = x) ↔ (∃ idx < k, out[idx]! = x)

def PartialOccursInOrderFirst (nums : Array Int) (i : Nat) (out : Array Int) (k : Nat) : Prop :=
  ∃ (f : Nat → Nat),
    (∀ (idx : Nat), idx < k → f idx < i ∧ out[idx]! = nums[f idx]!) ∧
    (∀ (idx1 : Nat) (idx2 : Nat), idx1 < idx2 → idx2 < k → f idx1 < f idx2) ∧
    (∀ (idx : Nat), idx < k → ∀ (j : Nat), j < f idx → nums[j]! ≠ out[idx]!)

/-
Lemma: When `nums[i] == last`, skipping it preserves the loop invariants. The set of unique elements doesn't change, and the stability mapping remains valid.
-/
theorem go_skip_preserves_invariants (nums : Array Int) (n : Nat) (i k : Nat) (last : Int) (out : Array Int)
  (hn : n = nums.size)
  (hi : i < n)
  (hk : k ≤ i)
  (hk_pos : 0 < k)
  (hi_pos : 0 < i)
  (hout_size : out.size = n)
  (h_sorted : ArraySortedLe nums)
  (h_prefix_inc : PrefixStrictIncreasing out k)
  (h_last : out[k-1]! = last)
  (h_last_nums : nums[i-1]! = last)
  (h_eq : nums[i]! = last)
  (h_members : PartialSameMembers nums i out k)
  (h_stable : PartialOccursInOrderFirst nums i out k) :
  PartialSameMembers nums (i + 1) out k ∧
  PartialOccursInOrderFirst nums (i + 1) out k := by
  constructor;
  · intro x; specialize h_members x; simp_all +decide [ PartialSameMembers ] ;
    grind;
  · obtain ⟨ f, hf1, hf2, hf3 ⟩ := h_stable;
    use f;
    exact ⟨ fun idx hidx => ⟨ Nat.lt_succ_of_lt ( hf1 idx hidx |>.1 ), hf1 idx hidx |>.2 ⟩, hf2, hf3 ⟩

/-
Lemma: When `nums[i] != last`, writing `nums[i]` to `out[k]` and incrementing `i, k` preserves the loop invariants. The prefix remains strictly increasing, the set of members is updated correctly, and the stability mapping is extended.
-/
theorem go_write_preserves_invariants (nums : Array Int) (n : Nat) (i k : Nat) (last : Int) (out : Array Int)
  (hn : n = nums.size)
  (hi : i < n)
  (hk : k ≤ i)
  (hk_pos : 0 < k)
  (hi_pos : 0 < i)
  (hout_size : out.size = n)
  (h_sorted : ArraySortedLe nums)
  (h_prefix_inc : PrefixStrictIncreasing out k)
  (h_last : out[k-1]! = last)
  (h_last_nums : nums[i-1]! = last)
  (h_ne : nums[i]! ≠ last)
  (h_members : PartialSameMembers nums i out k)
  (h_stable : PartialOccursInOrderFirst nums i out k) :
  let out' := out.set! k nums[i]!
  PrefixStrictIncreasing out' (k + 1) ∧
  out'[k]! = nums[i]! ∧
  PartialSameMembers nums (i + 1) out' (k + 1) ∧
  PartialOccursInOrderFirst nums (i + 1) out' (k + 1) := by
  refine' ⟨ _, _, _, _ ⟩;
  · refine' ⟨ _, _ ⟩;
    · grind +ring;
    · intro j hj; cases lt_or_eq_of_le ( Nat.le_of_lt_succ hj ) <;> simp_all +decide [ Array.set! ] ;
      · convert h_prefix_inc.2 j ‹_› using 1;
        · grind +ring;
        · grind;
      · have h_out_k : out[k - 1]! < nums[i]! := by
          have h_out_k : nums[i - 1]! ≤ nums[i]! := by
            specialize h_sorted ( i - 1 ) ; rcases i with ( _ | _ | i ) <;> simp_all +decide [ Nat.succ_eq_add_one ] ;
          cases lt_or_gt_of_ne ( show nums[i]! ≠ last from by cases nums ; aesop ) <;> linarith! [ h_sorted i ] ;
        grind;
  · grind +ring;
  · intro x;
    constructor;
    · rintro ⟨ idx, hidx₁, hidx₂ ⟩;
      by_cases hidx₃ : idx < i;
      · obtain ⟨ idx', hidx'₁, hidx'₂ ⟩ := h_members x |>.1 ⟨ idx, hidx₃, hidx₂ ⟩;
        use idx';
        grind;
      · use k;
        grind;
    · rintro ⟨ j, hj₁, hj₂ ⟩ ; by_cases hj₃ : j = k <;> simp_all +decide [ Array.set! ];
      · use i;
        grind;
      · have := h_members x; simp_all +decide [ Nat.lt_succ_iff ] ;
        contrapose! this;
        refine Or.inr ⟨ fun x hx => this x hx.le, j, lt_of_le_of_ne hj₁ hj₃, ?_ ⟩;
        grind;
  · obtain ⟨ f, hf ⟩ := h_stable;
    use fun j => if j = k then i else f j;
    refine' ⟨ _, _, _ ⟩;
    · grind;
    · grind;
    · intro idx hidx j hj; rcases eq_or_lt_of_le ( Nat.le_of_lt_succ hidx ) with rfl | hidx' <;> simp_all +decide ;
      · have h_sorted : nums[j]! ≤ nums[i - 1]! := by
          have h_sorted : ∀ j k, j ≤ k → k < n → nums[j]! ≤ nums[k]! := by
            intros j k hjk hk_lt_n
            induction' hjk with j k hjk ih;
            · norm_num;
            · exact le_trans ( hjk ( Nat.lt_of_succ_lt hk_lt_n ) ) ( h_sorted _ ( by linarith ) );
          exact h_sorted _ _ ( Nat.le_sub_one_of_lt hj ) ( Nat.sub_lt hi_pos zero_lt_one |> LT.lt.trans_le <| by linarith );
        have h_sorted : nums[i - 1]! ≤ nums[i]! := by
          exact ‹ArraySortedLe nums› ( i - 1 ) ( by omega ) |> fun h => by cases i <;> aesop;
        grind;
      · grind

/-
Correctness of the main loop `go`. It maintains invariants and produces a result satisfying the postcondition. Uses helper lemmas `fill_model_correct`, `go_skip_preserves_invariants`, and `go_write_preserves_invariants`.
-/
theorem go_correct (nums : Array Int) (n : Nat) (i k : Nat) (last : Int) (out : Array Int)
  (hn : n = nums.size)
  (hi : i ≤ n)
  (hk : k ≤ i)
  (hk_pos : 0 < k)
  (hi_pos : 0 < i)
  (hout_size : out.size = n)
  (h_sorted : ArraySortedLe nums)
  (h_prefix_inc : PrefixStrictIncreasing out k)
  (h_last : out[k-1]! = last)
  (h_last_nums : nums[i-1]! = last)
  (h_members : PartialSameMembers nums i out k)
  (h_stable : PartialOccursInOrderFirst nums i out k) :
  postcondition nums (implementation.go nums n i k last out) := by
  induction' h : n - i with m ih generalizing i k last out;
  · -- Since `i = n`, the loop `go` has already processed all elements, so the result is the same as the initial `out` array.
    have h_final : implementation.go nums n n k last out = (k, fill_model n k out) := by
      unfold implementation.go;
      simp +zetaDelta at *;
      -- By definition of `fill_model`, we can see that it is equivalent to the `fill` function in the `go` function.
      have h_fill_eq : ∀ (n : Nat) (j : Nat) (out : Array Int), fill_model n j out = if hj : j < n then fill_model n (j + 1) (out.set! j 0) else out := by
        exact?;
      -- By definition of `fill`, we can see that it is equivalent to the `fill_model` function.
      have h_fill_eq : ∀ (n : Nat) (j : Nat) (out : Array Int), implementation.go.fill n j out = if hj : j < n then implementation.go.fill n (j + 1) (out.set! j 0) else out := by
        exact?;
      -- By induction on `n - j`, we can show that `fill_model n j out` and `implementation.go.fill n j out` are equal.
      have h_ind : ∀ (n j : Nat) (out : Array Int), j ≤ n → fill_model n j out = implementation.go.fill n j out := by
        intros n j out hj_le_n
        induction' m : n - j with m ih generalizing j out;
        · grind;
        · grind;
      rw [ h_ind n k out ( by linarith ) ];
    -- By definition of `fill_model`, we know that `fill_model n k out` preserves the size of `out` and the elements in `0..k`.
    have h_fill_model : let res := fill_model n k out; res.size = n ∧ (∀ i, i < k → res[i]! = out[i]!) ∧ (∀ i, k ≤ i → i < n → res[i]! = 0) := by
      exact fill_model_correct n k out hout_size |> fun h => ⟨ h.1, h.2.1, h.2.2 ⟩
    generalize_proofs at *; (
    -- By definition of `postcondition`, we need to show that the size of `out` is `n`, the prefix is strictly increasing, and the members are the same.
    unfold postcondition; simp_all +decide [ Nat.sub_add_cancel hi ] ;
    rw [ show i = nums.size by omega ] ; simp_all +decide [ PrefixStrictIncreasing, PrefixSameMembers, PrefixOccursInOrderFirst ] ;
    refine' ⟨ _, _, _ ⟩ <;> simp_all +decide [ PartialSameMembers, PartialOccursInOrderFirst ];
    · exact fun i hi => by rw [ h_fill_model.2.1 i ( by linarith ) ] ; exact h_prefix_inc.2 i hi;
    · intro x; specialize h_members x; simp_all +decide [ Array.mem_iff_getElem ] ;
      convert h_members using 1 <;> simp_all +decide [ Nat.sub_eq_iff_eq_add ] ;
      · convert h_members using 1 ; simp +decide [ ← h ] ;
        exact ⟨ fun ⟨ i, hi, hi' ⟩ => ⟨ i, hi, by simpa [ hi ] using hi' ⟩, fun ⟨ i, hi, hi' ⟩ => ⟨ i, hi, by simpa [ hi ] using hi' ⟩ ⟩;
      · exact ⟨ fun ⟨ i, hi, hi' ⟩ => ⟨ i, hi, h_fill_model.2.1 i hi ▸ hi' ⟩, fun ⟨ i, hi, hi' ⟩ => ⟨ i, hi, h_fill_model.2.1 i hi ▸ hi' ⟩ ⟩;
    · exact ⟨ h_stable.choose, fun i hi => ⟨ by linarith [ h_stable.choose_spec.1 i hi ], h_stable.choose_spec.1 i hi |>.2 ⟩, h_stable.choose_spec.2.1, h_stable.choose_spec.2.2 ⟩);
  · unfold implementation.go; simp +decide [ * ] ;
    split_ifs;
    · convert ih ( i + 1 ) k last out ( by linarith ) ( by linarith ) ( by linarith ) ( by linarith ) ( by linarith ) h_prefix_inc h_last ( by
        aesop ) _ _ _ using 1
      all_goals generalize_proofs at *;
      · rw [ hn ];
      · convert go_skip_preserves_invariants nums n i k last out hn ( by linarith ) hk hk_pos hi_pos hout_size h_sorted h_prefix_inc h_last h_last_nums ( by linarith ) h_members h_stable |> And.left using 1;
      · convert go_skip_preserves_invariants nums n i k last out hn ( by linarith ) hk hk_pos hi_pos hout_size h_sorted h_prefix_inc h_last h_last_nums ‹_› h_members h_stable |> And.right using 1;
      · omega;
    · convert ih ( i + 1 ) ( k + 1 ) ( nums[i]! ) ( out.setIfInBounds k nums[i]! ) ( by linarith ) ( by omega ) ( by omega ) ( by omega ) _ _ _ _ _ _ using 1 <;> norm_num [ * ];
      · exact Or.inl ( by omega );
      · convert go_write_preserves_invariants nums n i k last out hn ( by linarith ) hk hk_pos hi_pos hout_size h_sorted h_prefix_inc h_last h_last_nums ( by tauto ) ( by tauto ) ( by tauto ) |>.1 using 1;
        grind +ring;
      · grind;
      · have := go_write_preserves_invariants nums n i k last out hn ( by linarith ) hk hk_pos hi_pos hout_size h_sorted h_prefix_inc h_last h_last_nums ‹_› h_members h_stable; aesop;
      · have := go_write_preserves_invariants nums n i k last out hn ( by linarith ) hk hk_pos hi_pos hout_size h_sorted h_prefix_inc h_last h_last_nums ( by tauto ) h_members h_stable; aesop;
    · omega

end AristotleLemmas

theorem correctness_goal_0_0 (nums : Array ℤ) (h_precond : precondition nums) (h0 : ¬nums.size = 0) : postcondition nums
  (have n := nums.size;
  if h0 : n = 0 then (0, nums)
  else
    have first := nums[0]!;
    have out0 := nums.set! 0 first;
    implementation.go nums n 1 1 first out0) := by
    simp +zetaDelta at *;
    split_ifs ; simp_all +decide [ Array.setIfInBounds ];
    apply go_correct; aesop;
    any_goals tauto;
    · exact Nat.pos_of_ne_zero ( by aesop );
    · exact ⟨ by linarith [ Array.size_pos_iff.mpr h0 ], by intros; linarith ⟩;
    · use fun _ => 0; aesop;

end Proof