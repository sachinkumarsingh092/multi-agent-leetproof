/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 17308414-96f6-4d27-8b0f-8825374f291f

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem correctness_goal (nums : Array Int) (h_precond : precondition nums) : postcondition nums (implementation (nums))

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
    MoveZeroes: Move all 0 values to the end of an integer array while preserving the relative order of non-zero elements.
    Natural language breakdown:
    1. Input is an array of integers.
    2. The output is an array of integers with the same length as the input.
    3. The output contains exactly the same multiset of values as the input (no values are lost or created).
    4. All non-zero elements appear before all zero elements in the output (zeros form a suffix).
    5. The relative order of the non-zero elements is preserved: scanning left-to-right, the sequence of non-zero values
       in the output is exactly the sequence of non-zero values in the input.
    Your algorithm should run in **O(n)** time and **O(1)** extra space (in-place).
-/

-- Helper: count occurrences of a value in an array.
-- (Computable; used to express multiset preservation without defining a concrete implementation of MoveZeroes.)
def countVal (arr : Array Int) (v : Int) : Nat :=
  arr.foldl (fun (acc : Nat) (x : Int) => if x = v then acc + 1 else acc) 0

-- Helper: output has all zeros grouped at the end.
-- If a position is zero, everything to its right is also zero.
def zerosFormSuffix (output : Array Int) : Prop :=
  ∀ (k : Nat),
    k < output.size →
    output[k]! = 0 →
    ∀ (j : Nat), k < j → j < output.size → output[j]! = 0

-- Helper: a nonzero index predicate (kept small and decidable-looking).
def isNonZeroIndex (a : Array Int) (i : Nat) : Prop :=
  i < a.size ∧ a[i]! ≠ 0

-- Helper: the output nonzero prefix corresponds exactly to the input nonzero elements in order.
-- We use a strictly-increasing mapping f from input indices (where input[i] != 0) to output indices.
-- This expresses stability without giving an algorithm.
def preservesNonZeroOrder (input : Array Int) (output : Array Int) : Prop :=
  ∃ (f : Nat → Nat),
    (∀ (i : Nat), isNonZeroIndex input i → f i < output.size ∧ output[(f i)]! = input[i]!) ∧
    (∀ (i : Nat) (j : Nat), i < j → isNonZeroIndex input i → isNonZeroIndex input j → f i < f j) ∧
    (∀ (p : Nat), p < output.size → output[p]! ≠ 0 → ∃ (i : Nat), isNonZeroIndex input i ∧ f i = p)

-- Preconditions: none (any array is valid).
def precondition (nums : Array Int) : Prop :=
  True

-- Postcondition:
-- 1) same size
-- 2) same multiset of values (via per-value counts)
-- 3) zeros form a suffix
-- 4) stable preservation of the entire nonzero subsequence (via an order-isomorphism style mapping)
def postcondition (nums : Array Int) (result : Array Int) : Prop :=
  result.size = nums.size ∧
  (∀ (v : Int), countVal nums v = countVal result v) ∧
  zerosFormSuffix result ∧
  preservesNonZeroOrder nums result

end Specs

section Impl

def implementation (nums : Array Int) : Array Int :=
  -- In-place style (O(1) extra space in an imperative setting):
  -- scan left-to-right, writing nonzeros to the next write position;
  -- then fill the remaining suffix with zeros.
  let n := nums.size
  let step (st : Nat × Array Int) (x : Int) : Nat × Array Int :=
    let (w, a) := st
    if x = 0 then
      (w, a)
    else
      -- write x at position w (which is always < n)
      (w + 1, a.set! w x)
  let (w, a1) := nums.foldl step (0, nums)
  let rec fillZeros (a : Array Int) (i : Nat) : Array Int :=
    if h : i < n then
      fillZeros (a.set! i 0) (i + 1)
    else
      a
  termination_by n - i
  fillZeros a1 w

end Impl

section TestCases

-- Test case 1: Example 1
-- Input: [0,1,0,3,12]
-- Output: [1,3,12,0,0]
def test1_nums : Array Int := #[0, 1, 0, 3, 12]

def test1_Expected : Array Int := #[1, 3, 12, 0, 0]

-- Test case 2: Example 2
-- Input: [0]
-- Output: [0]
def test2_nums : Array Int := #[0]

def test2_Expected : Array Int := #[0]

-- Test case 3: Empty array
-- Input: []
-- Output: []
def test3_nums : Array Int := #[]

def test3_Expected : Array Int := #[]

-- Test case 4: No zeros
-- Input: [1,2,3]
-- Output: [1,2,3]
def test4_nums : Array Int := #[1, 2, 3]

def test4_Expected : Array Int := #[1, 2, 3]

-- Test case 5: All zeros
-- Input: [0,0,0]
-- Output: [0,0,0]
def test5_nums : Array Int := #[0, 0, 0]

def test5_Expected : Array Int := #[0, 0, 0]

-- Test case 6: Zeros already at end
-- Input: [5,0,0]
-- Output: [5,0,0]
def test6_nums : Array Int := #[5, 0, 0]

def test6_Expected : Array Int := #[5, 0, 0]

-- Test case 7: Alternating including negatives
-- Input: [0,-1,0,-2,3]
-- Output: [-1,-2,3,0,0]
def test7_nums : Array Int := #[0, -1, 0, -2, 3]

def test7_Expected : Array Int := #[-1, -2, 3, 0, 0]

-- Test case 8: Duplicates of non-zero values and multiple zeros
-- Input: [1,0,1,0,1]
-- Output: [1,1,1,0,0]
def test8_nums : Array Int := #[1, 0, 1, 0, 1]

def test8_Expected : Array Int := #[1, 1, 1, 0, 0]

-- Test case 9: Mix with repeated negatives and zeros
-- Input: [-1,0,-1,2,0]
-- Output: [-1,-1,2,0,0]
def test9_nums : Array Int := #[-1, 0, -1, 2, 0]

def test9_Expected : Array Int := #[-1, -1, 2, 0, 0]

-- Recommend to validate: MoveZeroes, precondition, postcondition
end TestCases

section Proof

noncomputable section AristotleLemmas

def MoveZeroes.step (st : Nat × Array Int) (x : Int) : Nat × Array Int :=
  let (w, a) := st
  if x = 0 then
    (w, a)
  else
    (w + 1, a.set! w x)

def MoveZeroes.fillZerosAux (n : Nat) (a : Array Int) (i : Nat) : Array Int :=
  if h : i < n then
    MoveZeroes.fillZerosAux n (a.set! i 0) (i + 1)
  else
    a
termination_by n - i

lemma MoveZeroes.foldl_step_w (l : List Int) (w : Nat) (a : Array Int) :
  (l.foldl MoveZeroes.step (w, a)).1 = w + (l.filter (· ≠ 0)).length := by
    -- We can prove this by induction on the list `l`.
    induction' l with x l ih generalizing w a <;> simp_all +decide [ List.foldl ];
    -- By definition of `MoveZeroes.step`, we have:
    by_cases hx : x = 0 <;> simp [hx, MoveZeroes.step];
    -- By commutativity of addition, we can rearrange the terms on the right-hand side.
    ring

lemma MoveZeroes.foldl_step_size (l : List Int) (w : Nat) (a : Array Int) :
  (l.foldl MoveZeroes.step (w, a)).2.size = a.size := by
    -- By induction on the list l, we can show that the size of the array remains the same after each step.
    induction' l with x l ih generalizing w a;
    · rfl;
    · -- By definition of `MoveZeroes.step`, if `x` is zero, the array remains the same, so the size is preserved. If `x` is not zero, the array is modified by setting the `w`-th element to `x`, but the size remains the same.
      simp [MoveZeroes.step, ih];
      -- If x is zero, the array remains the same, so the size is preserved. If x is not zero, the array is modified by setting the w-th element to x, but the size remains the same.
      split_ifs <;> simp [ih]

lemma MoveZeroes.foldl_step_stable_left (l : List Int) (w : Nat) (a : Array Int) :
  let (w', a') := l.foldl MoveZeroes.step (w, a)
  ∀ i, i < w → a'[i]! = a[i]! := by
    -- By induction on the list l, we can show that the elements at positions less than w in the array a' are the same as in a.
    induction' l with x l ih generalizing w a;
    · aesop;
    · -- By definition of `MoveZeroes.step`, we know that the elements at positions less than w in the array a' are the same as in a.
      intros i hi
      simp [MoveZeroes.step];
      grind

lemma MoveZeroes.foldl_step_content (l : List Int) (w : Nat) (a : Array Int)
  (h_sz : w + (l.filter (· ≠ 0)).length ≤ a.size) :
  let (w', a') := l.foldl MoveZeroes.step (w, a)
  ∀ k (hk : k < (l.filter (· ≠ 0)).length),
    a'[w + k]! = (l.filter (· ≠ 0))[k] := by
      induction' l using List.reverseRecOn with l ih generalizing w a ; aesop;
      by_cases h : ih = 0 <;> simp_all +decide [ List.filter_cons ];
      · unfold MoveZeroes.step; aesop;
      · intro k hk; cases hk <;> simp_all +decide [ MoveZeroes.step ] ;
        · -- By definition of `MoveZeroes.step`, the write position `w` is incremented for each non-zero element in `l`.
          have h_w : (List.foldl MoveZeroes.step (w, a) l).1 = w + (List.filter (fun x => x ≠ 0) l).length := by
            convert MoveZeroes.foldl_step_w l w a using 1;
          simp_all +decide [ Array.setIfInBounds ];
          split_ifs <;> simp_all +decide [ Array.set ];
          linarith [ show ( List.foldl MoveZeroes.step ( w, a ) l ).2.size = a.size from by exact? ];
        · rename_i hk;
          rename_i h';
          convert h' w a ( by linarith ) k ( Nat.lt_of_succ_le hk ) using 1;
          · -- Since the position (w + k) is not within the bounds of the array, the element at (w + k) remains unchanged.
            have h_bound : (List.foldl MoveZeroes.step (w, a) l).1 = w + (List.filter (fun x => !Decidable.decide (x = 0)) l).length := by
              convert MoveZeroes.foldl_step_w l w a using 1;
              grind;
            grind +ring;
          · grind +ring

lemma MoveZeroes.fillZerosAux_spec (n : Nat) (a : Array Int) (i : Nat)
  (h_i : i ≤ n) (h_sz : n ≤ a.size) :
  let res := MoveZeroes.fillZerosAux n a i
  res.size = a.size ∧
  (∀ k, k < i → res[k]! = a[k]!) ∧
  (∀ k, i ≤ k → k < n → res[k]! = 0) ∧
  (∀ k, n ≤ k → k < a.size → res[k]! = a[k]!) := by
    -- We'll use induction on the difference between `n` and `i`.
    induction' h : n - i with d hd generalizing i a;
    · -- Since $n - i = 0$, we have $i = n$. Therefore, the function `fillZerosAux` does not change the array.
      have h_eq : i = n := by
        omega;
      unfold MoveZeroes.fillZerosAux; aesop;
    · unfold MoveZeroes.fillZerosAux; simp +decide [ h, hd ] ;
      split_ifs <;> simp_all +decide [ Nat.sub_eq_iff_eq_add' h_i ];
      grind

lemma MoveZeroes.implementation_eq (nums : Array Int) :
  implementation nums = MoveZeroes.fillZerosAux nums.size (nums.foldl MoveZeroes.step (0, nums)).2 (nums.foldl MoveZeroes.step (0, nums)).1 := by
    -- By definition of `implementation`, we know that it is equal to the fillZerosAux function applied to the result of the foldl step.
    simp [implementation];
    congr! 1;
    -- By definition of `implementation.fillZeros`, we know that it is equal to `MoveZeroes.fillZerosAux`.
    funext n a i; exact (by
    -- By definition of `implementation.fillZeros`, we know that it is equal to `MoveZeroes.fillZerosAux` by definition.
    unfold implementation.fillZeros; exact (by
    -- By definition of `MoveZeroes.fillZerosAux`, we can rewrite the right-hand side of the equation.
    rw [MoveZeroes.fillZerosAux];
    -- By induction on $n - i$, we can show that the two functions are equal.
    induction' h : n - i with k ih generalizing i a;
    · grind;
    · convert ih ( a.setIfInBounds i 0 ) ( i + 1 ) _ using 1;
      · rw [ implementation.fillZeros ];
        aesop;
      · rw [ MoveZeroes.fillZerosAux ];
        split_ifs <;> simp_all +decide [ Nat.lt_succ_iff ];
      · omega))

end AristotleLemmas

theorem correctness_goal (nums : Array Int) (h_precond : precondition nums) : postcondition nums (implementation (nums)) := by
    refine' ⟨ _, _, _, _ ⟩;
    · rw [ MoveZeroes.implementation_eq ];
      rw [ MoveZeroes.fillZerosAux_spec _ _ _ ( by
        have := MoveZeroes.foldl_step_w nums.toList 0 nums;
        grind ) ( by
        -- The size of the array remains unchanged after the foldl operation.
        have h_size : ∀ (l : List Int) (w : Nat) (a : Array Int), (l.foldl MoveZeroes.step (w, a)).2.size = a.size := by
          exact?;
        induction nums using Array.recOn ; aesop ) |>.1 ];
      convert MoveZeroes.foldl_step_size _ _ _;
      rw [ ← Array.foldl_toList ];
    · intro v
      unfold countVal at *;
      -- By definition of `implementation`, we know that it rearranges the elements of `nums` such that all zeros are at the end.
      have h_rearrange : (implementation nums).toList = (nums.toList.filter (· ≠ 0)) ++ List.replicate (nums.size - (nums.toList.filter (· ≠ 0)).length) 0 := by
        rw [ MoveZeroes.implementation_eq ];
        -- By definition of `MoveZeroes.foldl_step_content`, we know that the first `w` elements of `a1` are the non-zero elements of `nums`.
        have h_foldl_step_content : ∀ k (hk : k < (nums.toList.filter (· ≠ 0)).length), (Array.foldl MoveZeroes.step (0, nums) nums |>.2)[k]! = (nums.toList.filter (· ≠ 0))[k]! := by
          convert MoveZeroes.foldl_step_content nums.toList 0 nums _ using 1;
          · aesop;
          · grind;
        -- By definition of `MoveZeroes.fillZerosAux`, we know that the elements of `res` are the non-zero elements of `nums` followed by zeros.
        have h_fillZerosAux : ∀ k (hk : k < nums.size), (MoveZeroes.fillZerosAux nums.size (Array.foldl MoveZeroes.step (0, nums) nums).2 (Array.foldl MoveZeroes.step (0, nums) nums).1)[k]! = if k < (nums.toList.filter (· ≠ 0)).length then (nums.toList.filter (· ≠ 0))[k]! else 0 := by
          intro k hk
          have h_fillZerosAux_spec : (MoveZeroes.fillZerosAux nums.size (Array.foldl MoveZeroes.step (0, nums) nums).2 (Array.foldl MoveZeroes.step (0, nums) nums).1).size = nums.size ∧ (∀ k, k < (Array.foldl MoveZeroes.step (0, nums) nums).1 → (MoveZeroes.fillZerosAux nums.size (Array.foldl MoveZeroes.step (0, nums) nums).2 (Array.foldl MoveZeroes.step (0, nums) nums).1)[k]! = (Array.foldl MoveZeroes.step (0, nums) nums).2[k]!) ∧ (∀ k, (Array.foldl MoveZeroes.step (0, nums) nums).1 ≤ k → k < nums.size → (MoveZeroes.fillZerosAux nums.size (Array.foldl MoveZeroes.step (0, nums) nums).2 (Array.foldl MoveZeroes.step (0, nums) nums).1)[k]! = 0) := by
            have := MoveZeroes.fillZerosAux_spec nums.size (Array.foldl MoveZeroes.step (0, nums) nums).2 (Array.foldl MoveZeroes.step (0, nums) nums).1 (by
            have h_foldl_step_w : (Array.foldl MoveZeroes.step (0, nums) nums).1 = (nums.toList.filter (· ≠ 0)).length := by
              convert MoveZeroes.foldl_step_w nums.toList 0 nums using 1;
              · conv => rw [ ← Array.foldl_toList ] ;
              · norm_num;
            exact h_foldl_step_w.symm ▸ le_trans ( List.length_filter_le _ _ ) ( by simpa )) (by
            have h_foldl_step_size : (Array.foldl MoveZeroes.step (0, nums) nums).2.size = nums.size := by
              convert MoveZeroes.foldl_step_size nums.toList 0 nums using 1;
              conv => rw [ ← Array.foldl_toList ] ;
            rw [h_foldl_step_size]);
            have := MoveZeroes.foldl_step_size nums.toList 0 nums; aesop;
          split_ifs;
          · rw [ h_fillZerosAux_spec.2.1 k, h_foldl_step_content k ‹_› ];
            convert ‹k < ( List.filter ( fun x => Decidable.decide ( x ≠ 0 ) ) nums.toList ).length› using 1;
            convert MoveZeroes.foldl_step_w nums.toList 0 nums using 1;
            · conv => rw [ ← Array.foldl_toList ] ;
            · norm_num;
          · have := MoveZeroes.foldl_step_w nums.toList 0 nums; aesop;
        refine' List.ext_get _ _ <;> simp_all +decide [ List.get ];
        · rw [ MoveZeroes.fillZerosAux_spec _ _ _ ( by
            have h_foldl_step_w : (Array.foldl MoveZeroes.step (0, nums) nums).1 = (nums.toList.filter (· ≠ 0)).length := by
              convert MoveZeroes.foldl_step_w nums.toList 0 nums using 1;
              · conv => rw [ ← Array.foldl_toList ] ;
              · norm_num;
            grind ) ( by
            have h_foldl_step_size : ∀ (l : List ℤ) (w : Nat) (a : Array ℤ), (List.foldl MoveZeroes.step (w, a) l).2.size = a.size := by
              exact?;
            convert h_foldl_step_size nums.toList 0 nums |> Eq.ge using 1;
            conv => rw [ ← Array.foldl_toList ] ; ) |>.1, Nat.add_sub_of_le ];
          · convert MoveZeroes.foldl_step_size _ _ _;
            rotate_left;
            exact nums.toList;
            exact 0;
            grind;
          · exact le_trans ( List.length_filter_le _ _ ) ( by simpa );
        · grind;
      -- By definition of `countVal`, we can rewrite the goal in terms of the number of occurrences of `v` in `nums` and `implementation nums`.
      have h_count_eq : (nums.toList.filter (· ≠ 0)).count v + (nums.size - (nums.toList.filter (· ≠ 0)).length) * (if v = 0 then 1 else 0) = nums.toList.count v := by
        by_cases hv : v = 0 <;> simp +decide [ hv ];
        have h_count_zero : List.count 0 (List.filter (fun x => !Decidable.decide (x = 0)) nums.toList) = 0 := by
          rw [ List.count_eq_zero ] ; aesop;
        have h_count_zero : List.length (List.filter (fun x => x = 0) nums.toList) = Array.count 0 nums := by
          grind;
        have h_count_zero : List.length (List.filter (fun x => x = 0) nums.toList) + List.length (List.filter (fun x => !Decidable.decide (x = 0)) nums.toList) = nums.size := by
          have h_count_zero : ∀ (l : List ℤ), List.length (List.filter (fun x => x = 0) l) + List.length (List.filter (fun x => !Decidable.decide (x = 0)) l) = l.length := by
            exact?;
          exact h_count_zero _;
        omega;
      convert h_count_eq.symm using 1;
      · conv => rw [ ← Array.foldl_toList ] ;
        induction' nums.toList using List.reverseRecOn with x xs ih <;> aesop;
      · convert congr_arg ( fun l : List ℤ => List.count v l ) h_rearrange using 1;
        · conv => rw [ ← Array.foldl_toList ] ;
          induction' ( implementation nums ).toList using List.reverseRecOn with x xs ih <;> aesop;
        · grind +ring;
    · intro k hk hk' j hj₁ hj₂;
      -- By definition of `implementation`, we know that `implementation nums` is the result of `fillZerosAux` with `i = w`.
      obtain ⟨w, a1, hw, ha1⟩ : ∃ w a1, (nums.foldl MoveZeroes.step (0, nums)) = (w, a1) ∧ (implementation nums) = MoveZeroes.fillZerosAux nums.size a1 w := by
        exact ⟨ _, _, rfl, MoveZeroes.implementation_eq nums ⟩;
      -- By definition of `fillZerosAux`, we know that `fillZerosAux nums.size a1 w` has all zeros at the end.
      have h_fillZerosAux : (MoveZeroes.fillZerosAux nums.size a1 w).size = a1.size ∧ (∀ k, k < w → (MoveZeroes.fillZerosAux nums.size a1 w)[k]! = a1[k]!) ∧ (∀ k, w ≤ k → k < nums.size → (MoveZeroes.fillZerosAux nums.size a1 w)[k]! = 0) ∧ (∀ k, nums.size ≤ k → k < a1.size → (MoveZeroes.fillZerosAux nums.size a1 w)[k]! = a1[k]!) := by
        apply MoveZeroes.fillZerosAux_spec;
        · have h_foldl_step_w : (nums.foldl MoveZeroes.step (0, nums)).1 = (nums.toList.filter (· ≠ 0)).length := by
            convert MoveZeroes.foldl_step_w nums.toList 0 nums using 1;
            · conv => rw [ ← Array.foldl_toList ] ;
            · norm_num;
          grind;
        · have := MoveZeroes.foldl_step_size nums.toList 0 nums; aesop;
      by_cases hk'' : k < w <;> by_cases hj'' : j < w <;> simp_all +decide;
      · have h_foldl_step_content : ∀ k (hk : k < (nums.toList.filter (· ≠ 0)).length), a1[k]! = (nums.toList.filter (· ≠ 0))[k] := by
          convert MoveZeroes.foldl_step_content nums.toList 0 nums _ using 1;
          · grind;
          · grind;
        have h_foldl_step_w : w = (nums.toList.filter (· ≠ 0)).length := by
          have := MoveZeroes.foldl_step_w nums.toList 0 nums; aesop;
        grind;
      · convert h_fillZerosAux.2.2.1 j hj'' _ using 1;
        · exact?;
        · have := MoveZeroes.foldl_step_size nums.toList 0 nums; aesop;
      · grind;
      · by_cases hj''' : j < nums.size <;> simp_all +decide [ Array.get! ];
        · grind +ring;
        · have h_size : a1.size = nums.size := by
            have h_size : ∀ (l : List Int) (w : Nat) (a : Array Int), (l.foldl MoveZeroes.step (w, a)).2.size = a.size := by
              exact?;
            specialize h_size nums.toList 0 nums ; aesop;
          linarith;
    · -- Define the function `f` that maps the indices of the non-zero elements in the input array to their positions in the output array.
      obtain ⟨f, hf⟩ : ∃ f : Nat → Nat,
        (∀ i, isNonZeroIndex nums i → f i < (nums.foldl MoveZeroes.step (0, nums)).1 ∧ (nums.foldl MoveZeroes.step (0, nums)).2[f i]! = nums[i]!) ∧
        (∀ i j, i < j → isNonZeroIndex nums i → isNonZeroIndex nums j → f i < f j) ∧
        (∀ p, p < (nums.foldl MoveZeroes.step (0, nums)).1 → (nums.foldl MoveZeroes.step (0, nums)).2[p]! ≠ 0 → ∃ i, isNonZeroIndex nums i ∧ f i = p) := by
          -- Define the function `f` that maps each non-zero index `i` in `nums` to its position in the output array using the `foldl` step.
          use fun i => (List.take i (nums.toList)).countP (fun x => x ≠ 0);
          refine' ⟨ _, _, _ ⟩;
          · intro i hi;
            -- By definition of `MoveZeroes.step`, the count of non-zero elements up to index `i` is equal to the position of the `i`-th non-zero element in the output array.
            have h_count : (List.take i (nums.toList)).countP (fun x => x ≠ 0) < (nums.foldl MoveZeroes.step (0, nums)).1 := by
              have h_count : (List.take i (nums.toList)).countP (fun x => x ≠ 0) < (List.filter (fun x => x ≠ 0) (nums.toList)).length := by
                have h_count : List.countP (fun x => x ≠ 0) (List.take i nums.toList) < List.countP (fun x => x ≠ 0) (List.take (i + 1) nums.toList) := by
                  rw [ List.take_succ ];
                  cases hi ; aesop;
                refine lt_of_lt_of_le h_count ?_;
                rw [ ← List.take_append_drop ( i + 1 ) nums.toList, List.filter_append ];
                simp +arith +decide [ List.countP_eq_length_filter ];
              convert h_count using 1;
              convert MoveZeroes.foldl_step_w nums.toList 0 nums using 1;
              · conv => rw [ ← Array.foldl_toList ] ;
              · norm_num;
            have h_content : ∀ k (hk : k < (List.filter (· ≠ 0) (nums.toList)).length), (nums.foldl MoveZeroes.step (0, nums)).2[(List.filter (· ≠ 0) (nums.toList)).take k |>.length]! = (List.filter (· ≠ 0) (nums.toList))[k]! := by
              convert MoveZeroes.foldl_step_content ( nums.toList ) 0 nums _ using 1;
              · grind;
              · grind;
            have h_filter : (List.filter (· ≠ 0) (nums.toList))[List.countP (fun x => x ≠ 0) (List.take i (nums.toList))]! = nums[i]! := by
              have h_filter : ∀ (l : List ℤ) (i : ℕ), i < l.length → l[i]! ≠ 0 → (List.filter (fun x => x ≠ 0) l)[List.countP (fun x => x ≠ 0) (List.take i l)]! = l[i]! := by
                intros l i hi h_nonzero
                induction' l with hd tl ih generalizing i;
                · contradiction;
                · rcases i with ( _ | i ) <;> simp_all +decide [ List.countP_cons ];
                  split_ifs <;> simp_all +decide [ List.filter_cons ];
              cases hi ; aesop;
            have h_filter_length : (List.filter (· ≠ 0) (nums.toList)).length ≥ List.countP (fun x => x ≠ 0) (List.take i (nums.toList)) + 1 := by
              have h_filter_length : (List.filter (· ≠ 0) (nums.toList)).length = (nums.foldl MoveZeroes.step (0, nums)).1 := by
                have h_filter_length : ∀ (l : List ℤ) (w : Nat) (a : Array ℤ), (List.foldl MoveZeroes.step (w, a) l).1 = w + (List.filter (· ≠ 0) l).length := by
                  exact?;
                convert h_filter_length nums.toList 0 nums |> Eq.symm using 1;
                · norm_num;
                · conv => rw [ ← Array.foldl_toList ] ;
              linarith;
            grind;
          · intro i j hij hi hj;
            have h_count : List.countP (fun x => x ≠ 0) (List.take j nums.toList) = List.countP (fun x => x ≠ 0) (List.take i nums.toList) + List.countP (fun x => x ≠ 0) (List.drop i (List.take j nums.toList)) := by
              rw [ ← List.take_append_drop i ( List.take j nums.toList ), List.countP_append ];
              grind;
            have h_count_pos : List.countP (fun x => x ≠ 0) (List.drop i (List.take j nums.toList)) ≥ 1 := by
              have h_count_pos : nums[i]! ∈ List.drop i (List.take j nums.toList) := by
                rw [ List.mem_iff_get ];
                use ⟨ 0, by
                  simp +arith +decide [ hij.le ];
                  exact ⟨ hij, hi.1 ⟩ ⟩
                generalize_proofs at *;
                grind;
              have h_count_pos : ∀ {l : List ℤ}, nums[i]! ∈ l → nums[i]! ≠ 0 → List.countP (fun x => x ≠ 0) l ≥ 1 := by
                intros l hl hl_nonzero; induction l <;> aesop;
              exact h_count_pos ‹_› ( by cases hi; aesop );
            grind;
          · intro p hp hp';
            -- By definition of `MoveZeroes.step`, the number of non-zero elements up to index `p` in the output array is exactly `p`.
            have h_count : ∀ p < (nums.foldl MoveZeroes.step (0, nums)).1, (nums.foldl MoveZeroes.step (0, nums)).2[p]! = (nums.toList.filter (· ≠ 0))[p]! := by
              intro p hp;
              have := MoveZeroes.foldl_step_content nums.toList 0 nums (by
              grind) p (by
              convert hp using 1;
              convert MoveZeroes.foldl_step_w nums.toList 0 nums |> Eq.symm;
              · norm_num;
              · exact?);
              all_goals generalize_proofs at *;
              grind;
            -- By definition of `MoveZeroes.step`, the number of non-zero elements up to index `p` in the output array is exactly `p`. Therefore, we can find such an `i` in the input array.
            obtain ⟨i, hi⟩ : ∃ i, i < nums.size ∧ (nums.toList.filter (· ≠ 0))[p]! = nums[i]! ∧ List.countP (fun x => x ≠ 0) (List.take i nums.toList) = p := by
              have h_count : ∀ {l : List ℤ} {p : ℕ}, p < List.length (List.filter (fun x => x ≠ 0) l) → ∃ i, i < List.length l ∧ (List.filter (fun x => x ≠ 0) l)[p]! = l[i]! ∧ List.countP (fun x => x ≠ 0) (List.take i l) = p := by
                intros l p hp;
                induction' l with x l ih generalizing p;
                · contradiction;
                · by_cases hx : x = 0 <;> simp_all +decide [ List.filter_cons ];
                  · obtain ⟨ i, hi, hi', hi'' ⟩ := ih hp; use i + 1; aesop;
                  · rcases p with ( _ | p ) <;> simp_all +decide [ List.filter_cons ];
                    · exact ⟨ 0, Nat.zero_lt_succ _, rfl, by simp +decide ⟩;
                    · obtain ⟨ i, hi, hi', hi'' ⟩ := ih hp; use i + 1; aesop;
              convert h_count _;
              · cases nums ; aesop;
              · convert hp using 1;
                convert MoveZeroes.foldl_step_w nums.toList 0 nums using 1;
                · rw [ MoveZeroes.foldl_step_w ];
                  norm_num;
                · convert MoveZeroes.foldl_step_w nums.toList 0 nums using 1;
                  conv => rw [ ← Array.foldl_toList ] ;
            unfold isNonZeroIndex; aesop;
      use f;
      rw [ MoveZeroes.implementation_eq ];
      have := MoveZeroes.fillZerosAux_spec nums.size (Array.foldl MoveZeroes.step (0, nums) nums).2 (Array.foldl MoveZeroes.step (0, nums) nums).1;
      have h_size : (Array.foldl MoveZeroes.step (0, nums) nums).1 ≤ nums.size := by
        have h_size : (Array.foldl MoveZeroes.step (0, nums) nums).1 = (nums.toList.filter (· ≠ 0)).length := by
          convert MoveZeroes.foldl_step_w nums.toList 0 nums using 1;
          · conv => rw [ ← Array.foldl_toList ] ;
          · norm_num;
        exact h_size.symm ▸ le_trans ( List.length_filter_le _ _ ) ( by simpa );
      have h_size : (Array.foldl MoveZeroes.step (0, nums) nums).2.size = nums.size := by
        convert MoveZeroes.foldl_step_size nums.toList 0 nums using 1;
        conv => rw [ ← Array.foldl_toList ] ;
      grind

end Proof