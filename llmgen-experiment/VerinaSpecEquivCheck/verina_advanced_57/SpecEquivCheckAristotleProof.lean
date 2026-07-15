/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: a42dab8e-72ba-434c-8359-ea6ade87638a

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (nums1 : List Int) (nums2 : List Int) : VerinaSpec.nextGreaterElement_precond nums1 nums2 ↔ LLMSpec.precondition nums1 nums2

The following was negated by Aristotle:

- theorem postcondition_equiv (nums1 : List Int) (nums2 : List Int) (result : List Int) : LLMSpec.precondition nums1 nums2 →
  (VerinaSpec.nextGreaterElement_postcond nums1 nums2 result ↔ LLMSpec.postcondition nums1 nums2 result)

Here is the code for the `negate_state` tactic, used within these negations:

```lean
import Mathlib
open Lean Meta Elab Tactic in
elab "revert_all" : tactic => do
  let goals ← getGoals
  let mut newGoals : List MVarId := []
  for mvarId in goals do
    newGoals := newGoals.append [(← mvarId.revertAll)]
  setGoals newGoals

open Lean.Elab.Tactic in
macro "negate_state" : tactic => `(tactic|
  (
    guard_goal_nums 1
    revert_all
    refine @(((by admit) : ∀ {p : Prop}, ¬p → p) ?_)
    try (push_neg; guard_goal_nums 1)
  )
)
```



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

namespace VerinaSpec

def nextGreaterElement_precond (nums1 : List Int) (nums2 : List Int) : Prop :=
  List.Nodup nums1 ∧
  List.Nodup nums2 ∧
  nums1.all (fun x => x ∈ nums2)

def nextGreaterElement_postcond (nums1 : List Int) (nums2 : List Int) (result: List Int) : Prop :=
  result.length = nums1.length ∧
  (List.range nums1.length |>.all (fun i =>
    let val := nums1[i]!
    let resultVal := result[i]!
    let j := nums2.findIdx? (fun x => x == val)
    match j with
    | none => false
    | some idx =>
      let nextGreater := (List.range (nums2.length - idx - 1)).find? (fun k =>
        let pos := idx + k + 1
        nums2[pos]! > val
      )
      match nextGreater with
      | none => resultVal = -1
      | some offset => resultVal = nums2[idx + offset + 1]!
  )) ∧
  (result.all (fun val =>
    val = -1 ∨ val ∈ nums2
  ))

end VerinaSpec

namespace LLMSpec

-- Helper predicate: x occurs at index i in list l.
-- We use Nat indices and `l[i]!` for safe indexing under the bound proof.
def At (l : List Int) (i : Nat) (x : Int) : Prop :=
  i < l.length ∧ l[i]! = x

-- Helper predicate: y is the next greater element of x in nums2.
-- This is defined via positions ix and iy in nums2:
--   * x is at ix, y is at iy, and ix < iy
--   * y is strictly greater than x
--   * among all elements to the right of ix that are > x, iy is the least index
--     (i.e., there is no earlier position between ix and iy with value > x).
def IsNextGreater (nums2 : List Int) (x : Int) (y : Int) : Prop :=
  ∃ (ix : Nat) (iy : Nat),
    At nums2 ix x ∧
    At nums2 iy y ∧
    ix < iy ∧
    x < y ∧
    (∀ (j : Nat), j < nums2.length → ix < j → nums2[j]! > x → iy ≤ j)

-- Helper predicate: x has no greater element to its right in nums2.
def HasNoGreaterToRight (nums2 : List Int) (x : Int) : Prop :=
  ∃ (ix : Nat),
    At nums2 ix x ∧
    (∀ (j : Nat), j < nums2.length → ix < j → nums2[j]! ≤ x)

-- Preconditions:
-- 1) nums1 and nums2 contain no duplicates
-- 2) every element of nums1 occurs in nums2

def precondition (nums1 : List Int) (nums2 : List Int) : Prop :=
  nums1.Nodup ∧
  nums2.Nodup ∧
  (∀ (x : Int), x ∈ nums1 → x ∈ nums2)

-- Postconditions:
-- 1) result has the same length as nums1
-- 2) for each i, result[i] is either -1 (and there is no greater element to the right in nums2),
--    or a value y that is the first greater element to the right.

def postcondition (nums1 : List Int) (nums2 : List Int) (result : List Int) : Prop :=
  result.length = nums1.length ∧
  (∀ (i : Nat), i < nums1.length →
    let x : Int := nums1[i]!
    (result[i]! = (-1) ∧ HasNoGreaterToRight nums2 x) ∨
    (result[i]! ≠ (-1) ∧ IsNextGreater nums2 x (result[i]!)))

end LLMSpec

section Proof

theorem precondition_equiv (nums1 : List Int) (nums2 : List Int) : VerinaSpec.nextGreaterElement_precond nums1 nums2 ↔ LLMSpec.precondition nums1 nums2 := by
  -- The preconditions are equivalent because they both state that nums1 and nums2 have no duplicates and every element of nums1 is in nums2.
  simp [VerinaSpec.nextGreaterElement_precond, LLMSpec.precondition]

/- Aristotle found this block to be false. Here is a proof of the negation:

noncomputable section AristotleLemmas

/-
Helper lemma: `findIdx?` returns `some i` if and only if `x` is at index `i` in `nums`, assuming `nums` has no duplicates.
-/
open VerinaSpec LLMSpec

lemma findIdx_eq_some_iff_at {nums : List Int} {x : Int} {i : Nat} (h_nodup : nums.Nodup) :
  nums.findIdx? (fun y => y == x) = some i ↔ At nums i x := by
    constructor <;> intro h <;> induction' nums with hd tl ih generalizing i <;> simp_all +decide [ List.findIdx?_cons ];
    · split_ifs at h <;> simp_all +decide [ LLMSpec.At ];
      · aesop;
      · grind +ring;
    · cases h ; aesop;
    · rcases i with ( _ | i ) <;> simp_all +decide [ LLMSpec.At ];
      grind +ring

/-
Helper lemma: `find?` returns `some offset` if and only if `nums[idx + offset + 1]` is the next greater element of `val` in `nums`.
-/
open VerinaSpec LLMSpec

lemma find_next_greater_some_iff {nums : List Int} {val : Int} {idx : Nat} {offset : Nat}
  (h_nodup : nums.Nodup) (h_at : At nums idx val) :
  (List.range (nums.length - idx - 1)).find? (fun k => nums[idx + k + 1]! > val) = some offset ↔
  (idx + offset + 1 < nums.length ∧ IsNextGreater nums val nums[idx + offset + 1]!) := by
    constructor;
    · intro h;
      have h_find : offset < nums.length - idx - 1 := by
        exact List.mem_range.mp ( List.mem_of_find?_eq_some h );
      refine' ⟨ by omega, _ ⟩;
      refine' ⟨ idx, idx + offset + 1, h_at, _, _, _, _ ⟩ <;> simp_all +decide [ LLMSpec.At ];
      · omega;
      · grind;
      · intro j hj₁ hj₂ hj₃; contrapose! hj₃;
        convert h.2 ( j - idx - 1 ) _ using 1 <;> norm_num [ Nat.sub_sub ];
        · grind;
        · omega;
    · intro h
      obtain ⟨h_lt, h_next⟩ := h
      have h_find : List.find? (fun k => (nums[idx + k + 1]! > val)) (List.range (nums.length - idx - 1)) = some offset := by
        obtain ⟨ ix, iy, h_at, h_at', h_lt', h_gt, h_least ⟩ := h_next;
        have h_find : ∀ k < offset, ¬(nums[idx + k + 1]! > val) := by
          intros k hk_lt hk_gt
          have h_contra : iy ≤ idx + k + 1 := by
            apply h_least; exact (by
            linarith); exact (by
            have h_contra : ix = idx := by
              have h_unique : ∀ i j : ℕ, i < nums.length → j < nums.length → nums[i]! = nums[j]! → i = j := by
                intros i j hi hj h_eq; exact (by
                have := List.nodup_iff_injective_get.mp h_nodup; have := @this ⟨ i, hi ⟩ ⟨ j, hj ⟩ ; aesop;);
              generalize_proofs at *; (
              exact h_unique _ _ h_at.1 ( by linarith [ ‹LLMSpec.At nums idx val›.1 ] ) ( by linarith [ h_at.2, ‹LLMSpec.At nums idx val›.2 ] ))
            rw [h_contra]
            linarith); exact hk_gt;
          have h_contra : nums[iy]! = nums[idx + offset + 1]! := by
            exact h_at'.2;
          have h_contra : List.Nodup nums → ∀ i j, i < j → i < nums.length → j < nums.length → nums[i]! = nums[j]! → False := by
            intros h_nodup i j hij hi hj h_eq; have := List.nodup_iff_injective_get.mp h_nodup; have := @this ⟨ i, hi ⟩ ⟨ j, hj ⟩ ; aesop;
          exact h_contra h_nodup iy ( idx + offset + 1 ) ( by linarith ) ( by linarith ) ( by linarith ) ( by linarith );
        rw [ show nums.length - idx - 1 = offset + ( nums.length - idx - 1 - offset ) by rw [ Nat.add_sub_cancel' ( by omega ) ] ] ; simp_all +decide [ List.range_add ] ;
        omega
      exact h_find

/-
Helper lemma: `find?` returns `none` if and only if there is no greater element to the right of `val` in `nums`.
-/
open VerinaSpec LLMSpec

lemma find_next_greater_none_iff {nums : List Int} {val : Int} {idx : Nat}
  (h_nodup : nums.Nodup) (h_at : At nums idx val) :
  (List.range (nums.length - idx - 1)).find? (fun k => nums[idx + k + 1]! > val) = none ↔
  HasNoGreaterToRight nums val := by
    simp +zetaDelta at *;
    constructor;
    · intro h;
      constructor;
      exact ⟨ h_at, fun j hj₁ hj₂ => by have := h ( j - idx - 1 ) ( by omega ) ; rw [ show j = idx + ( j - idx - 1 ) + 1 by omega ] ; cases hj₁' : nums[j]? <;> simp_all +decide [ add_assoc ] ⟩;
    · intro h x hx; specialize h; rcases h with ⟨ iy, hiy₁, hiy₂ ⟩ ; simp_all +decide [ LLMSpec.At ] ;
      by_cases h_cases : idx + x + 1 < iy + 1;
      · have := List.nodup_iff_injective_get.mp h_nodup ; have := @this ⟨ idx, by linarith ⟩ ⟨ iy, by linarith ⟩ ; aesop;
      · grind +ring

/-
Backward direction: if LLMSpec postcondition holds, then VerinaSpec postcondition holds. Use the helper lemmas to show that the code's logic (findIdx?, find?) matches the predicates.
-/
open VerinaSpec LLMSpec

lemma postcondition_backward (nums1 : List Int) (nums2 : List Int) (result : List Int)
  (h_pre : LLMSpec.precondition nums1 nums2)
  (h_llm : LLMSpec.postcondition nums1 nums2 result) :
  VerinaSpec.nextGreaterElement_postcond nums1 nums2 result := by
    unfold VerinaSpec.nextGreaterElement_postcond LLMSpec.precondition LLMSpec.postcondition at *;
    refine' ⟨ h_llm.1, _, _ ⟩;
    · simp +zetaDelta at *;
      intro i hi; specialize h_llm; rcases h_llm.2 i hi with h|h <;> simp_all +decide ;
      · obtain ⟨ idx, hidx ⟩ := h.2;
        -- Since there's no greater element to the right of `nums1[i]` in `nums2`, `find?` returns `none`.
        have h_find_none : List.find? (fun k => nums2[idx + k + 1]?.getD 0 > nums1[i]) (List.range (nums2.length - idx - 1)) = none := by
          grind;
        -- Since `findIdx?` returns `some idx`, we can simplify the match expression.
        have h_findIdx_some : List.findIdx? (fun x => x == nums1[i]) nums2 = some idx := by
          rw [ findIdx_eq_some_iff_at ] ; aesop;
          exact h_pre.2.1;
        simp_all +decide [ not_lt_of_gt ];
        rw [ List.find?_eq_none.mpr ] ; aesop;
      · obtain ⟨ ix, iy, hix, hiy, hxy ⟩ := h.2;
        -- By definition of `findIdx?`, we know that `findIdx? (fun x => x == nums1[i]) nums2 = some ix`.
        have h_findIdx : List.findIdx? (fun x => x == nums1[i]) nums2 = some ix := by
          apply (findIdx_eq_some_iff_at h_pre.2.1).mpr hix;
        -- By definition of `find?`, we know that `find? (fun k => nums2[ix + k + 1]! > nums1[i]) (List.range (nums2.length - ix - 1)) = some (iy - ix - 1)`.
        have h_find : List.find? (fun k => nums2[ix + k + 1]! > nums1[i]) (List.range (nums2.length - ix - 1)) = some (iy - ix - 1) := by
          apply find_next_greater_some_iff h_pre.2.1 hix |>.2;
          unfold LLMSpec.At at *; simp_all +decide [ Nat.sub_sub ] ;
          grind +ring;
        simp_all +decide [ List.find?_eq_some_iff_append ];
        rw [ show List.find? ( fun k => Decidable.decide ( nums1[i] < nums2[ix + k + 1]?.getD 0 ) ) ( List.range ( nums2.length - ix - 1 ) ) = some ( iy - ix - 1 ) from ?_ ] ; simp +decide [ hxy ];
        · convert hiy.2 using 1;
          · exact hiy.2.symm ▸ rfl;
          · convert hiy.2 using 1;
            rw [ show ix + ( iy - ix - 1 ) + 1 = iy by omega ] ; aesop;
        · rw [ List.find?_eq_some_iff_append ] ; aesop;
    · simp_all +decide [ List.all_eq_true ];
      intro x hx; rw [ List.mem_iff_get ] at hx; obtain ⟨ i, hi ⟩ := hx; by_cases hi' : i < nums1.length <;> simp_all +decide ;
      · cases h_llm.2 i hi' <;> simp_all +decide [ List.get?_eq_get ];
        rename_i h;
        obtain ⟨ ix, iy, hix, hiy, hlt, hgt, hlt' ⟩ := h.2;
        exact hiy.2.symm ▸ by simp [ List.getElem?_eq_getElem, hiy.1 ] ;
      · linarith [ Fin.is_lt i ]

/-
Disproof of the equivalence theorem by counterexample: when `-1` is present in `nums2` and is the next greater element, `VerinaSpec` sets result to `-1` (valid), but `LLMSpec` rejects it because `result[i] = -1` implies `HasNoGreaterToRight` which is false.
-/
open VerinaSpec LLMSpec

lemma postcondition_equiv_false : ¬ (∀ nums1 nums2 result, LLMSpec.precondition nums1 nums2 → (VerinaSpec.nextGreaterElement_postcond nums1 nums2 result ↔ LLMSpec.postcondition nums1 nums2 result)) := by
  push_neg;
  use [ -2 ], [ -2, -1 ], [ -1 ];
  unfold LLMSpec.precondition LLMSpec.postcondition VerinaSpec.nextGreaterElement_postcond; simp +decide ;
  unfold LLMSpec.HasNoGreaterToRight; simp +decide ;
  rintro ( _ | _ | x ) <;> simp +decide [ LLMSpec.At ]

/-
Corrected equivalence theorem. `LLMSpec.postcondition_fixed` allows `result[i] = -1` to represent a valid next greater element (if the value is `-1`), fixing the bug in the original specification.
-/
open VerinaSpec LLMSpec

def LLMSpec.postcondition_fixed (nums1 : List Int) (nums2 : List Int) (result : List Int) : Prop :=
  result.length = nums1.length ∧
  (∀ (i : Nat), i < nums1.length →
    let x : Int := nums1[i]!
    (result[i]! = (-1) ∧ HasNoGreaterToRight nums2 x) ∨
    (IsNextGreater nums2 x (result[i]!)))

theorem postcondition_equiv_fixed (nums1 : List Int) (nums2 : List Int) (result : List Int) :
  LLMSpec.precondition nums1 nums2 →
  (VerinaSpec.nextGreaterElement_postcond nums1 nums2 result ↔ LLMSpec.postcondition_fixed nums1 nums2 result) := by
    intro h_pre; constructor <;> intro h <;> unfold LLMSpec.postcondition_fixed at * <;> simp_all +decide [ LLMSpec.postcondition ] ; (
    -- By definition of VerinaSpec.nextGreaterElement_postcond, we know that for every i, the result at i is either -1 or the next greater element.
    obtain ⟨h_len, h_cond⟩ := h;
    refine' ⟨ h_len, fun i hi => _ ⟩ ; specialize h_cond ; rcases h_cond with ⟨ h₁, h₂ ⟩ ; simp_all +decide [ List.all_eq_true ] ; (
    specialize h₁ i hi ; rcases h : List.findIdx? ( fun x_1 => x_1 == nums1[i] ) nums2 with ( _ | idx ) <;> simp_all +decide ; (
    rcases h' : List.find? ( fun k => Decidable.decide ( nums1[i] < nums2[idx + k + 1]?.getD 0 ) ) ( List.range ( nums2.length - idx - 1 ) ) with ( _ | offset ) <;> simp_all +decide ; (
    refine Or.inl ⟨ idx, ?_, ?_ ⟩ <;> simp_all +decide [ LLMSpec.At ];
    · have h_findIdx : ∀ {l : List ℤ} {x : ℤ} {i : ℕ}, List.findIdx? (fun y => y == x) l = some i → i < l.length ∧ l[i]! = x := by
        intros l x i hi; induction l generalizing i <;> simp_all +decide [ List.findIdx?_cons ] ; (
        cases h : List.findIdx? ( fun y => y == x ) ‹_› <;> aesop ( simp_config := { decide := true } ) ;)
      generalize_proofs at *; (
      specialize h_findIdx h; aesop;);
    · intro j hj₁ hj₂; specialize h' ( j - idx - 1 ) ; simp_all +decide [ Nat.sub_sub ] ;
      convert h' ( by omega ) using 1 ; rw [ show idx + ( j - ( idx + 1 ) ) + 1 = j by omega ] ; aesop;);
    refine Or.inr ⟨ idx, idx + offset + 1, ?_, ?_, ?_, ?_, ?_ ⟩ <;> norm_num at * <;> try omega;
    · have h_at : idx < nums2.length ∧ nums2[idx]! = nums1[i] := by
        have h_findIdx : List.findIdx? (fun x_1 => x_1 == nums1[i]) nums2 = some idx := h
        have h_at : At nums2 idx (nums1[i]) := by
          have h_findIdx : List.findIdx? (fun x_1 => x_1 == nums1[i]) nums2 = some idx := h_findIdx
          exact (findIdx_eq_some_iff_at (by
          exact h_pre.2.1) |>.1 h_findIdx);
        exact h_at
      exact h_at;
    · exact ⟨ by omega, by cases h : nums2.get? ( idx + offset + 1 ) <;> aesop ⟩;
    · intro j hj₁ hj₂ hj₃; contrapose! hj₃; simp_all +decide [ List.getElem?_eq_none ] ;
      convert h'.2.2 ( j - idx - 1 ) _ using 1 <;> norm_num [ Nat.sub_sub ] at * <;> try omega;
      rw [ show idx + ( j - ( idx + 1 ) ) + 1 = j by omega ] ; aesop;)););
    refine' ⟨ h.1, _, _ ⟩ <;> simp_all +decide [ VerinaSpec.nextGreaterElement_postcond ];
    · intro i hi; specialize h; rcases h with ⟨ h₁, h₂ ⟩ ; specialize h₂ i hi; rcases h₂ with ( ⟨ h₂, h₃ ⟩ | h₂ ) <;> simp_all +decide [ List.get?_eq_get ] ;
      · cases' h₃ with idx hidx ; simp_all +decide [ LLMSpec.IsNextGreater ];
        -- Since `nums1[i]` is at index `idx` in `nums2`, we have `List.findIdx? (fun x => x == nums1[i]) nums2 = some idx`.
        have h_findIdx : List.findIdx? (fun x => x == nums1[i]) nums2 = some idx := by
          apply (findIdx_eq_some_iff_at h_pre.2.1).mpr hidx.1;
        rw [ h_findIdx ] ; simp +decide [ List.find?_eq_none.mpr ] ;
        cases h : List.find? ( fun k => Decidable.decide ( nums1[i] < nums2[idx + k + 1]?.getD 0 ) ) ( List.range ( nums2.length - idx - 1 ) ) <;> simp_all +decide [ List.find?_eq_none.mpr ] ;
        grind +ring;
      · obtain ⟨ ix, iy, hix, hiy, hxy ⟩ := h₂;
        -- Since `ix` is the index of `nums1[i]` in `nums2`, we have `List.findIdx? (fun x => x == nums1[i]) nums2 = some ix`.
        have h_findIdx : List.findIdx? (fun x => x == nums1[i]) nums2 = some ix := by
          apply (findIdx_eq_some_iff_at h_pre.2.1).mpr hix;
        -- Since `iy` is the index of `result[i]` in `nums2`, we have `List.find? (fun k => nums1[i] < nums2[ix + k + 1]!) (List.range (nums2.length - ix - 1)) = some (iy - ix - 1)`.
        have h_find : List.find? (fun k => nums1[i] < nums2[ix + k + 1]!) (List.range (nums2.length - ix - 1)) = some (iy - ix - 1) := by
          apply find_next_greater_some_iff (h_pre.2.1) hix |>.2;
          refine' ⟨ _, _ ⟩
          all_goals generalize_proofs at *;
          · linarith [ Nat.sub_add_cancel ( show 1 ≤ iy - ix from Nat.sub_pos_of_lt hxy.1 ), Nat.sub_add_cancel ( show ix ≤ iy from hxy.1.le ), hiy.1 ];
          · refine' ⟨ ix, iy, hix, _, _, _, _ ⟩ <;> try omega
            all_goals generalize_proofs at *; simp_all +decide [ LLMSpec.At ] ;
            · rw [ show ix + ( iy - ix - 1 ) + 1 = iy by omega ] ; aesop;
            · grind +ring;
        rw [ h_findIdx ] ; simp +decide [ h_find ] ;
        rw [ show List.find? ( fun k => Decidable.decide ( nums1[i] < nums2[ix + k + 1]?.getD 0 ) ) ( List.range ( nums2.length - ix - 1 ) ) = some ( iy - ix - 1 ) from ?_ ] ; simp +decide [ hxy ];
        · rw [ show ix + ( iy - ix - 1 ) + 1 = iy by omega ] ; cases hiy ; aesop;
        · cases h : nums2.get? ( ix + ‹_› + 1 ) <;> aesop;
    · intro x hx; rw [ List.mem_iff_get ] at hx; obtain ⟨ i, hi ⟩ := hx; by_cases hi' : i < nums1.length <;> simp_all +decide ;
      · cases h.2 i hi' <;> simp_all +decide [ List.getElem?_eq_getElem ] ; (
        -- Since x is the next greater element of nums1[i] in nums2, and nums2 has no duplicates, x must be an element of nums2.
        obtain ⟨ix, iy, hix, hiy, hlt, hgt, hmin⟩ := ‹LLMSpec.IsNextGreater nums2 nums1[(↑i : ℕ)] x›;
        have hx_in_nums2 : x ∈ nums2 := by
          exact hiy.2 ▸ by simp +decide [ List.getElem?_eq_getElem, hiy.1 ] ;;
        exact Or.inr hx_in_nums2;);
      · linarith [ Fin.is_lt i ]

end AristotleLemmas

theorem postcondition_equiv (nums1 : List Int) (nums2 : List Int) (result : List Int) : LLMSpec.precondition nums1 nums2 →
  (VerinaSpec.nextGreaterElement_postcond nums1 nums2 result ↔ LLMSpec.postcondition nums1 nums2 result) := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  by_contra! h_contra;
  -- Apply the equivalence theorem to the counterexample to derive a contradiction.
  apply postcondition_equiv_false;
  grind +ring

-/
theorem postcondition_equiv (nums1 : List Int) (nums2 : List Int) (result : List Int) : LLMSpec.precondition nums1 nums2 →
  (VerinaSpec.nextGreaterElement_postcond nums1 nums2 result ↔ LLMSpec.postcondition nums1 nums2 result) := by
  sorry

end Proof