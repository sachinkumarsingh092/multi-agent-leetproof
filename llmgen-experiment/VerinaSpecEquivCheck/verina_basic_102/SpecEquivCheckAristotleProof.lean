/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: a2be2dbe-501e-4760-8f71-c694cb053d5a

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (nums : Array Int) (target : Int) : VerinaSpec.twoSum_precond nums target ↔ LLMSpec.precondition nums target

- theorem postcondition_equiv (nums : Array Int) (target : Int) (result : (Nat × Nat)) : LLMSpec.precondition nums target →
  (VerinaSpec.twoSum_postcond nums target result ↔ LLMSpec.postcondition nums target result)

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

def twoSum_precond (nums : Array Int) (target : Int) : Prop :=
  nums.size > 1 ∧ ¬ List.Pairwise (fun a b => a + b ≠ target) nums.toList

def twoSum_postcond (nums : Array Int) (target : Int) (result: (Nat × Nat)) :=
  let (i, j) := result
  i < j ∧ j < nums.size ∧ nums[i]! + nums[j]! = target ∧
  (nums.toList.take i).zipIdx.all (fun ⟨a, i'⟩ =>
    (nums.toList.drop (i' + 1)).all (fun b => a + b ≠ target)) ∧
  ((nums.toList.drop (i + 1)).take (j - i - 1)).all (fun b => nums[i]! + b ≠ target)

end VerinaSpec

namespace LLMSpec

-- A computable/decidable predicate describing when (i,j) is a valid two-sum witness.
-- We keep it purely in terms of Array operations (no conversions).
def isTwoSumPair (nums : Array Int) (target : Int) (i : Nat) (j : Nat) : Prop :=
  i < j ∧ j < nums.size ∧ nums[i]! + nums[j]! = target

-- Lexicographic minimality on Nat × Nat, specialized to the two-sum predicate.
-- This states that (i,j) is no larger (lexicographically) than any other valid pair.
def isLexMinTwoSumPair (nums : Array Int) (target : Int) (i : Nat) (j : Nat) : Prop :=
  isTwoSumPair nums target i j ∧
  ∀ (i' : Nat) (j' : Nat),
    isTwoSumPair nums target i' j' →
      (i < i') ∨ (i = i' ∧ j ≤ j')

-- Preconditions
-- 1) at least two elements
-- 2) existence of at least one valid pair

def precondition (nums : Array Int) (target : Int) : Prop :=
  nums.size ≥ 2 ∧
  ∃ (i : Nat) (j : Nat), isTwoSumPair nums target i j

-- Postconditions
-- result must be a valid two-sum pair and lexicographically minimal among all valid pairs.
def postcondition (nums : Array Int) (target : Int) (result : (Nat × Nat)) : Prop :=
  isLexMinTwoSumPair nums target result.1 result.2

end LLMSpec

section Proof

theorem precondition_equiv (nums : Array Int) (target : Int) : VerinaSpec.twoSum_precond nums target ↔ LLMSpec.precondition nums target := by
  constructor;
  · -- If the pairwise condition is false, then there must exist some i and j such that nums[i]! + nums[j]! = target.
    intro h
    obtain ⟨i, j, hij, h_eq⟩ : ∃ i j, i < j ∧ j < nums.size ∧ nums[i]! + nums[j]! = target := by
      -- By definition of `List.Pairwise`, if the list is not pairwise such that the sum of any two elements is not equal to the target, then there must exist indices i and j such that i < j and the sum of the elements at those indices is equal to the target.
      have h_pairwise : ¬List.Pairwise (fun a b => a + b ≠ target) nums.toList → ∃ i j : ℕ, i < j ∧ j < nums.size ∧ nums[i]! + nums[j]! = target := by
        rw [ List.pairwise_iff_get ];
        aesop;
      exact h_pairwise h.2;
    exact ⟨ by linarith, i, j, hij, h_eq.1, h_eq.2 ⟩;
  · -- If there exists a valid pair (i, j) in the LLMSpec.precondition, then the list cannot be pairwise distinct.
    intro h
    obtain ⟨i, j, hij, hsum⟩ := h.right
    have h_not_pairwise : ¬List.Pairwise (fun a b => a + b ≠ target) nums.toList := by
      rw [ List.pairwise_iff_get ];
      simp +zetaDelta at *;
      -- Since $i < j$ and $j < \text{nums.size}$, we can use $i$ and $j$ as the indices in the Fin type.
      use ⟨i, by linarith⟩, ⟨j, by linarith⟩;
      grind;
    exact ⟨ by linarith, h_not_pairwise ⟩

theorem postcondition_equiv (nums : Array Int) (target : Int) (result : (Nat × Nat)) : LLMSpec.precondition nums target →
  (VerinaSpec.twoSum_postcond nums target result ↔ LLMSpec.postcondition nums target result) := by
  intro h_pre
  unfold LLMSpec.postcondition VerinaSpec.twoSum_postcond;
  constructor <;> intro h <;> unfold LLMSpec.isLexMinTwoSumPair at * <;> simp_all +decide [ LLMSpec.isTwoSumPair ];
  · refine' ⟨ _, _ ⟩;
    · grind;
    · -- If $i' < \text{result.1}$, then we are done.
      intros i' j' hij' hj' hsum
      by_cases h_cases : i' < result.1;
      · have h_zip : (nums[i']!, i') ∈ (List.take result.1 nums.toList).zipIdx := by
          grind;
        have h_drop : nums[j'] ∈ List.drop (i' + 1) nums.toList := by
          rw [ List.mem_iff_get ];
          use ⟨ j' - ( i' + 1 ), by
            grind ⟩
          generalize_proofs at *;
          simp +decide [ List.get ];
          grind;
        exact False.elim <| h.2.2.2.1 _ _ h_zip _ h_drop hsum;
      · simp_all +decide [ List.mem_iff_get ];
        contrapose! hsum;
        convert h.2.2.2.2 ⟨ j' - ( result.1 + 1 ), _ ⟩ using 1;
        grind;
        grind;
  · refine' ⟨ _, _, _ ⟩;
    · grind;
    · intro a b hab x hx; contrapose! h; simp_all +decide [ List.mem_iff_get ] ;
      obtain ⟨ n, hn ⟩ := hab; obtain ⟨ m, hm ⟩ := hx; use fun _ _ _ => ⟨ n, b + 1 + m, ?_, ?_, ?_, ?_ ⟩ <;> simp_all +decide [ Fin.ext_iff ] ;
      · linarith;
      · grind +ring;
      · linarith [ Fin.is_lt n, Fin.is_lt m, show ( n : ℕ ) < result.1 from by simpa using n.2.trans_le ( by simp ) ];
      · intro h; have := n.2; have := m.2; simp_all +decide [ List.length_zipIdx ] ;
    · intro x hx; contrapose! h; simp_all +decide [ List.mem_iff_get ] ;
      obtain ⟨ n, hn ⟩ := hx; use fun h₁ h₂ h₃ => ⟨ result.1, result.1 + 1 + n, by linarith [ Fin.is_lt n ], ⟨ by
        grind +ring, by
        grind +ring ⟩, by linarith [ Fin.is_lt n ], by
        grind ⟩ ;

end Proof