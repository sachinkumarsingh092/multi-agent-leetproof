/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: ba3ffb4d-8507-4db0-930d-e7bf8b62df02

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (xs : List Int) : VerinaSpec.mostFrequent_precond xs ↔ LLMSpec.precondition xs

- theorem postcondition_equiv (xs : List Int) (result : Int) : LLMSpec.precondition xs →
  (VerinaSpec.mostFrequent_postcond xs result ↔ LLMSpec.postcondition xs result)

At Harmonic, we use a modified version of the `generalize_proofs` tactic.
For compatibility, we include this tactic at the start of the file.
If you add the comment "-- Harmonic `generalize_proofs` tactic" to your file, we will not do this.
-/

import Mathlib.Tactic

import Std.Data.HashMap


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

open Std

def mostFrequent_precond (xs : List Int) : Prop :=
  xs ≠ []

def countMap (xs : List Int) : HashMap Int Nat :=
  let step := fun m x =>
    let current := m.getD x 0
    m.insert x (current + 1)
  let init := (HashMap.empty : HashMap Int Nat)
  xs.foldl step init

def getMaxFrequency (m : HashMap Int Nat) : Nat :=
  let step := fun acc (_k, v) =>
    if v > acc then v else acc
  let init := 0
  m.toList.foldl step init

def getCandidates (m : HashMap Int Nat) (maxFreq : Nat) : List Int :=
  let isTarget := fun (_k, v) => v = maxFreq
  let extract := fun (k, _) => k
  m.toList.filter isTarget |>.map extract

def getFirstWithFreq (xs : List Int) (candidates : List Int) : Int :=
  match xs.find? (fun x => candidates.contains x) with
  | some x => x
  | none => 0

def mostFrequent_postcond (xs : List Int) (result: Int) : Prop :=
  let count := fun x => xs.countP (fun y => y = x)
  result ∈ xs ∧
  xs.all (fun x => count x ≤ count result) ∧
  ((xs.filter (fun x => count x = count result)).head? = some result)

end VerinaSpec

namespace LLMSpec

-- Helper: first index of `x` in `xs` if present; otherwise `xs.length`.
-- In the postcondition we only compare first indices for values known to be in `xs`.
def firstIndex (xs : List Int) (x : Int) : Nat :=
  (xs.findIdx? (fun y => y = x)).getD xs.length

-- Precondition: input list is non-empty.
def precondition (xs : List Int) : Prop :=
  xs ≠ []

-- Postcondition: `result` is a most frequent element, and among ties it occurs first.
def postcondition (xs : List Int) (result : Int) : Prop :=
  result ∈ xs ∧
  (∀ (y : Int), y ∈ xs → xs.count y ≤ xs.count result) ∧
  (∀ (y : Int), y ∈ xs → xs.count y = xs.count result → firstIndex xs result ≤ firstIndex xs y)

end LLMSpec

section Proof

theorem precondition_equiv (xs : List Int) : VerinaSpec.mostFrequent_precond xs ↔ LLMSpec.precondition xs := by
  -- The preconditions are equivalent because they both check if the list is non-empty.
  simp [VerinaSpec.mostFrequent_precond, LLMSpec.precondition]

theorem postcondition_equiv (xs : List Int) (result : Int) : LLMSpec.precondition xs →
  (VerinaSpec.mostFrequent_postcond xs result ↔ LLMSpec.postcondition xs result) := by
  -- To prove the equivalence of the postconditions, we need to show that the conditions in VerinaSpec's mostFrequent_postcond are equivalent to those in LLMSpec's postcondition.
  intros h_pre
  apply Iff.intro;
  · intro h_post
    obtain ⟨h_mem, h_count, h_first⟩ := h_post
    simp [LLMSpec.postcondition, h_mem, h_count, h_first];
    refine' ⟨ _, _ ⟩ <;> simp_all +decide [ List.count ];
    · exact?;
    · intros y hy h_eq_count
      have h_find : List.find? (fun x => List.countP (fun y => y == x) xs = List.countP (fun y => y == result) xs) xs = some result := by
        grind +ring
      generalize_proofs at *; (
      -- Since `find?` returns the first occurrence of the element that satisfies the predicate, and `result` is the first such element, its first index is less than or equal to the first index of any other element that satisfies the predicate.
      have h_first_index : ∀ {l : List ℤ} {p : ℤ → Bool}, List.find? p l = some result → ∀ y ∈ l, p y → LLMSpec.firstIndex l result ≤ LLMSpec.firstIndex l y := by
        intros l p hp y hy hp_y; induction l <;> simp_all +decide [ LLMSpec.firstIndex ] ;
        cases hp <;> simp_all +decide [ List.findIdx?_cons ] ; aesop;
      generalize_proofs at *; (
      exact h_first_index h_find y hy ( by simpa using h_eq_count )));
  · intro h_post
    obtain ⟨h_mem, h_count, h_first⟩ := h_post
    constructor;
    · assumption;
    · -- Since result is the first element in xs with the maximum count, when we filter the list to get elements with the same count as result, the head of this filtered list should be result.
      have h_head : List.head? (List.filter (fun x => List.count x xs = List.count result xs) xs) = some result := by
        have h_head : ∀ {l : List ℤ}, result ∈ l → (∀ y ∈ l, List.count y xs = List.count result xs → LLMSpec.firstIndex l result ≤ LLMSpec.firstIndex l y) → List.head? (List.filter (fun x => List.count x xs = List.count result xs) l) = some result := by
          intros l hl_mem hl_first; induction' l with hd tl ih <;> simp_all +decide [ LLMSpec.firstIndex ] ;
          by_cases h : hd = result <;> simp_all +decide [ List.findIdx?_cons ];
          apply ih;
          · tauto;
          · intro y hy hy'; specialize hl_first; have := hl_first.2 y hy hy'; split_ifs at this <;> simp_all +decide ;
        exact h_head h_mem h_first;
      aesop

end Proof