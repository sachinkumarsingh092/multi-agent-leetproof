/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 5a55e53b-7ebf-4a71-96cd-f7c6b5efc2ed

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem goal_0 (nums1 : Array ℤ) (nums2 : Array ℤ) (require_1 : (∀ (i : ℕ), i + OfNat.ofNat 1 < nums1.size → nums1[i]! ≤ nums1[i + OfNat.ofNat 1]!) ∧ ∀ (i : ℕ), i + OfNat.ofNat 1 < nums2.size → nums2[i]! ≤ nums2[i + OfNat.ofNat 1]!) (i : ℕ) (j : ℕ) (res : Array ℤ) (invariant_inv_sizes : res.size = nums1.size + nums2.size) (invariant_inv_bounds_i : i ≤ nums1.size) (invariant_inv_bounds_j : j ≤ nums2.size) (invariant_inv_bounds_k : i + j ≤ res.size) (if_pos : i + j < res.size) (if_pos_1 : nums1.size ≤ i) (invariant_inv_counts : ∀ (v : ℤ), List.count v (List.take (i + j) res.toList) = List.count v (List.take i nums1.toList) + List.count v (List.take j nums2.toList)) (invariant_inv_sorted_prefix : ∀ (i_1 : ℕ), i_1 + OfNat.ofNat 1 < i + j → i_1 + OfNat.ofNat 1 < res.size → (res.extract (OfNat.ofNat 0) (i + j))[i_1]! ≤ (res.extract (OfNat.ofNat 0) (i + j))[i_1 + OfNat.ofNat 1]!) (invariant_inv_last_le_next : i = OfNat.ofNat 0 ∧ j = OfNat.ofNat 0 ∨ (i < nums1.size → res[i + j - OfNat.ofNat 1]! ≤ nums1[i]!) ∧ (j < nums2.size → res[i + j - OfNat.ofNat 1]! ≤ nums2[j]!)) : ∀ (v : ℤ), List.count v (List.take (i + j + OfNat.ofNat 1) (res.toList.set (i + j) nums2[j]!)) = List.count v (List.take i nums1.toList) + List.count v (List.take (j + OfNat.ofNat 1) nums2.toList)

- theorem goal_1 (nums1 : Array ℤ) (nums2 : Array ℤ) (require_1 : (∀ (i : ℕ), i + OfNat.ofNat 1 < nums1.size → nums1[i]! ≤ nums1[i + OfNat.ofNat 1]!) ∧ ∀ (i : ℕ), i + OfNat.ofNat 1 < nums2.size → nums2[i]! ≤ nums2[i + OfNat.ofNat 1]!) (i : ℕ) (j : ℕ) (res : Array ℤ) (invariant_inv_sizes : res.size = nums1.size + nums2.size) (invariant_inv_bounds_i : i ≤ nums1.size) (invariant_inv_bounds_j : j ≤ nums2.size) (invariant_inv_bounds_k : i + j ≤ res.size) (if_pos : i + j < res.size) (if_pos_1 : nums1.size ≤ i) (invariant_inv_counts : ∀ (v : ℤ), List.count v (List.take (i + j) res.toList) = List.count v (List.take i nums1.toList) + List.count v (List.take j nums2.toList)) (invariant_inv_sorted_prefix : ∀ (i_1 : ℕ), i_1 + OfNat.ofNat 1 < i + j → i_1 + OfNat.ofNat 1 < res.size → (res.extract (OfNat.ofNat 0) (i + j))[i_1]! ≤ (res.extract (OfNat.ofNat 0) (i + j))[i_1 + OfNat.ofNat 1]!) (invariant_inv_last_le_next : i = OfNat.ofNat 0 ∧ j = OfNat.ofNat 0 ∨ (i < nums1.size → res[i + j - OfNat.ofNat 1]! ≤ nums1[i]!) ∧ (j < nums2.size → res[i + j - OfNat.ofNat 1]! ≤ nums2[j]!)) : ∀ i_1 < i + j, i_1 + OfNat.ofNat 1 < res.size → ((res.setIfInBounds (i + j) nums2[j]!).extract (OfNat.ofNat 0) (i + j + OfNat.ofNat 1))[i_1]! ≤ ((res.setIfInBounds (i + j) nums2[j]!).extract (OfNat.ofNat 0) (i + j + OfNat.ofNat 1))[i_1 + OfNat.ofNat 1]!

- theorem goal_5 (nums1 : Array ℤ) (nums2 : Array ℤ) (require_1 : (∀ (i : ℕ), i + OfNat.ofNat 1 < nums1.size → nums1[i]! ≤ nums1[i + OfNat.ofNat 1]!) ∧ ∀ (i : ℕ), i + OfNat.ofNat 1 < nums2.size → nums2[i]! ≤ nums2[i + OfNat.ofNat 1]!) (i : ℕ) (j : ℕ) (res : Array ℤ) (invariant_inv_sizes : res.size = nums1.size + nums2.size) (invariant_inv_bounds_i : i ≤ nums1.size) (invariant_inv_bounds_j : j ≤ nums2.size) (if_pos_1 : nums1[i]! ≤ nums2[j]!) (invariant_inv_bounds_k : i + j ≤ res.size) (if_pos : i + j < res.size) (if_neg : i < nums1.size) (if_neg_1 : j < nums2.size) (invariant_inv_counts : ∀ (v : ℤ), List.count v (List.take (i + j) res.toList) = List.count v (List.take i nums1.toList) + List.count v (List.take j nums2.toList)) (invariant_inv_sorted_prefix : ∀ (i_1 : ℕ), i_1 + OfNat.ofNat 1 < i + j → i_1 + OfNat.ofNat 1 < res.size → (res.extract (OfNat.ofNat 0) (i + j))[i_1]! ≤ (res.extract (OfNat.ofNat 0) (i + j))[i_1 + OfNat.ofNat 1]!) (invariant_inv_last_le_next : i = OfNat.ofNat 0 ∧ j = OfNat.ofNat 0 ∨ (i < nums1.size → res[i + j - OfNat.ofNat 1]! ≤ nums1[i]!) ∧ (j < nums2.size → res[i + j - OfNat.ofNat 1]! ≤ nums2[j]!)) : ∀ i_1 < i + j, i_1 + OfNat.ofNat 1 < res.size → ((res.setIfInBounds (i + j) nums1[i]!).extract (OfNat.ofNat 0) (i + j + OfNat.ofNat 1))[i_1]! ≤ ((res.setIfInBounds (i + j) nums1[i]!).extract (OfNat.ofNat 0) (i + j + OfNat.ofNat 1))[i_1 + OfNat.ofNat 1]!

- theorem goal_6 (nums1 : Array ℤ) (nums2 : Array ℤ) (require_1 : (∀ (i : ℕ), i + OfNat.ofNat 1 < nums1.size → nums1[i]! ≤ nums1[i + OfNat.ofNat 1]!) ∧ ∀ (i : ℕ), i + OfNat.ofNat 1 < nums2.size → nums2[i]! ≤ nums2[i + OfNat.ofNat 1]!) (i : ℕ) (j : ℕ) (res : Array ℤ) (invariant_inv_sizes : res.size = nums1.size + nums2.size) (invariant_inv_bounds_i : i ≤ nums1.size) (invariant_inv_bounds_j : j ≤ nums2.size) (invariant_inv_bounds_k : i + j ≤ res.size) (if_pos : i + j < res.size) (if_neg : i < nums1.size) (if_neg_1 : j < nums2.size) (if_neg_2 : nums2[j]! < nums1[i]!) (invariant_inv_counts : ∀ (v : ℤ), List.count v (List.take (i + j) res.toList) = List.count v (List.take i nums1.toList) + List.count v (List.take j nums2.toList)) (invariant_inv_sorted_prefix : ∀ (i_1 : ℕ), i_1 + OfNat.ofNat 1 < i + j → i_1 + OfNat.ofNat 1 < res.size → (res.extract (OfNat.ofNat 0) (i + j))[i_1]! ≤ (res.extract (OfNat.ofNat 0) (i + j))[i_1 + OfNat.ofNat 1]!) (invariant_inv_last_le_next : i = OfNat.ofNat 0 ∧ j = OfNat.ofNat 0 ∨ (i < nums1.size → res[i + j - OfNat.ofNat 1]! ≤ nums1[i]!) ∧ (j < nums2.size → res[i + j - OfNat.ofNat 1]! ≤ nums2[j]!)) : ∀ (v : ℤ), List.count v (List.take (i + j + OfNat.ofNat 1) (res.toList.set (i + j) nums2[j]!)) = List.count v (List.take i nums1.toList) + List.count v (List.take (j + OfNat.ofNat 1) nums2.toList)

- theorem goal_7 (nums1 : Array ℤ) (nums2 : Array ℤ) (require_1 : (∀ (i : ℕ), i + OfNat.ofNat 1 < nums1.size → nums1[i]! ≤ nums1[i + OfNat.ofNat 1]!) ∧ ∀ (i : ℕ), i + OfNat.ofNat 1 < nums2.size → nums2[i]! ≤ nums2[i + OfNat.ofNat 1]!) (i : ℕ) (j : ℕ) (res : Array ℤ) (invariant_inv_sizes : res.size = nums1.size + nums2.size) (invariant_inv_bounds_i : i ≤ nums1.size) (invariant_inv_bounds_j : j ≤ nums2.size) (invariant_inv_bounds_k : i + j ≤ res.size) (if_pos : i + j < res.size) (if_neg : i < nums1.size) (if_neg_1 : j < nums2.size) (if_neg_2 : nums2[j]! < nums1[i]!) (invariant_inv_counts : ∀ (v : ℤ), List.count v (List.take (i + j) res.toList) = List.count v (List.take i nums1.toList) + List.count v (List.take j nums2.toList)) (invariant_inv_sorted_prefix : ∀ (i_1 : ℕ), i_1 + OfNat.ofNat 1 < i + j → i_1 + OfNat.ofNat 1 < res.size → (res.extract (OfNat.ofNat 0) (i + j))[i_1]! ≤ (res.extract (OfNat.ofNat 0) (i + j))[i_1 + OfNat.ofNat 1]!) (invariant_inv_last_le_next : i = OfNat.ofNat 0 ∧ j = OfNat.ofNat 0 ∨ (i < nums1.size → res[i + j - OfNat.ofNat 1]! ≤ nums1[i]!) ∧ (j < nums2.size → res[i + j - OfNat.ofNat 1]! ≤ nums2[j]!)) : ∀ i_1 < i + j, i_1 + OfNat.ofNat 1 < res.size → ((res.setIfInBounds (i + j) nums2[j]!).extract (OfNat.ofNat 0) (i + j + OfNat.ofNat 1))[i_1]! ≤ ((res.setIfInBounds (i + j) nums2[j]!).extract (OfNat.ofNat 0) (i + j + OfNat.ofNat 1))[i_1 + OfNat.ofNat 1]!

- theorem goal_8 (nums1 : Array ℤ) (nums2 : Array ℤ) (require_1 : (∀ (i : ℕ), i + OfNat.ofNat 1 < nums1.size → nums1[i]! ≤ nums1[i + OfNat.ofNat 1]!) ∧ ∀ (i : ℕ), i + OfNat.ofNat 1 < nums2.size → nums2[i]! ≤ nums2[i + OfNat.ofNat 1]!) (i_1 : ℕ) (i_2 : ℕ) (res_1 : Array ℤ) (invariant_inv_bounds_i : i_1 ≤ nums1.size) (invariant_inv_bounds_j : i_2 ≤ nums2.size) (invariant_inv_sizes : res_1.size = nums1.size + nums2.size) (invariant_inv_bounds_k : i_1 + i_2 ≤ res_1.size) (invariant_inv_sorted_prefix : ∀ (i : ℕ), i + OfNat.ofNat 1 < i_1 + i_2 → i + OfNat.ofNat 1 < res_1.size → (res_1.extract (OfNat.ofNat 0) (i_1 + i_2))[i]! ≤ (res_1.extract (OfNat.ofNat 0) (i_1 + i_2))[i + OfNat.ofNat 1]!) (done_1 : res_1.size ≤ i_1 + i_2) (invariant_inv_counts : ∀ (v : ℤ), List.count v (List.take (i_1 + i_2) res_1.toList) = List.count v (List.take i_1 nums1.toList) + List.count v (List.take i_2 nums2.toList)) (invariant_inv_last_le_next : i_1 = OfNat.ofNat 0 ∧ i_2 = OfNat.ofNat 0 ∨ (i_1 < nums1.size → res_1[i_1 + i_2 - OfNat.ofNat 1]! ≤ nums1[i_1]!) ∧ (i_2 < nums2.size → res_1[i_1 + i_2 - OfNat.ofNat 1]! ≤ nums2[i_2]!)) : postcondition nums1 nums2 res_1

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

section Specs

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

theorem goal_0 (nums1 : Array ℤ) (nums2 : Array ℤ) (require_1 : (∀ (i : ℕ), i + OfNat.ofNat 1 < nums1.size → nums1[i]! ≤ nums1[i + OfNat.ofNat 1]!) ∧ ∀ (i : ℕ), i + OfNat.ofNat 1 < nums2.size → nums2[i]! ≤ nums2[i + OfNat.ofNat 1]!) (i : ℕ) (j : ℕ) (res : Array ℤ) (invariant_inv_sizes : res.size = nums1.size + nums2.size) (invariant_inv_bounds_i : i ≤ nums1.size) (invariant_inv_bounds_j : j ≤ nums2.size) (invariant_inv_bounds_k : i + j ≤ res.size) (if_pos : i + j < res.size) (if_pos_1 : nums1.size ≤ i) (invariant_inv_counts : ∀ (v : ℤ), List.count v (List.take (i + j) res.toList) = List.count v (List.take i nums1.toList) + List.count v (List.take j nums2.toList)) (invariant_inv_sorted_prefix : ∀ (i_1 : ℕ), i_1 + OfNat.ofNat 1 < i + j → i_1 + OfNat.ofNat 1 < res.size → (res.extract (OfNat.ofNat 0) (i + j))[i_1]! ≤ (res.extract (OfNat.ofNat 0) (i + j))[i_1 + OfNat.ofNat 1]!) (invariant_inv_last_le_next : i = OfNat.ofNat 0 ∧ j = OfNat.ofNat 0 ∨ (i < nums1.size → res[i + j - OfNat.ofNat 1]! ≤ nums1[i]!) ∧ (j < nums2.size → res[i + j - OfNat.ofNat 1]! ≤ nums2[j]!)) : ∀ (v : ℤ), List.count v (List.take (i + j + OfNat.ofNat 1) (res.toList.set (i + j) nums2[j]!)) = List.count v (List.take i nums1.toList) + List.count v (List.take (j + OfNat.ofNat 1) nums2.toList) := by
    cases if_pos_1.eq_or_lt <;> simp_all +decide [ List.take_succ ];
    · intro v; specialize invariant_inv_counts v; simp_all +decide [ List.take_set, List.count_cons ] ;
      rw [ List.set_eq_of_length_le ] <;> simp_all +decide [ List.length_take ] ; linarith;
    · linarith

theorem goal_1 (nums1 : Array ℤ) (nums2 : Array ℤ) (require_1 : (∀ (i : ℕ), i + OfNat.ofNat 1 < nums1.size → nums1[i]! ≤ nums1[i + OfNat.ofNat 1]!) ∧ ∀ (i : ℕ), i + OfNat.ofNat 1 < nums2.size → nums2[i]! ≤ nums2[i + OfNat.ofNat 1]!) (i : ℕ) (j : ℕ) (res : Array ℤ) (invariant_inv_sizes : res.size = nums1.size + nums2.size) (invariant_inv_bounds_i : i ≤ nums1.size) (invariant_inv_bounds_j : j ≤ nums2.size) (invariant_inv_bounds_k : i + j ≤ res.size) (if_pos : i + j < res.size) (if_pos_1 : nums1.size ≤ i) (invariant_inv_counts : ∀ (v : ℤ), List.count v (List.take (i + j) res.toList) = List.count v (List.take i nums1.toList) + List.count v (List.take j nums2.toList)) (invariant_inv_sorted_prefix : ∀ (i_1 : ℕ), i_1 + OfNat.ofNat 1 < i + j → i_1 + OfNat.ofNat 1 < res.size → (res.extract (OfNat.ofNat 0) (i + j))[i_1]! ≤ (res.extract (OfNat.ofNat 0) (i + j))[i_1 + OfNat.ofNat 1]!) (invariant_inv_last_le_next : i = OfNat.ofNat 0 ∧ j = OfNat.ofNat 0 ∨ (i < nums1.size → res[i + j - OfNat.ofNat 1]! ≤ nums1[i]!) ∧ (j < nums2.size → res[i + j - OfNat.ofNat 1]! ≤ nums2[j]!)) : ∀ i_1 < i + j, i_1 + OfNat.ofNat 1 < res.size → ((res.setIfInBounds (i + j) nums2[j]!).extract (OfNat.ofNat 0) (i + j + OfNat.ofNat 1))[i_1]! ≤ ((res.setIfInBounds (i + j) nums2[j]!).extract (OfNat.ofNat 0) (i + j + OfNat.ofNat 1))[i_1 + OfNat.ofNat 1]! := by
    intro i_1 hi_1 hi_1'; by_cases hi_1'' : i_1 + 1 = i + j <;> simp_all +decide [ Array.setIfInBounds ] ;
    · simp_all +decide [ Array.set ];
      rcases j <;> simp_all +decide [ List.take_succ ];
      · rcases i <;> simp_all +decide [ List.getElem_append ];
        grind;
      · grind +ring;
    · convert invariant_inv_sorted_prefix i_1 ( lt_of_le_of_ne ( by linarith ) hi_1'' ) hi_1' using 1;
      · simp +decide [ Array.set, Array.getElem?_eq_getElem, * ];
        grind +ring;
      · grind

theorem goal_5 (nums1 : Array ℤ) (nums2 : Array ℤ) (require_1 : (∀ (i : ℕ), i + OfNat.ofNat 1 < nums1.size → nums1[i]! ≤ nums1[i + OfNat.ofNat 1]!) ∧ ∀ (i : ℕ), i + OfNat.ofNat 1 < nums2.size → nums2[i]! ≤ nums2[i + OfNat.ofNat 1]!) (i : ℕ) (j : ℕ) (res : Array ℤ) (invariant_inv_sizes : res.size = nums1.size + nums2.size) (invariant_inv_bounds_i : i ≤ nums1.size) (invariant_inv_bounds_j : j ≤ nums2.size) (if_pos_1 : nums1[i]! ≤ nums2[j]!) (invariant_inv_bounds_k : i + j ≤ res.size) (if_pos : i + j < res.size) (if_neg : i < nums1.size) (if_neg_1 : j < nums2.size) (invariant_inv_counts : ∀ (v : ℤ), List.count v (List.take (i + j) res.toList) = List.count v (List.take i nums1.toList) + List.count v (List.take j nums2.toList)) (invariant_inv_sorted_prefix : ∀ (i_1 : ℕ), i_1 + OfNat.ofNat 1 < i + j → i_1 + OfNat.ofNat 1 < res.size → (res.extract (OfNat.ofNat 0) (i + j))[i_1]! ≤ (res.extract (OfNat.ofNat 0) (i + j))[i_1 + OfNat.ofNat 1]!) (invariant_inv_last_le_next : i = OfNat.ofNat 0 ∧ j = OfNat.ofNat 0 ∨ (i < nums1.size → res[i + j - OfNat.ofNat 1]! ≤ nums1[i]!) ∧ (j < nums2.size → res[i + j - OfNat.ofNat 1]! ≤ nums2[j]!)) : ∀ i_1 < i + j, i_1 + OfNat.ofNat 1 < res.size → ((res.setIfInBounds (i + j) nums1[i]!).extract (OfNat.ofNat 0) (i + j + OfNat.ofNat 1))[i_1]! ≤ ((res.setIfInBounds (i + j) nums1[i]!).extract (OfNat.ofNat 0) (i + j + OfNat.ofNat 1))[i_1 + OfNat.ofNat 1]! := by
    -- Since the original extract was sorted and we're just replacing the last element (where there's no element to compare with), the new extract remains sorted.
    intros i_1 hi_1 hi_1'
    by_cases hi_1'' : i_1 < i + j - 1;
    · simp_all +decide [ Array.setIfInBounds ];
      convert invariant_inv_sorted_prefix i_1 ( by
        exact Nat.lt_pred_iff.mp hi_1'' ) ( by
        exact? ) using 1
      all_goals generalize_proofs at *;
      · simp +decide [ Array.set, Array.getElem?_eq_getElem, hi_1, hi_1' ];
        simp +decide [ List.getElem?_set, List.getElem?_take, hi_1, hi_1' ];
        split_ifs <;> simp_all +decide [ Nat.lt_succ_iff ];
        · rw [ Array.getElem?_eq_getElem ] ; aesop;
        · linarith;
      · grind;
    · cases invariant_inv_last_le_next <;> simp_all +decide [ Nat.sub_add_cancel ( by linarith : 1 ≤ i + j ) ];
      cases hi_1''.eq_or_lt <;> first | linarith | simp_all +decide [ Nat.sub_add_cancel ( by linarith : 1 ≤ i + j ) ] ;
      grind

theorem goal_6 (nums1 : Array ℤ) (nums2 : Array ℤ) (require_1 : (∀ (i : ℕ), i + OfNat.ofNat 1 < nums1.size → nums1[i]! ≤ nums1[i + OfNat.ofNat 1]!) ∧ ∀ (i : ℕ), i + OfNat.ofNat 1 < nums2.size → nums2[i]! ≤ nums2[i + OfNat.ofNat 1]!) (i : ℕ) (j : ℕ) (res : Array ℤ) (invariant_inv_sizes : res.size = nums1.size + nums2.size) (invariant_inv_bounds_i : i ≤ nums1.size) (invariant_inv_bounds_j : j ≤ nums2.size) (invariant_inv_bounds_k : i + j ≤ res.size) (if_pos : i + j < res.size) (if_neg : i < nums1.size) (if_neg_1 : j < nums2.size) (if_neg_2 : nums2[j]! < nums1[i]!) (invariant_inv_counts : ∀ (v : ℤ), List.count v (List.take (i + j) res.toList) = List.count v (List.take i nums1.toList) + List.count v (List.take j nums2.toList)) (invariant_inv_sorted_prefix : ∀ (i_1 : ℕ), i_1 + OfNat.ofNat 1 < i + j → i_1 + OfNat.ofNat 1 < res.size → (res.extract (OfNat.ofNat 0) (i + j))[i_1]! ≤ (res.extract (OfNat.ofNat 0) (i + j))[i_1 + OfNat.ofNat 1]!) (invariant_inv_last_le_next : i = OfNat.ofNat 0 ∧ j = OfNat.ofNat 0 ∨ (i < nums1.size → res[i + j - OfNat.ofNat 1]! ≤ nums1[i]!) ∧ (j < nums2.size → res[i + j - OfNat.ofNat 1]! ≤ nums2[j]!)) : ∀ (v : ℤ), List.count v (List.take (i + j + OfNat.ofNat 1) (res.toList.set (i + j) nums2[j]!)) = List.count v (List.take i nums1.toList) + List.count v (List.take (j + OfNat.ofNat 1) nums2.toList) := by
    intro v; specialize invariant_inv_counts v; simp_all +decide [ List.take_succ ] ;
    -- By adding the count of v in the (i+j)th element, we can adjust the count accordingly.
    have h_count_adjusted : List.count v (List.take (i + j) (res.toList.set (i + j) nums2[j])) = List.count v (List.take (i + j) res.toList) := by
      rw [ List.take_set_of_le ] ; aesop;
    linarith

theorem goal_7 (nums1 : Array ℤ) (nums2 : Array ℤ) (require_1 : (∀ (i : ℕ), i + OfNat.ofNat 1 < nums1.size → nums1[i]! ≤ nums1[i + OfNat.ofNat 1]!) ∧ ∀ (i : ℕ), i + OfNat.ofNat 1 < nums2.size → nums2[i]! ≤ nums2[i + OfNat.ofNat 1]!) (i : ℕ) (j : ℕ) (res : Array ℤ) (invariant_inv_sizes : res.size = nums1.size + nums2.size) (invariant_inv_bounds_i : i ≤ nums1.size) (invariant_inv_bounds_j : j ≤ nums2.size) (invariant_inv_bounds_k : i + j ≤ res.size) (if_pos : i + j < res.size) (if_neg : i < nums1.size) (if_neg_1 : j < nums2.size) (if_neg_2 : nums2[j]! < nums1[i]!) (invariant_inv_counts : ∀ (v : ℤ), List.count v (List.take (i + j) res.toList) = List.count v (List.take i nums1.toList) + List.count v (List.take j nums2.toList)) (invariant_inv_sorted_prefix : ∀ (i_1 : ℕ), i_1 + OfNat.ofNat 1 < i + j → i_1 + OfNat.ofNat 1 < res.size → (res.extract (OfNat.ofNat 0) (i + j))[i_1]! ≤ (res.extract (OfNat.ofNat 0) (i + j))[i_1 + OfNat.ofNat 1]!) (invariant_inv_last_le_next : i = OfNat.ofNat 0 ∧ j = OfNat.ofNat 0 ∨ (i < nums1.size → res[i + j - OfNat.ofNat 1]! ≤ nums1[i]!) ∧ (j < nums2.size → res[i + j - OfNat.ofNat 1]! ≤ nums2[j]!)) : ∀ i_1 < i + j, i_1 + OfNat.ofNat 1 < res.size → ((res.setIfInBounds (i + j) nums2[j]!).extract (OfNat.ofNat 0) (i + j + OfNat.ofNat 1))[i_1]! ≤ ((res.setIfInBounds (i + j) nums2[j]!).extract (OfNat.ofNat 0) (i + j + OfNat.ofNat 1))[i_1 + OfNat.ofNat 1]! := by
    intros i_1 hi_1 hi_1'; by_cases hi_1'' : i_1 + 1 = i + j <;> simp_all +decide [ Array.setIfInBounds ] ;
    · simp_all +decide [ Array.set, Array.getElem?_set ];
      simp_all +decide [ List.getElem?_set, List.take_succ ];
      simp_all +decide [ List.getElem?_append, List.getElem?_set ];
      grind;
    · convert invariant_inv_sorted_prefix i_1 ( lt_of_le_of_ne ( by linarith ) hi_1'' ) hi_1' using 1;
      · simp +decide [ Array.set, Array.getElem?_eq_getElem, hi_1, hi_1' ];
        simp +decide [ List.getElem?_set, List.getElem?_take, hi_1, hi_1' ];
        split_ifs <;> simp_all +decide [ Nat.lt_succ_iff ];
        · rw [ Array.getElem?_eq_getElem ] ; aesop;
        · linarith;
      · grind +ring

theorem goal_8 (nums1 : Array ℤ) (nums2 : Array ℤ) (require_1 : (∀ (i : ℕ), i + OfNat.ofNat 1 < nums1.size → nums1[i]! ≤ nums1[i + OfNat.ofNat 1]!) ∧ ∀ (i : ℕ), i + OfNat.ofNat 1 < nums2.size → nums2[i]! ≤ nums2[i + OfNat.ofNat 1]!) (i_1 : ℕ) (i_2 : ℕ) (res_1 : Array ℤ) (invariant_inv_bounds_i : i_1 ≤ nums1.size) (invariant_inv_bounds_j : i_2 ≤ nums2.size) (invariant_inv_sizes : res_1.size = nums1.size + nums2.size) (invariant_inv_bounds_k : i_1 + i_2 ≤ res_1.size) (invariant_inv_sorted_prefix : ∀ (i : ℕ), i + OfNat.ofNat 1 < i_1 + i_2 → i + OfNat.ofNat 1 < res_1.size → (res_1.extract (OfNat.ofNat 0) (i_1 + i_2))[i]! ≤ (res_1.extract (OfNat.ofNat 0) (i_1 + i_2))[i + OfNat.ofNat 1]!) (done_1 : res_1.size ≤ i_1 + i_2) (invariant_inv_counts : ∀ (v : ℤ), List.count v (List.take (i_1 + i_2) res_1.toList) = List.count v (List.take i_1 nums1.toList) + List.count v (List.take i_2 nums2.toList)) (invariant_inv_last_le_next : i_1 = OfNat.ofNat 0 ∧ i_2 = OfNat.ofNat 0 ∨ (i_1 < nums1.size → res_1[i_1 + i_2 - OfNat.ofNat 1]! ≤ nums1[i_1]!) ∧ (i_2 < nums2.size → res_1[i_1 + i_2 - OfNat.ofNat 1]! ≤ nums2[i_2]!)) : postcondition nums1 nums2 res_1 := by
    -- Since `res_1.size = i_1 + i_2` and `i_1 + i_2 = nums1.size + nums2.size`, we can conclude that `res_1.size = nums1.size + nums2.size`.
    have h_size : res_1.size = nums1.size + nums2.size := by
      exact?;
    refine' ⟨ h_size, _, _ ⟩;
    · intro i hi;
      convert invariant_inv_sorted_prefix i _ _ using 1;
      · simp +decide [ show i_1 + i_2 = res_1.size by linarith ];
      · norm_num [ show i_1 + i_2 = res_1.size by linarith ] at *;
      · grind;
      · exact hi;
    · intro v;
      convert invariant_inv_counts v using 1;
      · -- Since the size of `res_1` is equal to the sum of the sizes of `nums1` and `nums2`, the count of `v` in the entire `res_1` array is the same as the count in the first `i_1 + i_2` elements.
        have h_count_eq : List.count v res_1.toList = List.count v (List.take (i_1 + i_2) res_1.toList) := by
          rw [ List.take_of_length_le ( by simpa [ h_size ] using by linarith ) ];
        exact h_count_eq;
      · rw [ show i_1 = nums1.size by linarith, show i_2 = nums2.size by linarith ] ; simp +decide [ countInArray ] ;
        rw [ ← Array.count_toList, ← Array.count_toList ] ; simp +decide [ List.take_of_length_le ] ;

end Proof