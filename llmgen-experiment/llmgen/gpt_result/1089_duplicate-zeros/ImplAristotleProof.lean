/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 8a9bdbe2-8282-4b96-b799-e3ff6fffbe16

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem goal_11 (arr : Array ℤ) (require_1 : True) (i_1 : ℕ) (idx : ℕ) (res : Array ℤ) (invariant_dz_pass2_idx_le_n : idx ≤ arr.size) (invariant_dz_pass2_res_size : res.size = arr.size) (if_neg : ¬arr[idx - OfNat.ofNat 1]! = OfNat.ofNat 0) (invariant_dz_pass1_i_le_n : i_1 ≤ arr.size) (if_pos : OfNat.ofNat 0 < idx) (done_1 : arr.size ≤ i_1) (invariant_dz_pass2_suffix_correct : ∀ j < arr.size, Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size) ≤ j → ∃! i, i < arr.size ∧ Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0) (min i arr.size) ≤ j ∧ j < Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) (OfNat.ofNat 0) (min (i + OfNat.ofNat 1) arr.size) ∧ res[j]! = if arr[i]! = OfNat.ofNat 0 then OfNat.ofNat 0 else arr[i]!) (if_pos_1 : OfNat.ofNat 0 < Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size)) (if_pos_2 : Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size) - OfNat.ofNat 1 < arr.size) : ∀ j < arr.size, Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size) ≤ j + OfNat.ofNat 1 → ∃! i, i < arr.size ∧ Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0) (min i arr.size) ≤ j ∧ j < Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) (OfNat.ofNat 0) (min (i + OfNat.ofNat 1) arr.size) ∧ (res.setIfInBounds (Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size) - OfNat.ofNat 1) arr[idx - OfNat.ofNat 1]!)[j]! = if arr[i]! = OfNat.ofNat 0 then OfNat.ofNat 0 else arr[i]!

- theorem goal_12 (arr : Array ℤ) (require_1 : True) (i_1 : ℕ) (idx : ℕ) (res : Array ℤ) (invariant_dz_pass2_idx_le_n : idx ≤ arr.size) (invariant_dz_pass2_res_size : res.size = arr.size) (if_neg : ¬arr[idx - OfNat.ofNat 1]! = OfNat.ofNat 0) (invariant_dz_pass1_i_le_n : i_1 ≤ arr.size) (if_pos : OfNat.ofNat 0 < idx) (done_1 : arr.size ≤ i_1) (invariant_dz_pass2_suffix_correct : ∀ j < arr.size, Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size) ≤ j → ∃! i, i < arr.size ∧ Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0) (min i arr.size) ≤ j ∧ j < Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) (OfNat.ofNat 0) (min (i + OfNat.ofNat 1) arr.size) ∧ res[j]! = if arr[i]! = OfNat.ofNat 0 then OfNat.ofNat 0 else arr[i]!) (if_pos_1 : OfNat.ofNat 0 < Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size)) (if_neg_1 : arr.size ≤ Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size) - OfNat.ofNat 1) : Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size) - OfNat.ofNat 1 = Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) (idx - OfNat.ofNat 1)) (OfNat.ofNat 0) (min (idx - OfNat.ofNat 1) arr.size)

- theorem goal_13 (arr : Array ℤ) (require_1 : True) (i_1 : ℕ) (idx : ℕ) (res : Array ℤ) (invariant_dz_pass2_idx_le_n : idx ≤ arr.size) (invariant_dz_pass2_res_size : res.size = arr.size) (if_neg : ¬arr[idx - OfNat.ofNat 1]! = OfNat.ofNat 0) (invariant_dz_pass1_i_le_n : i_1 ≤ arr.size) (if_pos : OfNat.ofNat 0 < idx) (done_1 : arr.size ≤ i_1) (invariant_dz_pass2_suffix_correct : ∀ j < arr.size, Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size) ≤ j → ∃! i, i < arr.size ∧ Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0) (min i arr.size) ≤ j ∧ j < Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) (OfNat.ofNat 0) (min (i + OfNat.ofNat 1) arr.size) ∧ res[j]! = if arr[i]! = OfNat.ofNat 0 then OfNat.ofNat 0 else arr[i]!) (if_neg_1 : Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size) = OfNat.ofNat 0) : Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size) = Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) (idx - OfNat.ofNat 1)) (OfNat.ofNat 0) (min (idx - OfNat.ofNat 1) arr.size)

- theorem goal_14 (arr : Array ℤ) (require_1 : True) (i_1 : ℕ) (invariant_dz_pass1_i_le_n : i_1 ≤ arr.size) (done_1 : arr.size ≤ i_1) : ∀ j < arr.size, Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) (min i_1 arr.size) ≤ j → ∃! i, i < arr.size ∧ Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0) (min i arr.size) ≤ j ∧ j < Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) (OfNat.ofNat 0) (min (i + OfNat.ofNat 1) arr.size) ∧ (Array.replicate arr.size (OfNat.ofNat 0))[j]! = if arr[i]! = OfNat.ofNat 0 then OfNat.ofNat 0 else arr[i]!

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

section Specs

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
Helper lemmas for producedLen. producedLen_step defines the folding function. producedLen_eq_foldl relates the foldl over extract to producedLen. producedLen_succ shows the recurrence relation for producedLen.
-/
def producedLen_step (acc : Nat) (x : Int) : Nat := if x = 0 then acc + 2 else acc + 1

theorem producedLen_eq_foldl (arr : Array Int) (k : Nat) :
  (arr.extract 0 k).foldl producedLen_step 0 = producedLen arr k := by
    unfold producedLen; aesop;

theorem producedLen_succ (arr : Array Int) (k : Nat) (hk : k < arr.size) :
  producedLen arr (k + 1) = producedLen arr k + if arr[k]! = 0 then 2 else 1 := by
    unfold producedLen;
    rw [ show arr.take ( k + 1 ) = arr.take k ++ #[arr[k]!] from ?_, Array.foldl_append ] ; aesop;
    refine' Array.ext _ _ <;> aesop

end AristotleLemmas

theorem goal_11 (arr : Array ℤ) (require_1 : True) (i_1 : ℕ) (idx : ℕ) (res : Array ℤ) (invariant_dz_pass2_idx_le_n : idx ≤ arr.size) (invariant_dz_pass2_res_size : res.size = arr.size) (if_neg : ¬arr[idx - OfNat.ofNat 1]! = OfNat.ofNat 0) (invariant_dz_pass1_i_le_n : i_1 ≤ arr.size) (if_pos : OfNat.ofNat 0 < idx) (done_1 : arr.size ≤ i_1) (invariant_dz_pass2_suffix_correct : ∀ j < arr.size, Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size) ≤ j → ∃! i, i < arr.size ∧ Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0) (min i arr.size) ≤ j ∧ j < Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) (OfNat.ofNat 0) (min (i + OfNat.ofNat 1) arr.size) ∧ res[j]! = if arr[i]! = OfNat.ofNat 0 then OfNat.ofNat 0 else arr[i]!) (if_pos_1 : OfNat.ofNat 0 < Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size)) (if_pos_2 : Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size) - OfNat.ofNat 1 < arr.size) : ∀ j < arr.size, Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size) ≤ j + OfNat.ofNat 1 → ∃! i, i < arr.size ∧ Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0) (min i arr.size) ≤ j ∧ j < Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) (OfNat.ofNat 0) (min (i + OfNat.ofNat 1) arr.size) ∧ (res.setIfInBounds (Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size) - OfNat.ofNat 1) arr[idx - OfNat.ofNat 1]!)[j]! = if arr[i]! = OfNat.ofNat 0 then OfNat.ofNat 0 else arr[i]! := by
    rcases idx with ( _ | _ | idx ) <;> simp +arith +decide at *;
    · rcases arr with ⟨ ⟨ ⟩ ⟩ <;> simp_all +decide [ Array.get ];
      cases i_1 <;> simp_all +decide [ Array.get ];
      intro j hj; rcases j with ( _ | j ) <;> simp_all +decide [ Array.setIfInBounds ] ;
      use 0; simp +decide [ if_neg ] ;
      rintro ( _ | y ) <;> simp_all +decide [ List.take ];
      cases y <;> simp_all +decide [ List.take_succ ];
      grind +ring;
    · intro j hj hj'; cases lt_or_eq_of_le hj'.ge <;> simp_all +decide [ Array.setIfInBounds ] ;
      · convert invariant_dz_pass2_suffix_correct j ‹_› _ using 1;
        · ext i; simp +decide [ Array.getElem_set, * ] ;
          split_ifs <;> simp_all +decide [ Nat.sub_eq_iff_eq_add ];
        · exact Nat.le_of_lt_succ ‹_›;
      · refine' ⟨ idx + 1, _, _ ⟩ <;> norm_num at *;
        · simp_all +decide [ Nat.succ_eq_add_one, min_eq_left ( by linarith : idx + 1 ≤ arr.size ), min_eq_left ( by linarith : idx + 2 ≤ arr.size ) ];
          rw [ show arr.extract 0 ( idx + 2 ) = arr.extract 0 ( idx + 1 ) ++ #[arr[idx + 1]!] from ?_ ] at * ; simp_all +decide [ Array.foldl_append ];
          · grind +ring;
          · simp +zetaDelta at *;
            refine' Array.ext _ _ <;> simp +arith +decide [ Array.getElem_push ];
            · grind +ring;
            · grind +ring;
        · intro y hy₁ hy₂ hy₃ hy₄; split_ifs at hy₄ ; simp_all +decide ;
          -- By definition of `producedLen`, we know that `producedLen arr (y + 1) = producedLen arr y + 1` if `arr[y]! ≠ 0`.
          have h_prod_len : ∀ y < arr.size, (arr.extract 0 (y + 1)).foldl (fun acc x => if x = 0 then acc + 2 else acc + 1) 0 = (arr.extract 0 y).foldl (fun acc x => if x = 0 then acc + 2 else acc + 1) 0 + if arr[y]! = 0 then 2 else 1 := by
            intros y hy; exact (by
            convert producedLen_succ arr y hy using 1);
          have h_unique : ∀ i j : ℕ, i < j → j < arr.size → (arr.extract 0 i).foldl (fun acc x => if x = 0 then acc + 2 else acc + 1) 0 < (arr.extract 0 j).foldl (fun acc x => if x = 0 then acc + 2 else acc + 1) 0 := by
            intros i j hij hj; induction hij <;> simp_all +decide [ Nat.succ_eq_add_one ] ;
            · grind +ring;
            · grind +ring;
          contrapose! h_unique;
          cases lt_or_gt_of_ne h_unique <;> simp_all +decide [ min_eq_left ];
          · use y, idx + 1;
            grind +ring;
          · use idx + 1, y;
            grind +ring

theorem goal_12 (arr : Array ℤ) (require_1 : True) (i_1 : ℕ) (idx : ℕ) (res : Array ℤ) (invariant_dz_pass2_idx_le_n : idx ≤ arr.size) (invariant_dz_pass2_res_size : res.size = arr.size) (if_neg : ¬arr[idx - OfNat.ofNat 1]! = OfNat.ofNat 0) (invariant_dz_pass1_i_le_n : i_1 ≤ arr.size) (if_pos : OfNat.ofNat 0 < idx) (done_1 : arr.size ≤ i_1) (invariant_dz_pass2_suffix_correct : ∀ j < arr.size, Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size) ≤ j → ∃! i, i < arr.size ∧ Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0) (min i arr.size) ≤ j ∧ j < Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) (OfNat.ofNat 0) (min (i + OfNat.ofNat 1) arr.size) ∧ res[j]! = if arr[i]! = OfNat.ofNat 0 then OfNat.ofNat 0 else arr[i]!) (if_pos_1 : OfNat.ofNat 0 < Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size)) (if_neg_1 : arr.size ≤ Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size) - OfNat.ofNat 1) : Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size) - OfNat.ofNat 1 = Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) (idx - OfNat.ofNat 1)) (OfNat.ofNat 0) (min (idx - OfNat.ofNat 1) arr.size) := by
    rcases idx <;> simp_all +decide [ Array.foldl_append ];
    rw [ show arr.extract ( 0 : ℕ ) ( _ + 1 ) = arr.extract ( 0 : ℕ ) ( _ ) ++ #[arr[‹_›]!] from ?_ ];
    any_goals exact ‹ℕ›;
    · simp +zetaDelta at *;
      grind +ring;
    · simp +zetaDelta at *;
      ext i ; simp +decide [ Array.getElem_push ];
      · grind;
      · -- Since the extracted array is just the first n elements of the original array, and the pushed array is the first n elements plus the nth element, the elements at position i in both arrays are the same.
        simp [Array.getElem_push, Array.getElem_extract];
        grind +ring

theorem goal_13 (arr : Array ℤ) (require_1 : True) (i_1 : ℕ) (idx : ℕ) (res : Array ℤ) (invariant_dz_pass2_idx_le_n : idx ≤ arr.size) (invariant_dz_pass2_res_size : res.size = arr.size) (if_neg : ¬arr[idx - OfNat.ofNat 1]! = OfNat.ofNat 0) (invariant_dz_pass1_i_le_n : i_1 ≤ arr.size) (if_pos : OfNat.ofNat 0 < idx) (done_1 : arr.size ≤ i_1) (invariant_dz_pass2_suffix_correct : ∀ j < arr.size, Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size) ≤ j → ∃! i, i < arr.size ∧ Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0) (min i arr.size) ≤ j ∧ j < Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) (OfNat.ofNat 0) (min (i + OfNat.ofNat 1) arr.size) ∧ res[j]! = if arr[i]! = OfNat.ofNat 0 then OfNat.ofNat 0 else arr[i]!) (if_neg_1 : Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size) = OfNat.ofNat 0) : Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size) = Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) (idx - OfNat.ofNat 1)) (OfNat.ofNat 0) (min (idx - OfNat.ofNat 1) arr.size) := by
    contrapose! if_neg_1;
    -- Since the array is non-empty and we're extracting elements from it, the foldl should accumulate some value.
    have h_foldl_pos : ∀ (xs : Array ℤ), xs ≠ #[] → Array.foldl (fun (acc : ℕ) (x : ℤ) => if x = 0 then acc + 2 else acc + 1) 0 xs ≠ 0 := by
      -- By induction on the array's length, we can show that the foldl result is always at least 1.
      intro xs hxs_nonempty
      induction' xs using Array.recOn with xs ih;
      induction xs using List.reverseRecOn <;> aesop;
    convert h_foldl_pos ( arr.extract 0 idx ) _ using 1;
    · norm_num [ min_eq_left invariant_dz_pass2_idx_le_n ];
    · cases idx <;> aesop

theorem goal_14 (arr : Array ℤ) (require_1 : True) (i_1 : ℕ) (invariant_dz_pass1_i_le_n : i_1 ≤ arr.size) (done_1 : arr.size ≤ i_1) : ∀ j < arr.size, Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) (min i_1 arr.size) ≤ j → ∃! i, i < arr.size ∧ Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0) (min i arr.size) ≤ j ∧ j < Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) (OfNat.ofNat 0) (min (i + OfNat.ofNat 1) arr.size) ∧ (Array.replicate arr.size (OfNat.ofNat 0))[j]! = if arr[i]! = OfNat.ofNat 0 then OfNat.ofNat 0 else arr[i]! := by
    intro j hj_lt hj_foldl
    generalize_proofs at *;
    contrapose! hj_foldl;
    refine' Nat.lt_of_lt_of_le hj_lt _;
    have h_foldl_ge_size : ∀ (xs : List ℤ), List.foldl (fun (acc : ℕ) (x : ℤ) => if x = 0 then acc + 2 else acc + 1) 0 xs ≥ xs.length := by
      -- We can prove this by induction on the list.
      intro xs
      induction' xs using List.reverseRecOn with x xs ih
      all_goals generalize_proofs at *;
      · rfl;
      · grind +ring
    generalize_proofs at *;
    convert h_foldl_ge_size ( arr.toList ) |> le_trans _ using 1
    generalize_proofs at *;
    · rw [ show i_1 = arr.size by linarith ] ; simp +decide [ Array.foldl_toList ] ;
    · norm_num +zetaDelta at *

end Proof