/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 27c8f801-3a40-484f-92c3-1b35bbc4b9ea

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem goal_3 (nums : Array ℤ) (require_1 : precondition nums) (i : ℕ) (res : Array ℤ) (invariant_mz1_size : res.size = nums.size) (a_1 : i ≤ nums.size) (invariant_mz1_countsNonZero : ∀ (v : ℤ), v ≠ OfNat.ofNat 0 → countVal res v = countVal (nums.extract (OfNat.ofNat 0) i) v) (invariant_mz1_order : preservesNonZeroOrder (nums.extract (OfNat.ofNat 0) i) res) (if_pos : i < nums.size) (if_neg : ¬nums[i]! = OfNat.ofNat 0) (a : i - countVal (nums.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0) ≤ i) (invariant_mz1_prefixNonZero : ∀ k < i - countVal (nums.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0), res[k]! ≠ OfNat.ofNat 0) (invariant_mz1_suffixZero : ∀ (k : ℕ), i - countVal (nums.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0) ≤ k → k < nums.size → res[k]! = OfNat.ofNat 0) : i - Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 1 else acc) (OfNat.ofNat 0) (nums.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0) (min i nums.size) + OfNat.ofNat 1 = i + OfNat.ofNat 1 - Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 1 else acc) (OfNat.ofNat 0) (nums.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) (OfNat.ofNat 0) (min (i + OfNat.ofNat 1) nums.size)

- theorem goal_4 (nums : Array ℤ) (require_1 : precondition nums) (i : ℕ) (res : Array ℤ) (invariant_mz1_size : res.size = nums.size) (a_1 : i ≤ nums.size) (invariant_mz1_countsNonZero : ∀ (v : ℤ), v ≠ OfNat.ofNat 0 → countVal res v = countVal (nums.extract (OfNat.ofNat 0) i) v) (invariant_mz1_order : preservesNonZeroOrder (nums.extract (OfNat.ofNat 0) i) res) (if_pos : i < nums.size) (if_neg : ¬nums[i]! = OfNat.ofNat 0) (a : i - countVal (nums.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0) ≤ i) (invariant_mz1_prefixNonZero : ∀ k < i - countVal (nums.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0), res[k]! ≠ OfNat.ofNat 0) (invariant_mz1_suffixZero : ∀ (k : ℕ), i - countVal (nums.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0) ≤ k → k < nums.size → res[k]! = OfNat.ofNat 0) : ∀ (v : ℤ), v ≠ OfNat.ofNat 0 → countVal (res.set! (i - countVal (nums.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0)) nums[i]!) v = countVal (nums.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) v

- theorem goal_5 (nums : Array ℤ) (require_1 : precondition nums) (i : ℕ) (res : Array ℤ) (invariant_mz1_size : res.size = nums.size) (a_1 : i ≤ nums.size) (invariant_mz1_countsNonZero : ∀ (v : ℤ), v ≠ OfNat.ofNat 0 → countVal res v = countVal (nums.extract (OfNat.ofNat 0) i) v) (invariant_mz1_order : preservesNonZeroOrder (nums.extract (OfNat.ofNat 0) i) res) (if_pos : i < nums.size) (if_neg : ¬nums[i]! = OfNat.ofNat 0) (a : i - countVal (nums.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0) ≤ i) (invariant_mz1_prefixNonZero : ∀ k < i - countVal (nums.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0), res[k]! ≠ OfNat.ofNat 0) (invariant_mz1_suffixZero : ∀ (k : ℕ), i - countVal (nums.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0) ≤ k → k < nums.size → res[k]! = OfNat.ofNat 0) : preservesNonZeroOrder (nums.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) (res.setIfInBounds (i - Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 1 else acc) (OfNat.ofNat 0) (nums.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0) (min i nums.size)) nums[i]!)

- theorem goal_6 (nums : Array ℤ) (require_1 : precondition nums) : ∀ (v : ℤ), v ≠ OfNat.ofNat 0 → countVal (Array.replicate nums.size (OfNat.ofNat 0)) v = countVal (nums.extract (OfNat.ofNat 0) (OfNat.ofNat 0)) v

- theorem goal_7 (nums : Array ℤ) (require_1 : precondition nums) : preservesNonZeroOrder #[] (Array.replicate nums.size (OfNat.ofNat 0))

- theorem goal_8 (nums : Array ℤ) (require_1 : precondition nums) (i_1 : ℕ) (i_2 : Array ℤ) (j : ℕ) (res_1 : Array ℤ) (invariant_mz2_size : res_1.size = nums.size) (a_3 : j ≤ nums.size) (invariant_mz2_counts : ∀ (v : ℤ), countVal nums v = countVal res_1 v) (invariant_mz2_order : preservesNonZeroOrder nums res_1) (if_pos : j < nums.size) (a_1 : i_1 ≤ nums.size) (done_1 : ¬i_1 < nums.size) (invariant_mz1_size : i_2.size = nums.size) (invariant_mz1_countsNonZero : ∀ (v : ℤ), v ≠ OfNat.ofNat 0 → countVal i_2 v = countVal (nums.extract (OfNat.ofNat 0) i_1) v) (invariant_mz1_order : preservesNonZeroOrder (nums.extract (OfNat.ofNat 0) i_1) i_2) (a_2 : i_1 - countVal (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) ≤ j) (invariant_mz2_prefixNonZero : ∀ k < i_1 - countVal (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0), res_1[k]! ≠ OfNat.ofNat 0) (invariant_mz2_suffixZero : ∀ (k : ℕ), i_1 - countVal (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) ≤ k → k < nums.size → res_1[k]! = OfNat.ofNat 0) (a : i_1 - countVal (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) ≤ i_1) (invariant_mz1_prefixNonZero : ∀ k < i_1 - countVal (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0), i_2[k]! ≠ OfNat.ofNat 0) (invariant_mz1_suffixZero : ∀ (k : ℕ), i_1 - countVal (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) ≤ k → k < nums.size → i_2[k]! = OfNat.ofNat 0) : ∀ (v : ℤ), countVal nums v = countVal (res_1.set! j (OfNat.ofNat 0)) v

- theorem goal_9 (nums : Array ℤ) (require_1 : precondition nums) (i_1 : ℕ) (i_2 : Array ℤ) (j : ℕ) (res_1 : Array ℤ) (invariant_mz2_size : res_1.size = nums.size) (a_3 : j ≤ nums.size) (invariant_mz2_counts : ∀ (v : ℤ), countVal nums v = countVal res_1 v) (invariant_mz2_order : preservesNonZeroOrder nums res_1) (if_pos : j < nums.size) (a_1 : i_1 ≤ nums.size) (done_1 : ¬i_1 < nums.size) (invariant_mz1_size : i_2.size = nums.size) (invariant_mz1_countsNonZero : ∀ (v : ℤ), v ≠ OfNat.ofNat 0 → countVal i_2 v = countVal (nums.extract (OfNat.ofNat 0) i_1) v) (invariant_mz1_order : preservesNonZeroOrder (nums.extract (OfNat.ofNat 0) i_1) i_2) (a_2 : i_1 - countVal (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) ≤ j) (invariant_mz2_prefixNonZero : ∀ k < i_1 - countVal (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0), res_1[k]! ≠ OfNat.ofNat 0) (invariant_mz2_suffixZero : ∀ (k : ℕ), i_1 - countVal (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) ≤ k → k < nums.size → res_1[k]! = OfNat.ofNat 0) (a : i_1 - countVal (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) ≤ i_1) (invariant_mz1_prefixNonZero : ∀ k < i_1 - countVal (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0), i_2[k]! ≠ OfNat.ofNat 0) (invariant_mz1_suffixZero : ∀ (k : ℕ), i_1 - countVal (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) ≤ k → k < nums.size → i_2[k]! = OfNat.ofNat 0) : preservesNonZeroOrder nums (res_1.setIfInBounds j (OfNat.ofNat 0))

- theorem goal_10 (nums : Array ℤ) (require_1 : precondition nums) (i_1 : ℕ) (i_2 : Array ℤ) (a_1 : i_1 ≤ nums.size) (done_1 : ¬i_1 < nums.size) (invariant_mz1_size : i_2.size = nums.size) (invariant_mz1_countsNonZero : ∀ (v : ℤ), v ≠ OfNat.ofNat 0 → countVal i_2 v = countVal (nums.extract (OfNat.ofNat 0) i_1) v) (invariant_mz1_order : preservesNonZeroOrder (nums.extract (OfNat.ofNat 0) i_1) i_2) (a : i_1 - countVal (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) ≤ i_1) (invariant_mz1_prefixNonZero : ∀ k < i_1 - countVal (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0), i_2[k]! ≠ OfNat.ofNat 0) (invariant_mz1_suffixZero : ∀ (k : ℕ), i_1 - countVal (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) ≤ k → k < nums.size → i_2[k]! = OfNat.ofNat 0) : ∀ (v : ℤ), countVal nums v = countVal i_2 v

- theorem goal_11 (nums : Array ℤ) (require_1 : precondition nums) (i_1 : ℕ) (i_2 : Array ℤ) (a_1 : i_1 ≤ nums.size) (done_1 : ¬i_1 < nums.size) (invariant_mz1_size : i_2.size = nums.size) (invariant_mz1_countsNonZero : ∀ (v : ℤ), v ≠ OfNat.ofNat 0 → countVal i_2 v = countVal (nums.extract (OfNat.ofNat 0) i_1) v) (invariant_mz1_order : preservesNonZeroOrder (nums.extract (OfNat.ofNat 0) i_1) i_2) (a : i_1 - countVal (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) ≤ i_1) (invariant_mz1_prefixNonZero : ∀ k < i_1 - countVal (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0), i_2[k]! ≠ OfNat.ofNat 0) (invariant_mz1_suffixZero : ∀ (k : ℕ), i_1 - countVal (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) ≤ k → k < nums.size → i_2[k]! = OfNat.ofNat 0) : preservesNonZeroOrder nums i_2

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

section Specs

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

theorem goal_3 (nums : Array ℤ) (require_1 : precondition nums) (i : ℕ) (res : Array ℤ) (invariant_mz1_size : res.size = nums.size) (a_1 : i ≤ nums.size) (invariant_mz1_countsNonZero : ∀ (v : ℤ), v ≠ OfNat.ofNat 0 → countVal res v = countVal (nums.extract (OfNat.ofNat 0) i) v) (invariant_mz1_order : preservesNonZeroOrder (nums.extract (OfNat.ofNat 0) i) res) (if_pos : i < nums.size) (if_neg : ¬nums[i]! = OfNat.ofNat 0) (a : i - countVal (nums.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0) ≤ i) (invariant_mz1_prefixNonZero : ∀ k < i - countVal (nums.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0), res[k]! ≠ OfNat.ofNat 0) (invariant_mz1_suffixZero : ∀ (k : ℕ), i - countVal (nums.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0) ≤ k → k < nums.size → res[k]! = OfNat.ofNat 0) : i - Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 1 else acc) (OfNat.ofNat 0) (nums.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0) (min i nums.size) + OfNat.ofNat 1 = i + OfNat.ofNat 1 - Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 1 else acc) (OfNat.ofNat 0) (nums.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) (OfNat.ofNat 0) (min (i + OfNat.ofNat 1) nums.size) := by
    rw [ min_eq_left, min_eq_left ] <;> try linarith;
    rw [ show nums.extract ( OfNat.ofNat ( OfNat.ofNat 0 ) ) ( i + 1 ) = ( nums.extract ( OfNat.ofNat ( OfNat.ofNat 0 ) ) i ).push ( nums[i]! ) from ?_ ];
    · simp +zetaDelta at *;
      rw [ Nat.sub_add_comm ];
      · grind;
      · induction' i with i ih <;> simp_all +decide [ Array.push ];
        induction' i + 1 with i ih <;> simp_all +decide [ List.take_succ ];
        grind;
    · ext j ; aesop;
      simp +zetaDelta at *;
      grind

theorem goal_4 (nums : Array ℤ) (require_1 : precondition nums) (i : ℕ) (res : Array ℤ) (invariant_mz1_size : res.size = nums.size) (a_1 : i ≤ nums.size) (invariant_mz1_countsNonZero : ∀ (v : ℤ), v ≠ OfNat.ofNat 0 → countVal res v = countVal (nums.extract (OfNat.ofNat 0) i) v) (invariant_mz1_order : preservesNonZeroOrder (nums.extract (OfNat.ofNat 0) i) res) (if_pos : i < nums.size) (if_neg : ¬nums[i]! = OfNat.ofNat 0) (a : i - countVal (nums.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0) ≤ i) (invariant_mz1_prefixNonZero : ∀ k < i - countVal (nums.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0), res[k]! ≠ OfNat.ofNat 0) (invariant_mz1_suffixZero : ∀ (k : ℕ), i - countVal (nums.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0) ≤ k → k < nums.size → res[k]! = OfNat.ofNat 0) : ∀ (v : ℤ), v ≠ OfNat.ofNat 0 → countVal (res.set! (i - countVal (nums.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0)) nums[i]!) v = countVal (nums.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) v := by
    unfold countVal at *;
    intro v hv;
    convert congr_arg ( fun x : ℕ => x + if nums[i]! = v then 1 else 0 ) ( invariant_mz1_countsNonZero v hv ) using 1;
    · -- By definition of foldl, we can split the operation into the original array and the new element.
      have h_split : ∀ (arr : Array ℤ) (i : ℕ) (x : ℤ), i < arr.size → Array.foldl (fun (acc : ℕ) (x : ℤ) => if x = v then acc + 1 else acc) 0 (arr.set! i x) = Array.foldl (fun (acc : ℕ) (x : ℤ) => if x = v then acc + 1 else acc) 0 arr + (if x = v then 1 else 0) - (if arr[i]! = v then 1 else 0) := by
        intros arr i x hi;
        induction' arr using Array.recOn with arr ih ; simp_all +decide [ Array.setIfInBounds ];
        induction' arr using List.reverseRecOn with arr ih generalizing i ; aesop;
        by_cases hi' : i < arr.length <;> simp_all +decide [ List.getElem_append_right ];
        · split_ifs <;> simp_all +decide [ add_assoc ];
          rw [ Nat.sub_add_cancel ];
          have h_foldl_pos : ∀ (arr : List ℤ), (∃ x ∈ arr, x = v) → 1 ≤ List.foldl (fun (acc : ℕ) (x : ℤ) => if x = v then acc + 1 else acc) 0 arr := by
            intros arr harr; induction' arr using List.reverseRecOn with arr ih <;> aesop;
          exact h_foldl_pos arr ⟨ _, List.getElem_mem _, ‹_› ⟩;
        · cases hi'.eq_or_lt <;> first | linarith | aesop;
      grind;
    · rw [ show nums.extract 0 ( i + 1 ) = nums.extract 0 i ++ #[nums[i]!] from ?_ ];
      · grind +ring;
      · refine' Array.ext _ _ <;> aesop

theorem goal_5 (nums : Array ℤ) (require_1 : precondition nums) (i : ℕ) (res : Array ℤ) (invariant_mz1_size : res.size = nums.size) (a_1 : i ≤ nums.size) (invariant_mz1_countsNonZero : ∀ (v : ℤ), v ≠ OfNat.ofNat 0 → countVal res v = countVal (nums.extract (OfNat.ofNat 0) i) v) (invariant_mz1_order : preservesNonZeroOrder (nums.extract (OfNat.ofNat 0) i) res) (if_pos : i < nums.size) (if_neg : ¬nums[i]! = OfNat.ofNat 0) (a : i - countVal (nums.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0) ≤ i) (invariant_mz1_prefixNonZero : ∀ k < i - countVal (nums.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0), res[k]! ≠ OfNat.ofNat 0) (invariant_mz1_suffixZero : ∀ (k : ℕ), i - countVal (nums.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0) ≤ k → k < nums.size → res[k]! = OfNat.ofNat 0) : preservesNonZeroOrder (nums.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) (res.setIfInBounds (i - Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 1 else acc) (OfNat.ofNat 0) (nums.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0) (min i nums.size)) nums[i]!) := by
    obtain ⟨ f, hf1, hf2, hf3 ⟩ := invariant_mz1_order;
    refine' ⟨ fun j => if j < i then f j else if j = i then i - countVal ( nums.extract ( OfNat.ofNat ( OfNat.ofNat 0 ) ) i ) ( OfNat.ofNat ( OfNat.ofNat 0 ) ) else f ( j - 1 ) + 1, _, _, _ ⟩ <;> simp_all +decide [ Array.setIfInBounds ];
    · intro j hj; split_ifs <;> simp_all +decide [ Array.set ] ;
      any_goals omega;
      · have := hf1 j ?_ <;> simp_all +decide [ isNonZeroIndex ];
        · -- Since $f j \neq i - countVal ...$, the set operation does not affect the element at $f j$.
          have h_neq : f j ≠ i - countVal (nums.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0) := by
            intro H; have := invariant_mz1_suffixZero ( f j ) ; simp_all +decide [ isNonZeroIndex ] ;
            specialize invariant_mz1_suffixZero ( i - countVal ( nums.extract ( OfNat.ofNat 0 ) i ) ( OfNat.ofNat 0 ) ) ; simp_all +decide [ isNonZeroIndex ] ;
            rw [ Nat.sub_add_cancel ] at invariant_mz1_suffixZero <;> norm_num at *;
            grind;
          simp_all +decide [ List.getElem_set, countVal ];
          exact fun h => False.elim <| h_neq <| h.symm;
        · convert hj.2 using 1;
          simp +decide [ Array.getElem_extract, * ];
      · unfold countVal; aesop;
      · rcases hj with ⟨ hj₁, hj₂ ⟩ ; rcases j with ( _ | j ) <;> simp_all +decide [ Array.get ] ;
        grind;
    · intro i_1 j hij hi hj; split_ifs <;> try linarith;
      · unfold isNonZeroIndex at *; aesop;
      · simp_all +decide [ isNonZeroIndex ];
        contrapose! hi;
        -- Since $i_1 < i$, we have $nums[i_1]! = 0$ by the definition of `extract`.
        have h_extract : nums[i_1]! = 0 := by
          grind +ring;
        cases nums ; aesop;
      · refine' Nat.lt_succ_of_le ( le_trans _ ( show f ( j - 1 ) ≥ f i_1 from _ ) );
        · grind;
        · refine' Nat.le_of_not_lt fun h => _;
          refine' h.not_le ( hf2 _ _ _ _ _ |> le_of_lt ) <;> simp_all +decide [ isNonZeroIndex ];
          · grind;
          · cases nums ; aesop;
          · grind +ring;
      · simp_all +decide [ isNonZeroIndex ];
        grind +ring;
      · simp_all +decide [ isNonZeroIndex ];
        grind +ring;
    · intro p hp hp'; split_ifs at hp' <;> simp_all +decide [ Array.set ] ;
      · simp_all +decide [ List.getElem_set ];
        split_ifs at hp' <;> simp_all +decide [ isNonZeroIndex ];
        · unfold countVal; aesop;
        · obtain ⟨ k, hk₁, hk₂ ⟩ := hf3 p ( by
            grind ) hp'
          generalize_proofs at *;
          use k; simp_all +decide [ Array.getElem?_eq_getElem ] ;
          -- Since $k < i$, we have $k \leq i$.
          have hk_le_i : k ≤ i := by
            grind;
          cases hk_le_i.eq_or_lt <;> simp_all +decide [ Array.getElem?_eq_getElem, Nat.lt_succ_iff ];
      · omega

theorem goal_6 (nums : Array ℤ) (require_1 : precondition nums) : ∀ (v : ℤ), v ≠ OfNat.ofNat 0 → countVal (Array.replicate nums.size (OfNat.ofNat 0)) v = countVal (nums.extract (OfNat.ofNat 0) (OfNat.ofNat 0)) v := by
    -- Since the replicate array is all zeros and the empty array has no elements, both counts are zero.
    intros v hv
    simp [countVal, hv];
    induction nums.size <;> simp_all +decide [ Array.replicate_succ ];
    -- Since $v \neq 0$, we have $0 \neq v$.
    exact Ne.symm hv

theorem goal_7 (nums : Array ℤ) (require_1 : precondition nums) : preservesNonZeroOrder #[] (Array.replicate nums.size (OfNat.ofNat 0)) := by
    -- Since there are no non-zero elements in the input, the output is also empty.
    use fun _ => 0;
    -- Since the input is empty, the output is also empty, and the non-zero order is preserved.
    simp [isNonZeroIndex];
    cases nums ; aesop

theorem goal_8 (nums : Array ℤ) (require_1 : precondition nums) (i_1 : ℕ) (i_2 : Array ℤ) (j : ℕ) (res_1 : Array ℤ) (invariant_mz2_size : res_1.size = nums.size) (a_3 : j ≤ nums.size) (invariant_mz2_counts : ∀ (v : ℤ), countVal nums v = countVal res_1 v) (invariant_mz2_order : preservesNonZeroOrder nums res_1) (if_pos : j < nums.size) (a_1 : i_1 ≤ nums.size) (done_1 : ¬i_1 < nums.size) (invariant_mz1_size : i_2.size = nums.size) (invariant_mz1_countsNonZero : ∀ (v : ℤ), v ≠ OfNat.ofNat 0 → countVal i_2 v = countVal (nums.extract (OfNat.ofNat 0) i_1) v) (invariant_mz1_order : preservesNonZeroOrder (nums.extract (OfNat.ofNat 0) i_1) i_2) (a_2 : i_1 - countVal (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) ≤ j) (invariant_mz2_prefixNonZero : ∀ k < i_1 - countVal (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0), res_1[k]! ≠ OfNat.ofNat 0) (invariant_mz2_suffixZero : ∀ (k : ℕ), i_1 - countVal (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) ≤ k → k < nums.size → res_1[k]! = OfNat.ofNat 0) (a : i_1 - countVal (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) ≤ i_1) (invariant_mz1_prefixNonZero : ∀ k < i_1 - countVal (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0), i_2[k]! ≠ OfNat.ofNat 0) (invariant_mz1_suffixZero : ∀ (k : ℕ), i_1 - countVal (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) ≤ k → k < nums.size → i_2[k]! = OfNat.ofNat 0) : ∀ (v : ℤ), countVal nums v = countVal (res_1.set! j (OfNat.ofNat 0)) v := by
    intro v; specialize invariant_mz2_counts v; simp_all +decide [ countVal ] ;
    -- Since the j-th element is already 0, setting it to 0 again doesn't change the array. Therefore, the foldl operation on the array after setting the j-th element to 0 is the same as the original foldl operation.
    have h_foldl_eq : res_1.setIfInBounds j 0 = res_1 := by
      grind;
    rw [h_foldl_eq]

theorem goal_9 (nums : Array ℤ) (require_1 : precondition nums) (i_1 : ℕ) (i_2 : Array ℤ) (j : ℕ) (res_1 : Array ℤ) (invariant_mz2_size : res_1.size = nums.size) (a_3 : j ≤ nums.size) (invariant_mz2_counts : ∀ (v : ℤ), countVal nums v = countVal res_1 v) (invariant_mz2_order : preservesNonZeroOrder nums res_1) (if_pos : j < nums.size) (a_1 : i_1 ≤ nums.size) (done_1 : ¬i_1 < nums.size) (invariant_mz1_size : i_2.size = nums.size) (invariant_mz1_countsNonZero : ∀ (v : ℤ), v ≠ OfNat.ofNat 0 → countVal i_2 v = countVal (nums.extract (OfNat.ofNat 0) i_1) v) (invariant_mz1_order : preservesNonZeroOrder (nums.extract (OfNat.ofNat 0) i_1) i_2) (a_2 : i_1 - countVal (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) ≤ j) (invariant_mz2_prefixNonZero : ∀ k < i_1 - countVal (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0), res_1[k]! ≠ OfNat.ofNat 0) (invariant_mz2_suffixZero : ∀ (k : ℕ), i_1 - countVal (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) ≤ k → k < nums.size → res_1[k]! = OfNat.ofNat 0) (a : i_1 - countVal (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) ≤ i_1) (invariant_mz1_prefixNonZero : ∀ k < i_1 - countVal (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0), i_2[k]! ≠ OfNat.ofNat 0) (invariant_mz1_suffixZero : ∀ (k : ℕ), i_1 - countVal (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) ≤ k → k < nums.size → i_2[k]! = OfNat.ofNat 0) : preservesNonZeroOrder nums (res_1.setIfInBounds j (OfNat.ofNat 0)) := by
    convert invariant_mz2_order using 1;
    grind

theorem goal_10 (nums : Array ℤ) (require_1 : precondition nums) (i_1 : ℕ) (i_2 : Array ℤ) (a_1 : i_1 ≤ nums.size) (done_1 : ¬i_1 < nums.size) (invariant_mz1_size : i_2.size = nums.size) (invariant_mz1_countsNonZero : ∀ (v : ℤ), v ≠ OfNat.ofNat 0 → countVal i_2 v = countVal (nums.extract (OfNat.ofNat 0) i_1) v) (invariant_mz1_order : preservesNonZeroOrder (nums.extract (OfNat.ofNat 0) i_1) i_2) (a : i_1 - countVal (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) ≤ i_1) (invariant_mz1_prefixNonZero : ∀ k < i_1 - countVal (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0), i_2[k]! ≠ OfNat.ofNat 0) (invariant_mz1_suffixZero : ∀ (k : ℕ), i_1 - countVal (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) ≤ k → k < nums.size → i_2[k]! = OfNat.ofNat 0) : ∀ (v : ℤ), countVal nums v = countVal i_2 v := by
    intro v; by_cases hv : v = 0 <;> simp +decide [ hv, invariant_mz1_countsNonZero, invariant_mz1_size ] ;
    · have h_count_zero : ∑ v ∈ Finset.image (fun x => x) (nums.toList.toFinset ∪ i_2.toList.toFinset), countVal nums v = nums.size ∧ ∑ v ∈ Finset.image (fun x => x) (nums.toList.toFinset ∪ i_2.toList.toFinset), countVal i_2 v = i_2.size := by
        have h_count_zero : ∀ (arr : Array ℤ), ∑ v ∈ Finset.image (fun x => x) (arr.toList.toFinset), countVal arr v = arr.size := by
          intros arr
          have h_count_zero : ∀ (l : List ℤ), ∑ v ∈ l.toFinset, (List.count v l) = l.length := by
            exact?;
          convert h_count_zero arr.toList using 1 ; simp +decide [ countVal ];
          -- The foldl operation is equivalent to counting the occurrences of x in the array.
          have h_foldl_eq_count : ∀ (arr : Array ℤ) (x : ℤ), Array.foldl (fun (acc : ℕ) (x_1 : ℤ) => if x_1 = x then acc + 1 else acc) 0 arr = Array.count x arr := by
            intros arr x; induction arr using Array.recOn ; simp +decide [ * ] ;
            induction ‹List ℤ› using List.reverseRecOn <;> aesop;
          exact Finset.sum_congr rfl fun x hx => h_foldl_eq_count arr x ▸ rfl;
        apply And.intro;
        · convert h_count_zero nums using 1;
          rw [ ← Finset.sum_subset ];
          · simp +decide [ Finset.subset_iff ];
            exact fun x hx => Or.inl hx;
          · simp +contextual [ countVal ];
            -- If x is not in nums, then the foldl operation on nums with the function that adds 1 when x is encountered will result in 0 because there are no elements in nums that are equal to x.
            intros x hx hx_not_in_nums
            have h_foldl_zero : ∀ (arr : Array ℤ), x ∉ arr → Array.foldl (fun (acc : ℕ) (x_1 : ℤ) => if x_1 = x then acc + 1 else acc) 0 arr = 0 := by
              -- We can prove this by induction on the array.
              intro arr harr_not_in_arr
              induction' arr using Array.recOn with arr ih;
              induction arr using List.reverseRecOn <;> aesop;
            exact h_foldl_zero nums hx_not_in_nums;
        · convert h_count_zero i_2 using 1;
          rw [ ← Finset.sum_subset ] ; aesop_cat;
          -- Since x is not in i_2, the if condition will always be false, so the accumulator remains 0.
          intros x hx hx_not_in_i2
          have h_foldl_zero : ∀ (xs : List ℤ), x ∉ xs → List.foldl (fun acc x_1 => if x_1 = x then acc + 1 else acc) 0 xs = 0 := by
            intro xs hx_not_in_xs; induction xs using List.reverseRecOn <;> aesop;
          simpa using h_foldl_zero i_2.toList ( by simpa using hx_not_in_i2 );
      have h_count_zero : ∑ v ∈ Finset.image (fun x => x) (nums.toList.toFinset ∪ i_2.toList.toFinset) \ {0}, countVal nums v = ∑ v ∈ Finset.image (fun x => x) (nums.toList.toFinset ∪ i_2.toList.toFinset) \ {0}, countVal i_2 v := by
        apply Finset.sum_congr rfl;
        simp +zetaDelta at *;
        cases le_antisymm a_1 done_1 ; aesop;
      by_cases h : 0 ∈ Finset.image ( fun x => x ) ( nums.toList.toFinset ∪ i_2.toList.toFinset ) <;> simp_all +decide [ Finset.sum_eq_add_sum_diff_singleton ];
      · simp_all +decide [ Finset.sum_eq_add_sum_diff_singleton ( show 0 ∈ nums.toList.toFinset ∪ i_2.toList.toFinset from by aesop ) ];
        linarith;
      · -- Since 0 is not in the list of elements of nums or i_2, the count of 0 in both arrays is zero.
        have h_count_zero : countVal nums 0 = 0 ∧ countVal i_2 0 = 0 := by
          -- Since 0 is not in the list of elements of nums or i_2, the count of 0 in both arrays is zero by definition of countVal.
          have h_count_zero : ∀ (arr : Array ℤ), 0 ∉ arr.toList → countVal arr 0 = 0 := by
            intros arr harr; induction arr using Array.recOn ; simp_all +decide [ countVal ] ;
            induction' ‹List ℤ› using List.reverseRecOn with x xs ih <;> aesop;
          exact ⟨ h_count_zero nums ( by simpa using h.1 ), h_count_zero i_2 ( by simpa using h.2 ) ⟩;
        exact h_count_zero.left.trans h_count_zero.right.symm;
    · rw [ show i_1 = nums.size by linarith ] ; simp +decide [ countVal ] ;

theorem goal_11 (nums : Array ℤ) (require_1 : precondition nums) (i_1 : ℕ) (i_2 : Array ℤ) (a_1 : i_1 ≤ nums.size) (done_1 : ¬i_1 < nums.size) (invariant_mz1_size : i_2.size = nums.size) (invariant_mz1_countsNonZero : ∀ (v : ℤ), v ≠ OfNat.ofNat 0 → countVal i_2 v = countVal (nums.extract (OfNat.ofNat 0) i_1) v) (invariant_mz1_order : preservesNonZeroOrder (nums.extract (OfNat.ofNat 0) i_1) i_2) (a : i_1 - countVal (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) ≤ i_1) (invariant_mz1_prefixNonZero : ∀ k < i_1 - countVal (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0), i_2[k]! ≠ OfNat.ofNat 0) (invariant_mz1_suffixZero : ∀ (k : ℕ), i_1 - countVal (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) ≤ k → k < nums.size → i_2[k]! = OfNat.ofNat 0) : preservesNonZeroOrder nums i_2 := by
    -- Since `i_1` is equal to the size of `nums`, the extract of `nums` from `0` to `i_1` is just `nums` itself.
    have h_extract : nums.extract 0 i_1 = nums := by
      grind;
    -- Substitute `h_extract` into `invariant_mz1_order` to conclude the proof.
    rw [h_extract] at invariant_mz1_order; exact invariant_mz1_order

end Proof