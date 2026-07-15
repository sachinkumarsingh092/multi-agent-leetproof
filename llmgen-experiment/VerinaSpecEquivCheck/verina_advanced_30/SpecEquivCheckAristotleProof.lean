/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: e305bdbc-0771-478b-892a-bccb39a70dc7

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (nums : List Int) : VerinaSpec.longestIncreasingStreak_precond nums ↔ LLMSpec.precondition nums

- theorem postcondition_equiv (nums : List Int) (result : Nat) : LLMSpec.precondition nums →
  (VerinaSpec.longestIncreasingStreak_postcond nums result ↔ LLMSpec.postcondition nums result)

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

def longestIncreasingStreak_precond (nums : List Int) : Prop :=
  True

def longestIncreasingStreak_postcond (nums : List Int) (result: Nat) : Prop :=
  (nums = [] → result = 0) ∧
  (result > 0 →
    (List.range (nums.length - result + 1) |>.any (fun start =>
      start + result ≤ nums.length ∧
      (List.range (result - 1) |>.all (fun i =>
        nums[start + i]! < nums[start + i + 1]!)) ∧
      (start = 0 ∨ nums[start - 1]! ≥ nums[start]!) ∧
      (start + result = nums.length ∨ nums[start + result - 1]! ≥ nums[start + result]!)))) ∧
  (List.range (nums.length - result) |>.all (fun start =>
    List.range result |>.any (fun i =>
      start + i + 1 ≥ nums.length ∨ nums[start + i]! ≥ nums[start + i + 1]!)))

end VerinaSpec

namespace LLMSpec

-- A segment of `nums` starting at index `start` with length `len` is strictly increasing
-- if every adjacent pair within the segment increases.
-- This predicate is only intended to be used when `start + len ≤ nums.length`.
def StrictIncSegment (nums : List Int) (start : Nat) (len : Nat) : Prop :=
  ∀ (i : Nat), i + 1 < len → nums.get! (start + i) < nums.get! (start + i + 1)

-- Precondition: no restrictions.
def precondition (nums : List Int) : Prop :=
  True

def postcondition (nums : List Int) (result : Nat) : Prop :=
  -- Empty list case
  (nums = [] → result = 0) ∧
  -- Non-empty list case bounds
  (nums ≠ [] → 1 ≤ result ∧ result ≤ nums.length) ∧
  -- Achievability: there exists a strictly increasing segment of length `result`
  (∃ (start : Nat), start + result ≤ nums.length ∧ StrictIncSegment nums start result) ∧
  -- Maximality: any strictly increasing segment length is bounded by `result`
  (∀ (start : Nat) (len : Nat),
      start + len ≤ nums.length →
      StrictIncSegment nums start len →
      len ≤ result)

end LLMSpec

section Proof

theorem precondition_equiv (nums : List Int) : VerinaSpec.longestIncreasingStreak_precond nums ↔ LLMSpec.precondition nums := by
  -- Since both preconditions are True, their equivalence is trivial.
  simp [VerinaSpec.longestIncreasingStreak_precond, LLMSpec.precondition]

theorem postcondition_equiv (nums : List Int) (result : Nat) : LLMSpec.precondition nums →
  (VerinaSpec.longestIncreasingStreak_postcond nums result ↔ LLMSpec.postcondition nums result) := by
  -- By definition of `postcondition`, we know that if `result > 0`, then there exists a `start` such that the segment from `start` to `start + result` is strictly increasing.
  intro h_precondition
  simp [VerinaSpec.longestIncreasingStreak_postcond, LLMSpec.postcondition] at *;
  intro h_empty
  constructor
  intro hickest
  constructor
  intro h_nonempty
  constructor
  generalize_proofs at *; (
  contrapose! h_nonempty; aesop;);
  · grind;
  · constructor
    generalize_proofs at *; (
    by_cases h : 0 < result <;> simp_all +decide [ LLMSpec.StrictIncSegment ];
    · exact ⟨ hickest.1.choose, hickest.1.choose_spec.2.1, fun i hi => hickest.1.choose_spec.2.2.1 i ( by omega ) ⟩;
    · exact ⟨ 0, Nat.zero_le _ ⟩);
    intro start len h1 h2
    by_contra h_contra
    push_neg at h_contra
    generalize_proofs at *; (
    have := hickest.2 start ( by omega ) ; obtain ⟨ k, hk₁, hk₂ ⟩ := this; specialize h2 k; simp_all +decide ; omega;);
  · intro h
    constructor
    intro h_pos
    obtain ⟨start, hstart⟩ := h.right.left
    use start
    generalize_proofs at *; (
    refine' ⟨ _, hstart.1, _, _, _ ⟩ <;> try omega;
    · -- By definition of `StrictIncSegment`, for any `i` where `i + 1 < result`, we have `nums[start + i]! < nums[start + i + 1]!`.
      intros x hx
      have := hstart.2 x (by
      omega)
      aesop;
    · contrapose! h;
      refine' fun _ _ => ⟨ start - 1, result + 1, _, _, _ ⟩ <;> rcases start <;> simp_all +decide [ Nat.succ_eq_add_one ];
      · grind;
      · intro i hi; cases i <;> simp_all +decide [ LLMSpec.StrictIncSegment ] ;
        simpa only [ add_assoc, add_comm, add_left_comm ] using hstart.2 _ hi;
    · contrapose! h;
      refine' fun _ _ => ⟨ start, result + 1, _, _, _ ⟩ <;> simp_all +decide [ LLMSpec.StrictIncSegment ];
      · omega;
      · grind +ring);
    intro x hx
    by_contra h_contra
    push_neg at h_contra
    have h_strict_inc : LLMSpec.StrictIncSegment nums x (result + 1) := by
      intro i hi; specialize h_contra i; aesop;
    generalize_proofs at *; (
    linarith [ h.2.2 x ( result + 1 ) ( by omega ) h_strict_inc ])

end Proof