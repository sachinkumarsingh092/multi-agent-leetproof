/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 88a716bb-8511-42c4-9bc8-bbdbe184be0d

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (nums : List Int) (target : Int) : VerinaSpec.twoSum_precond nums target ↔ LLMSpec.precondition nums target

- theorem postcondition_equiv (nums : List Int) (target : Int) (result : Option (Nat × Nat)) : LLMSpec.precondition nums target →
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

def twoSum_precond (nums : List Int) (target : Int) : Prop :=
  True

def twoSum_postcond (nums : List Int) (target : Int) (result: Option (Nat × Nat)) : Prop :=
    match result with
    | none => List.Pairwise (· + · ≠ target) nums
    | some (i, j) =>
        i < j ∧
        j < nums.length ∧
        nums[i]! + nums[j]! = target ∧
        (nums.take i).zipIdx.all (fun ⟨a, i'⟩ =>
          (nums.drop (i' + 1)).all (fun b => a + b ≠ target)) ∧
        ((nums.drop (i + 1)).take (j - i - 1)).all (fun b => nums[i]! + b ≠ target)

end VerinaSpec

namespace LLMSpec

-- Lexicographic (non-strict) order on pairs of natural numbers.
-- `a ≤lex b` iff `a.1 < b.1` or (`a.1 = b.1` and `a.2 ≤ b.2`).
def lexLE (a : Nat × Nat) (b : Nat × Nat) : Prop :=
  a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2)

-- A pair of indices is valid for TwoSum if it is in-bounds, ordered i<j, and sums to target.
def ValidPair (nums : List Int) (target : Int) (p : Nat × Nat) : Prop :=
  p.1 < p.2 ∧ p.2 < nums.length ∧ nums[p.1]! + nums[p.2]! = target

-- No preconditions: all lists and targets are allowed.
def precondition (nums : List Int) (target : Int) : Prop :=
  True

def postcondition (nums : List Int) (target : Int) (result : Option (Nat × Nat)) : Prop :=
  match result with
  | none =>
      -- No valid pair exists.
      ∀ (i : Nat) (j : Nat), i < j → j < nums.length → nums[i]! + nums[j]! ≠ target
  | some p =>
      -- Returned pair is valid and lexicographically minimal among all valid pairs.
      ValidPair nums target p ∧
      (∀ (q : Nat × Nat), ValidPair nums target q → lexLE p q)

end LLMSpec

section Proof

theorem precondition_equiv (nums : List Int) (target : Int) : VerinaSpec.twoSum_precond nums target ↔ LLMSpec.precondition nums target := by
  -- Since both preconditions are defined as True, they are trivially equivalent.
  simp [VerinaSpec.twoSum_precond, LLMSpec.precondition]

theorem postcondition_equiv (nums : List Int) (target : Int) (result : Option (Nat × Nat)) : LLMSpec.precondition nums target →
  (VerinaSpec.twoSum_postcond nums target result ↔ LLMSpec.postcondition nums target result) := by
  -- By definition of `twoSum_postcond` and `postcondition`, we can split the proof into two implications.
  intro h_precondition
  constructor;
  · cases result <;> simp_all +decide [ VerinaSpec.twoSum_postcond, LLMSpec.postcondition ];
    · intro h i j hij hj; contrapose! h; simp_all +decide [ List.pairwise_iff_get ] ;
      exact ⟨ ⟨ i, by linarith ⟩, ⟨ j, by linarith ⟩, hij, by simpa [ List.getElem?_eq_getElem ( by linarith : i < nums.length ) ] using h ⟩;
    · -- By definition of `ValidPair`, we know that `(i, j)` is a valid pair.
      intro h_lt h_bounds h_sum h_no_earlier h_no_later
      constructor;
      · unfold LLMSpec.ValidPair; aesop;
      · intro a b h_valid_pair
        cases' h_valid_pair with h_lt h_bounds h_sum
        by_cases h_cases : a < ‹ℕ × ℕ›.1;
        · contrapose! h_no_earlier;
          refine' ⟨ nums[a]!, a, _, _ ⟩ <;> simp_all +decide [ List.mem_iff_get ];
          · use ⟨ a, by
              simp +arith +decide [ List.length_zipIdx, h_cases ];
              linarith ⟩
            generalize_proofs at *;
            aesop;
          · use ⟨ b - ( a + 1 ), by
              grind ⟩
            generalize_proofs at *;
            grind +ring;
        · cases lt_or_eq_of_le ( le_of_not_gt h_cases ) <;> simp_all +decide [ LLMSpec.lexLE ];
          contrapose! h_no_later;
          -- Since $b < val✝.2$, we have $b - a - 1 < val✝.2 - a - 1$, so $nums[b]!$ is in the take of the drop of $a+1$ elements.
          have h_take : nums[b]! ∈ List.take (‹ℕ × ℕ›.2 - a - 1) (List.drop (a + 1) nums) := by
            rw [ List.mem_iff_get ];
            use ⟨ b - a - 1, by
              grind ⟩
            generalize_proofs at *;
            grind +ring;
          grind;
  · -- If the LLMSpec postcondition holds, then the VerinaSpec postcondition holds because the conditions are equivalent. We can use the fact that if the LLMSpec postcondition holds, then the VerinaSpec postcondition holds.
    intro h_postcondition
    cases' result with p hp;
    · -- By definition of `postcondition`, if there are no valid pairs, then the VerinaSpec postcondition holds.
      simp [VerinaSpec.twoSum_postcond, h_postcondition];
      rw [ List.pairwise_iff_get ] ; aesop;
    · obtain ⟨ hp₁, hp₂ ⟩ := h_postcondition;
      refine' ⟨ hp₁.1, hp₁.2.1, hp₁.2.2, _, _ ⟩;
      · -- By definition of `hp₂`, for any `i' < p.1`, there is no `j > i'` such that `nums[i']! + nums[j]! = target`.
        have h_no_pair : ∀ i' < p.1, ¬∃ j, i' < j ∧ j < nums.length ∧ nums[i']! + nums[j]! = target := by
          intro i' hi' h_exists_j
          obtain ⟨ j, hj₁, hj₂, hj₃ ⟩ := h_exists_j
          have h_contradiction : LLMSpec.lexLE p (i', j) := by
            exact hp₂ ( i', j ) ⟨ hj₁, hj₂, hj₃ ⟩;
          cases h_contradiction <;> linarith [ hp₁.1 ];
        simp_all +decide [ List.all_eq_true ];
        -- By definition of `List.zipIdx`, if `(a, b)` is in the zipIdx of the first `p.1` elements of `nums`, then `a = nums[b]!` and `b < p.1`.
        intro a b hab x hx
        obtain ⟨ha, hb⟩ : a = nums[b]! ∧ b < p.1 := by
          grind;
        obtain ⟨ k, hk ⟩ := List.mem_iff_get.mp hx;
        specialize h_no_pair b hb ( b + 1 + k ) ( by linarith [ Fin.is_lt k ] ) ; aesop;
      · contrapose! hp₂;
        simp_all +decide [ LLMSpec.ValidPair, LLMSpec.lexLE ];
        obtain ⟨ x, hx₁, hx₂ ⟩ := hp₂;
        obtain ⟨ k, hk ⟩ := List.mem_iff_get.mp hx₁;
        refine' ⟨ p.1, p.1 + 1 + k, _, _, _ ⟩ <;> simp_all +decide [ List.get ];
        · grind;
        · grind

end Proof