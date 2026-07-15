/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: df5c9575-805e-4531-aa55-1d7d8c9c7977

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (digits : List Nat) : VerinaSpec.binaryToDecimal_precond digits ↔ LLMSpec.precondition digits

- theorem postcondition_equiv (digits : List Nat) (result : Nat) : LLMSpec.precondition digits →
  (VerinaSpec.binaryToDecimal_postcond digits result ↔ LLMSpec.postcondition digits result)

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

def binaryToDecimal_precond (digits : List Nat) : Prop :=
  digits.all (fun d => d = 0 ∨ d = 1)

def binaryToDecimal_postcond (digits : List Nat) (result: Nat) : Prop :=
  result - List.foldl (λ acc bit => acc * 2 + bit) 0 digits = 0 ∧
  List.foldl (λ acc bit => acc * 2 + bit) 0 digits - result = 0

end VerinaSpec

namespace LLMSpec

-- Helper: digit validity predicate
def isBitDigit (d : Nat) : Prop := d = 0 ∨ d = 1

-- Helper: interpret a digit as a Bool bit (true iff digit is 1)
def digitToBit (d : Nat) : Bool := (d == 1)

-- Helper: kth digit from the right (least significant side), using total indexing.
-- This is intended to be used only under the guard k < digits.length.
def digitFromRight (digits : List Nat) (k : Nat) : Nat :=
  digits.get! (digits.length - 1 - k)

def precondition (digits : List Nat) : Prop :=
  ∀ (d : Nat), d ∈ digits → isBitDigit d

def postcondition (digits : List Nat) (result : Nat) : Prop :=
  (∀ (k : Nat), k < digits.length → result.testBit k = digitToBit (digitFromRight digits k)) ∧
  (∀ (k : Nat), digits.length ≤ k → result.testBit k = false)

end LLMSpec

section Proof

theorem precondition_equiv (digits : List Nat) : VerinaSpec.binaryToDecimal_precond digits ↔ LLMSpec.precondition digits := by
  -- The preconditions are equivalent because they both state that every element in the list is 0 or 1.
  simp [VerinaSpec.binaryToDecimal_precond, LLMSpec.precondition];
  -- The equivalence follows directly from the definition of `isBitDigit`.
  simp [LLMSpec.isBitDigit]

theorem postcondition_equiv (digits : List Nat) (result : Nat) : LLMSpec.precondition digits →
  (VerinaSpec.binaryToDecimal_postcond digits result ↔ LLMSpec.postcondition digits result) := by
  intro h_precondition
  constructor
  intro h_postcondition
  obtain ⟨h_foldl, h_valid⟩ := h_postcondition
  generalize_proofs at *;
  · -- By definition of `List.foldl`, we know that `List.foldl (fun acc bit => acc * 2 + bit) 0 digits` is equal to `Nat.ofDigits 2 digits`.
    have h_foldl_eq : List.foldl (fun acc bit => acc * 2 + bit) 0 digits = Nat.ofDigits 2 digits.reverse := by
      clear h_foldl h_valid h_precondition
      generalize_proofs at *;
      induction digits using List.reverseRecOn <;> simp_all +decide [ Nat.ofDigits ] ; ring!;
    generalize_proofs at *;
    -- By definition of `Nat.ofDigits`, we know that `Nat.ofDigits 2 digits.reverse` is equal to `result`.
    have h_ofDigits_eq : Nat.ofDigits 2 digits.reverse = result := by
      omega
    generalize_proofs at *;
    refine' ⟨ _, _ ⟩
    all_goals generalize_proofs at *;
    · intro k hk
      have h_bit_eq : Nat.testBit (Nat.ofDigits 2 digits.reverse) k = (digits.reverse.get! k = 1) := by
        have h_bit_eq : ∀ (ds : List ℕ), (∀ d ∈ ds, d = 0 ∨ d = 1) → ∀ k, k < ds.length → Nat.testBit (Nat.ofDigits 2 ds) k = (ds.get! k = 1) := by
          intros ds hds k hk; induction' ds with d ds ih generalizing k <;> simp_all +decide [ Nat.ofDigits ] ;
          rcases k with ( _ | k ) <;> simp_all +decide [ Nat.testBit, Nat.shiftRight_eq_div_pow ];
          · grind +ring;
          · simp_all +decide [ Nat.pow_succ', ← Nat.div_div_eq_div_mul ];
            cases hds.1 <;> simp_all +decide [ Nat.add_div ]
        generalize_proofs at *;
        exact h_bit_eq _ ( fun d hd => h_precondition d ( List.mem_reverse.mp hd ) ) _ ( by simpa using hk )
      generalize_proofs at *;
      simp_all +decide [ LLMSpec.digitToBit, LLMSpec.digitFromRight ];
      grind +ring;
    · intro k hk; rw [ ← h_ofDigits_eq ] ; simp +decide [ Nat.testBit, Nat.shiftRight_eq_div_pow ] ;
      rw [ Nat.div_eq_of_lt ];
      refine' Nat.ofDigits_lt_base_pow_length _ _ |> lt_of_lt_of_le <| Nat.pow_le_pow_right ( by decide ) _ ; aesop
      generalize_proofs at *; (
      exact fun x hx => by have := h_precondition x ( List.mem_reverse.mp hx ) ; rcases this with ( rfl | rfl ) <;> decide;);
      simpa using hk.trans' ( by simp +decide );
  · intro h_postcondition
    obtain ⟨h_foldl, h_valid⟩ := h_postcondition
    generalize_proofs at *;
    -- By definition of `testBit`, we know that `result = List.foldl (fun acc bit => acc * 2 + bit) 0 digits`.
    have h_result : result = Nat.ofDigits 2 (List.reverse digits) := by
      refine' Nat.eq_of_testBit_eq _;
      intro i; by_cases hi : i < digits.length <;> simp_all +decide [ Nat.testBit ] ;
      · -- By definition of `Nat.ofDigits`, the i-th bit of `Nat.ofDigits 2 digits.reverse` is equal to the i-th digit from the right of `digits`.
        have h_bit_eq : (Nat.ofDigits 2 digits.reverse) / 2 ^ i % 2 = (digits.reverse.get! i) := by
          have h_bit_eq : ∀ (L : List ℕ), (∀ d ∈ L, d = 0 ∨ d = 1) → ∀ i < L.length, (Nat.ofDigits 2 L) / 2 ^ i % 2 = L.get! i := by
            intros L hL i hi; induction' L with hd tl ih generalizing i <;> simp_all +decide [ Nat.ofDigits ] ;
            rcases i with ( _ | i ) <;> simp_all +decide [ Nat.pow_succ', ← Nat.div_div_eq_div_mul ];
            · grind +ring;
            · cases hL.1 <;> simp_all +decide [ Nat.add_div ]
          generalize_proofs at *;
          exact h_bit_eq _ ( fun d hd => by simpa using h_precondition d ( List.mem_reverse.mp hd ) ) _ ( by simpa using hi )
        generalize_proofs at *;
        simp_all +decide [ Nat.shiftRight_eq_div_pow, LLMSpec.digitToBit, LLMSpec.digitFromRight ];
        grind +ring;
      · rw [ Nat.shiftRight_eq_div_pow ];
        rw [ Nat.div_eq_of_lt ];
        refine' lt_of_lt_of_le ( Nat.ofDigits_lt_base_pow_length _ _ ) _ <;> norm_num [ hi ];
        · intro x hx; specialize h_precondition x hx; rcases h_precondition with ( rfl | rfl ) <;> norm_num;
        · exact pow_le_pow_right₀ ( by decide ) hi;
    -- By definition of `Nat.ofDigits`, we know that `Nat.ofDigits 2 (List.reverse digits) = List.foldl (fun acc bit => acc * 2 + bit) 0 digits`.
    have h_ofDigits : Nat.ofDigits 2 (List.reverse digits) = List.foldl (fun acc bit => acc * 2 + bit) 0 digits := by
      rw [ Nat.ofDigits_eq_foldr ] ; induction digits <;> simp_all +decide [ Nat.ofDigits ] ; ring;
      ac_rfl
    generalize_proofs at *; (simp_all +decide [ VerinaSpec.binaryToDecimal_postcond ] ;)

end Proof