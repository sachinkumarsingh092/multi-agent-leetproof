/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 2f56da9f-8722-4aa4-bd5c-ab3fa1d94f7d

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (n : Nat) : VerinaSpec.nthUglyNumber_precond n ↔ LLMSpec.precondition n

- theorem postcondition_equiv (n : Nat) (result : Nat) : LLMSpec.precondition n →
  (VerinaSpec.nthUglyNumber_postcond n result ↔ LLMSpec.postcondition n result)

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

def nthUglyNumber_precond (n : Nat) : Prop :=
  n > 0

def nextUgly (seq : List Nat) (c2 c3 c5 : Nat) : (Nat × Nat × Nat × Nat) :=
  let i2 := seq[c2]! * 2
  let i3 := seq[c3]! * 3
  let i5 := seq[c5]! * 5
  let next := min i2 (min i3 i5)
  let c2' := if next = i2 then c2 + 1 else c2
  let c3' := if next = i3 then c3 + 1 else c3
  let c5' := if next = i5 then c5 + 1 else c5
  (next, c2', c3', c5')

def divideOut : Nat → Nat → Nat
  | n, p =>
    if h : p > 1 ∧ n > 0 ∧ n % p = 0 then
      have : n / p < n := by
        apply Nat.div_lt_self
        · exact h.2.1  -- n > 0
        · exact Nat.lt_of_succ_le (Nat.succ_le_of_lt h.1)  -- 1 < p, so 2 ≤ p
      divideOut (n / p) p
    else n
termination_by n p => n

def isUgly (x : Nat) : Bool :=
  if x = 0 then
    false
  else
    let n1 := divideOut x 2
    let n2 := divideOut n1 3
    let n3 := divideOut n2 5
    n3 = 1

def nthUglyNumber_postcond (n : Nat) (result: Nat) : Prop :=
  isUgly result = true ∧
  ((List.range (result)).filter (fun i => isUgly i)).length = n - 1

end VerinaSpec

namespace LLMSpec

-- An ugly number is positive and has no prime divisors other than 2, 3, or 5.
-- This is purely relational (no factorization API required).
def IsUgly (x : Nat) : Prop :=
  x > 0 ∧
  ∀ (p : Nat), Nat.Prime p → p ∣ x → (p = 2 ∨ p = 3 ∨ p = 5)

-- Count ugly numbers in the bounded range [0, r].
-- We use Classical decidability to be able to filter by the Prop predicate `IsUgly`.
noncomputable def countUglyUpTo (r : Nat) : Nat :=
  by
    classical
    exact ((Finset.range (r + 1)).filter IsUgly).card

-- Input is a 1-based index into the increasing sequence of ugly numbers.
def precondition (n : Nat) : Prop :=
  n ≥ 1

-- Postcondition: result is the n-th ugly number.
-- Characterization via counting within a bounded range ensures the set is finite in Lean.
-- The pair of equalities pins down the unique n-th ugly number:
-- - there are exactly n ugly numbers ≤ result
-- - there are exactly n-1 ugly numbers ≤ result-1 (so result is the next ugly number)
def postcondition (n : Nat) (result : Nat) : Prop :=
  IsUgly result ∧
  countUglyUpTo result = n ∧
  countUglyUpTo (result - 1) = (n - 1)

end LLMSpec

section Proof

theorem precondition_equiv (n : Nat) : VerinaSpec.nthUglyNumber_precond n ↔ LLMSpec.precondition n := by
  -- The preconditions are the same, so the equivalence is immediate.
  simp [VerinaSpec.nthUglyNumber_precond, LLMSpec.precondition];
  grind

theorem postcondition_equiv (n : Nat) (result : Nat) : LLMSpec.precondition n →
  (VerinaSpec.nthUglyNumber_postcond n result ↔ LLMSpec.postcondition n result) := by
  -- TheVerinoSpec's isUgly is equivalent to LLMSpec's IsUgly.
  have h_isUgly_equiv : ∀ x, VerinaSpec.isUgly x ↔ LLMSpec.IsUgly x := by
    -- By definition of `divideOut`, we know that `divideOut x 2`, `divideOut (divideOut x 2) 3`, and `divideOut (divideOut (divideOut x 2) 3) 5` are all equal to 1 if and only if `x` has no prime factors other than 2, 3, or 5.
    have h_divideOut : ∀ x, VerinaSpec.divideOut x 2 = x / 2^Nat.factorization x 2 ∧ VerinaSpec.divideOut (x / 2^Nat.factorization x 2) 3 = (x / 2^Nat.factorization x 2) / 3^Nat.factorization (x / 2^Nat.factorization x 2) 3 ∧ VerinaSpec.divideOut ((x / 2^Nat.factorization x 2) / 3^Nat.factorization (x / 2^Nat.factorization x 2) 3) 5 = ((x / 2^Nat.factorization x 2) / 3^Nat.factorization (x / 2^Nat.factorization x 2) 3) / 5^Nat.factorization ((x / 2^Nat.factorization x 2) / 3^Nat.factorization (x / 2^Nat.factorization x 2) 3) 5 := by
      intro x
      have h_divideOut_2 : ∀ x, VerinaSpec.divideOut x 2 = x / 2^Nat.factorization x 2 := by
        intro x
        induction' x using Nat.strong_induction_on with x ih;
        unfold VerinaSpec.divideOut;
        rcases Nat.even_or_odd' x with ⟨ c, rfl | rfl ⟩ <;> simp_all +decide [ Nat.factorization_eq_zero_of_not_dvd ];
        rcases c with ( _ | c ) <;> simp_all +decide [ Nat.factorization_mul ];
        norm_num [ pow_add, Nat.mul_div_mul_left ]
      have h_divideOut_3 : ∀ x, VerinaSpec.divideOut x 3 = x / 3^Nat.factorization x 3 := by
        intro x
        induction' x using Nat.strong_induction_on with x ih
        by_cases hx : x = 0 ∨ x % 3 ≠ 0 ∨ Nat.factorization x 3 = 0
        all_goals generalize_proofs at *;
        · -- If x is 0, then divideOut x 3 is 0, and x / 3^Nat.factorization x 3 is also 0.
          by_cases hx0 : x = 0;
          · simp [hx0, VerinaSpec.divideOut];
          · -- If x is not divisible by 3, then divideOut x 3 is x.
            by_cases hx3 : x % 3 = 0 <;> simp_all +decide [ Nat.factorization_eq_zero_of_not_dvd ];
            · simp_all +decide [ Nat.factorization_eq_zero_iff ];
              exact False.elim <| hx <| Nat.dvd_of_mod_eq_zero hx3;
            · -- Since x is not divisible by 3, its factorization at 3 is zero.
              have h_factorization_zero : Nat.factorization x 3 = 0 := by
                exact Nat.factorization_eq_zero_of_not_dvd fun h => hx3 <| Nat.mod_eq_zero_of_dvd h
              generalize_proofs at *; (
              unfold VerinaSpec.divideOut; aesop;);
        · -- Since x is divisible by 3, we can write x as 3 * k for some k.
          obtain ⟨k, rfl⟩ : ∃ k, x = 3 * k := by
            exact Nat.dvd_of_mod_eq_zero ( by tauto )
          generalize_proofs at *; (
          rw [ VerinaSpec.divideOut ] ; simp_all +decide [ Nat.factorization_mul ] ; ring; (
          rw [ Nat.mul_div_mul_right _ _ ( by decide ) ] ; aesop;);)
      have h_divideOut_5 : ∀ x, VerinaSpec.divideOut x 5 = x / 5^Nat.factorization x 5 := by
        -- By definition of `divideOut`, we know that `divideOut x 5` is equal to `x / 5^Nat.factorization x 5`.
        intros x
        induction' x using Nat.strong_induction_on with x ih;
        unfold VerinaSpec.divideOut; by_cases hx : x = 0 <;> by_cases hx' : 5 ∣ x <;> simp +decide [ hx, hx', Nat.factorization_eq_zero_of_not_dvd ] ;
        · rw [ if_pos ⟨ Nat.pos_of_ne_zero hx, Nat.mod_eq_zero_of_dvd hx' ⟩, ih _ ( Nat.div_lt_self ( Nat.pos_of_ne_zero hx ) ( by decide ) ) ];
          cases hx' ; simp_all +decide [ Nat.factorization_eq_zero_of_not_dvd, Nat.dvd_div_iff_mul_dvd ];
          norm_num [ pow_add, Nat.mul_div_mul_left ];
        · exact fun _ _ => False.elim <| hx' <| Nat.dvd_of_mod_eq_zero ‹_›
      exact ⟨h_divideOut_2 x, h_divideOut_3 _, h_divideOut_5 _⟩;
    -- By definition of `divideOut`, we know that `divideOut x 2`, `divideOut (divideOut x 2) 3`, and `divideOut (divideOut (divideOut x 2) 3) 5` are all equal to 1 if and only if `x` has no prime factors other than 2, 3, or 5. Therefore, we can conclude that `isUgly x` is true if and only if `IsUgly x` is true.
    intros x
    simp [VerinaSpec.isUgly, LLMSpec.IsUgly, h_divideOut];
    constructor <;> intro h;
    · refine' ⟨ Nat.pos_of_ne_zero h.1, fun p pp dp => _ ⟩;
      contrapose! h;
      intro hx_ne_zero
      have h_div : p ∣ x / 2 ^ Nat.factorization x 2 / 3 ^ Nat.factorization (x / 2 ^ Nat.factorization x 2) 3 / 5 ^ Nat.factorization (x / 2 ^ Nat.factorization x 2 / 3 ^ Nat.factorization (x / 2 ^ Nat.factorization x 2) 3) 5 := by
        refine' Nat.dvd_div_of_mul_dvd _;
        refine' Nat.Coprime.mul_dvd_of_dvd_of_dvd _ _ _;
        · exact Nat.Coprime.pow_left _ ( Nat.Prime.coprime_iff_not_dvd ( by norm_num ) |>.2 fun h' => h.2.2 <| by have := Nat.prime_dvd_prime_iff_eq ( by norm_num : Nat.Prime 5 ) pp; tauto );
        · exact Nat.ordProj_dvd _ _;
        · refine' Nat.dvd_div_of_mul_dvd _;
          refine' Nat.Coprime.mul_dvd_of_dvd_of_dvd _ _ _;
          · exact Nat.Coprime.pow_left _ ( Nat.coprime_comm.mp <| pp.coprime_iff_not_dvd.mpr fun h' => by have := Nat.le_of_dvd ( by norm_num ) h'; interval_cases p <;> simp_all +decide );
          · exact Nat.ordProj_dvd _ _;
          · refine' Nat.dvd_div_of_mul_dvd _;
            exact Nat.Coprime.mul_dvd_of_dvd_of_dvd ( Nat.Coprime.pow_left _ ( by have := Nat.coprime_primes ( by decide : Nat.Prime 2 ) pp; tauto ) ) ( Nat.ordProj_dvd _ _ ) dp;
      exact fun h => by simp_all +decide [ Nat.Prime.dvd_iff_not_coprime ] ;
    · -- By definition of `IsUgly`, we know that `x` has no prime factors other than 2, 3, or 5.
      have h_factorization : x = 2^Nat.factorization x 2 * 3^Nat.factorization x 3 * 5^Nat.factorization x 5 := by
        conv_lhs => rw [ ← Nat.factorization_prod_pow_eq_self h.1.ne' ];
        rw [ Finsupp.prod_of_support_subset ];
        case s => exact { 2, 3, 5 };
        · simp +decide [ mul_assoc ];
        · intro p hp; specialize h; aesop;
        · norm_num;
      rw [ h_factorization ] ; norm_num [ Nat.mul_div_assoc, Nat.pow_succ', Nat.mul_assoc ] ;
  -- By definition of `countUglyUpTo`, we know that `countUglyUpTo result = n` if and only if there are exactly `n` ugly numbers less than or equal to `result`.
  have h_count_equiv : ∀ r, LLMSpec.countUglyUpTo r = ((List.range (r + 1)).filter (fun i => VerinaSpec.isUgly i)).length := by
    intro r
    simp [LLMSpec.countUglyUpTo];
    rw [ ← Multiset.coe_card ];
    rw [ ← Multiset.toFinset_card_of_nodup ] <;> norm_num [ List.nodup_range ];
    · congr 1 with x ; aesop;
    · exact List.Nodup.filter _ ( List.nodup_range );
  simp +decide [ LLMSpec.precondition, VerinaSpec.nthUglyNumber_postcond, LLMSpec.postcondition, h_count_equiv ];
  rcases result with ( _ | result ) <;> simp +arith +decide [ List.range_succ ];
  · aesop;
  · grind +ring

end Proof