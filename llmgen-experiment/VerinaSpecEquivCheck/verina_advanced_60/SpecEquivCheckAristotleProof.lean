/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: a2a7f8ce-3eb1-4416-a034-ac831cdf3ff1

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem postcondition_equiv (nums : List Nat) (result : (List Nat × List Nat)) : LLMSpec.precondition nums →
  (VerinaSpec.partitionEvensOdds_postcond nums result ↔ LLMSpec.postcondition nums result)

The following was negated by Aristotle:

- theorem precondition_equiv (nums : List Nat) : VerinaSpec.partitionEvensOdds_precond nums ↔ LLMSpec.precondition nums

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

def partitionEvensOdds_precond (nums : List Nat) : Prop :=
  True

def partitionEvensOdds_postcond (nums : List Nat) (result: (List Nat × List Nat)): Prop :=
  let evens := result.fst
  let odds := result.snd
  evens ++ odds = nums.filter (fun n => n % 2 == 0) ++ nums.filter (fun n => n % 2 == 1) ∧
  evens.all (fun n => n % 2 == 0) ∧
  odds.all (fun n => n % 2 == 1)

end VerinaSpec

namespace LLMSpec

-- Helper predicates for parity, defined using modulo so they are available in this environment.
def isEven (n : Nat) : Prop := n % 2 = 0

def isOdd (n : Nat) : Prop := n % 2 = 1

def precondition (nums : List Nat) : Prop :=
  nums.Nodup

def postcondition (nums : List Nat) (result : (List Nat × List Nat)) : Prop :=
  let evens := result.1
  let odds := result.2
  evens.Sublist nums ∧
  odds.Sublist nums ∧
  (∀ (x : Nat), x ∈ evens ↔ (x ∈ nums ∧ isEven x)) ∧
  (∀ (x : Nat), x ∈ odds ↔ (x ∈ nums ∧ isOdd x)) ∧
  (∀ (x : Nat), x ∈ evens → x ∉ odds)

end LLMSpec

section Proof

/- Aristotle found this block to be false. Here is a proof of the negation:



theorem precondition_equiv (nums : List Nat) : VerinaSpec.partitionEvensOdds_precond nums ↔ LLMSpec.precondition nums := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Consider the list [1, 2, 2].
  use [1, 2, 2];
  -- Show that the list [1, 2, 2] satisfies the preconditions for partitioning into evens and odds.
  simp [VerinaSpec.partitionEvensOdds_precond, LLMSpec.precondition]

-/
theorem precondition_equiv (nums : List Nat) : VerinaSpec.partitionEvensOdds_precond nums ↔ LLMSpec.precondition nums := by
  sorry

theorem postcondition_equiv (nums : List Nat) (result : (List Nat × List Nat)) : LLMSpec.precondition nums →
  (VerinaSpec.partitionEvensOdds_postcond nums result ↔ LLMSpec.postcondition nums result) := by
  intro h_nodup
  constructor <;> intro h_post
  generalize_proofs at *; (
  obtain ⟨h_even_sub, h_odd_sub, h_even_filter, h_odd_filter⟩ : result.1.Sublist nums ∧ result.2.Sublist nums ∧ (∀ x, x ∈ result.1 ↔ (x ∈ nums ∧ x % 2 = 0)) ∧ (∀ x, x ∈ result.2 ↔ (x ∈ nums ∧ x % 2 = 1)) := by
    -- By definition of `partitionEvensOdds_postcond`, we know that `result.1` is the list of even numbers in `nums` and `result.2` is the list of odd numbers in `nums`.
    have h_even_odd : result.1 = nums.filter (fun n => n % 2 = 0) ∧ result.2 = nums.filter (fun n => n % 2 = 1) := by
      -- By definition of `partitionEvensOdds_postcond`, we know that `result.1` is the list of even numbers in `nums` and `result.2` is the list of odd numbers in `nums`. Therefore, we can split the conjunction into two parts.
      obtain ⟨h_even, h_odd⟩ := h_post;
      have h_even_odd : ∀ {l1 l2 l3 l4 : List ℕ}, l1 ++ l2 = l3 ++ l4 → (∀ x ∈ l1, x % 2 = 0) → (∀ x ∈ l2, x % 2 = 1) → (∀ x ∈ l3, x % 2 = 0) → (∀ x ∈ l4, x % 2 = 1) → l1 = l3 ∧ l2 = l4 := by
        intros l1 l2 l3 l4 h_eq h_even1 h_odd1 h_even2 h_odd2
        have h_len : l1.length = l3.length := by
          replace h_eq := congr_arg ( fun l => List.filter ( fun x => x % 2 = 0 ) l ) h_eq ; simp_all +decide [ List.filter_append ] ;
          rw [ List.filter_eq_self.mpr, List.filter_eq_nil_iff.mpr, List.filter_eq_self.mpr, List.filter_eq_nil_iff.mpr ] at h_eq <;> aesop;
        generalize_proofs at *; (
        rw [ List.append_eq_append_iff ] at h_eq ; aesop;)
      generalize_proofs at *; (
      exact h_even_odd h_even ( by simpa using h_odd.1 ) ( by simpa using h_odd.2 ) ( by simp ) ( by simp ) |> fun h => ⟨ h.1, h.2 ⟩ ;)
    generalize_proofs at *; (
    simp_all +decide [ List.filter_eq, List.sublist_append_left ]);
  refine' ⟨ h_even_sub, h_odd_sub, _, _, _ ⟩ <;> aesop);
  -- By definition of `postcondition`, we know that `evens` and `odds` are sublists of `nums`, and every element in `evens` is even, and every element in `odds` is odd.
  obtain ⟨h_evens_sublist, h_odds_sublist, h_evens_even, h_odds_odd, h_disjoint⟩ := h_post
  generalize_proofs at *; (
  have h_evens_eq : result.1 = nums.filter (fun n => n % 2 == 0) := by
    -- Since `result.1` is a sublist of `nums` and contains exactly the even elements, it must be equal to the filtered list of even numbers from `nums`.
    have h_evens_eq : result.1.Sublist (List.filter (fun n => n % 2 == 0) nums) := by
      -- Since `result.1` is a sublist of `nums` and contains exactly the even elements, it must be a sublist of the filtered list of even numbers from `nums`.
      have h_evens_sublist_filter : ∀ {l : List ℕ}, l.Sublist nums → (∀ x, x ∈ l ↔ x ∈ nums ∧ x % 2 == 0) → l.Sublist (List.filter (fun n => n % 2 == 0) nums) := by
        intros l hl_sublist hl_even; exact (by
          have h_filter : List.Sublist (List.filter (fun n => n % 2 == 0) l) (List.filter (fun n => n % 2 == 0) nums) := by
            exact?
          convert h_filter using 1
          generalize_proofs at *; (
          rw [ List.filter_eq_self.mpr ] ; aesop;))
      generalize_proofs at *; (
      exact h_evens_sublist_filter h_evens_sublist fun x => by simpa using h_evens_even x;)
    generalize_proofs at *; (
    -- Since `result.1` is a sublist of the filtered list and they have the same elements, they must be equal.
    have h_evens_eq : List.toFinset result.1 = List.toFinset (List.filter (fun n => n % 2 == 0) nums) := by
      ext x; specialize h_evens_even x; aesop;
    generalize_proofs at *; (
    exact List.Sublist.eq_of_length_le ‹_› ( by rw [ ← List.toFinset_card_of_nodup ( show List.Nodup ( List.filter ( fun n => n % 2 == 0 ) nums ) from h_nodup.filter _ ), ← List.toFinset_card_of_nodup ( show List.Nodup result.1 from h_evens_sublist.nodup ( by unfold LLMSpec.precondition at h_nodup; aesop ) ) ] ; aesop )))
  have h_odds_eq : result.2 = nums.filter (fun n => n % 2 == 1) := by
    -- Since `result.2` is a sublist of `nums` and contains exactly the odd elements, it must be equal to `nums.filter (fun n => n % 2 == 1)`.
    have h_odds_eq : result.2.Sublist (nums.filter (fun n => n % 2 == 1)) := by
      have h_odds_eq : ∀ {l : List ℕ}, result.2.Sublist l → (∀ x ∈ result.2, x ∈ l ∧ x % 2 == 1) → result.2.Sublist (l.filter (fun n => n % 2 == 1)) := by
        -- By definition of sublist, if `result.2` is a sublist of `l` and all elements in `result.2` are odd, then `result.2` is also a sublist of the filtered list of `l` where elements are odd.
        intros l hl_sublist hl_odd
        have h_filter : List.Sublist (List.filter (fun n => n % 2 == 1) result.2) (List.filter (fun n => n % 2 == 1) l) := by
          exact?
        generalize_proofs at *; (
        convert h_filter using 1 ; rw [ List.filter_eq_self.mpr ] ; aesop ( simp_config := { singlePass := true } ) ;)
      generalize_proofs at *; (
      exact h_odds_eq h_odds_sublist fun x hx => by specialize h_odds_odd x; aesop;)
    generalize_proofs at *; (
    refine' h_odds_eq.eq_of_length_le _ ; simp_all +decide [ List.filter_eq ] ; (
    have h_card : (nums.filter (fun n => n % 2 == 1)).toFinset.card ≤ (result.2.toFinset).card := by
      refine Finset.card_le_card ?_ ; intro x ; aesop
    generalize_proofs at *; (
    exact le_trans ( by rw [ List.toFinset_card_of_nodup ] ; exact h_nodup.filter _ ) ( h_card.trans ( List.toFinset_card_le _ ) ))))
  generalize_proofs at *; (
  unfold VerinaSpec.partitionEvensOdds_postcond; aesop;))

end Proof