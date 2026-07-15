/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: f8528009-1bc4-4e29-9d4d-83abc0c2c3a5

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (s : String) : VerinaSpec.findFirstRepeatedChar_precond s ↔ LLMSpec.precondition s

- theorem postcondition_equiv (s : String) (result : Option Char) : LLMSpec.precondition s →
  (VerinaSpec.findFirstRepeatedChar_postcond s result ↔ LLMSpec.postcondition s result)

At Harmonic, we use a modified version of the `generalize_proofs` tactic.
For compatibility, we include this tactic at the start of the file.
If you add the comment "-- Harmonic `generalize_proofs` tactic" to your file, we will not do this.
-/

import Mathlib.Tactic

import Std.Data.HashSet


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

def findFirstRepeatedChar_precond (s : String) : Prop :=
  True

def findFirstRepeatedChar_postcond (s : String) (result: Option Char) :=
  let cs := s.toList
  match result with
  | some c =>
    let secondIdx := cs.zipIdx.findIdx (fun (x, i) => x = c && i ≠ cs.idxOf c)
    cs.count c ≥ 2 ∧
    List.Pairwise (· ≠ ·) (cs.take secondIdx)
  | none =>
    List.Pairwise (· ≠ ·) cs

end VerinaSpec

namespace LLMSpec

-- We reason about a `String` via its underlying list of characters.
-- This is a definitional projection in Lean (`String.data : List Char`).
def chars (s : String) : List Char :=
  s.data

-- Predicate: index j (in the character list) is a repeated occurrence.
def isRepeatIndex (s : String) (j : Nat) : Prop :=
  j < (chars s).length ∧
  ∃ i : Nat, i < j ∧ (chars s)[i]! = (chars s)[j]!

-- Predicate: j is the first index (left-to-right) at which a repeat occurs.
def isFirstRepeatIndex (s : String) (j : Nat) : Prop :=
  isRepeatIndex s j ∧
  ∀ k : Nat, k < j → ¬ isRepeatIndex s k

-- No preconditions.
def precondition (s : String) : Prop :=
  True

def postcondition (s : String) (result : Option Char) : Prop :=
  -- `none` exactly when there is no repeated index
  (result = none ↔ (∀ j : Nat, j < (chars s).length → ¬ isRepeatIndex s j)) ∧
  -- if `some c`, then c is the character at some first-repeat index
  (∀ c : Char, result = some c → (∃ j : Nat, isFirstRepeatIndex s j ∧ (chars s)[j]! = c)) ∧
  -- uniqueness: any first-repeat index must have the returned character
  (∀ c : Char, result = some c → (∀ j : Nat, isFirstRepeatIndex s j → (chars s)[j]! = c))

end LLMSpec

section Proof

theorem precondition_equiv (s : String) : VerinaSpec.findFirstRepeatedChar_precond s ↔ LLMSpec.precondition s := by
  -- Since both preconditions are True, their equivalence is trivial.
  simp [VerinaSpec.findFirstRepeatedChar_precond, LLMSpec.precondition]

noncomputable section AristotleLemmas

lemma LLMSpec.pairwise_iff_no_repeat (s : String) :
  List.Pairwise (· ≠ ·) s.data ↔ ∀ j < s.data.length, ¬ LLMSpec.isRepeatIndex s j := by
    constructor;
    · intro h j hj h';
      obtain ⟨ i, hi, h ⟩ := h';
      rename_i h';
      rw [ List.pairwise_iff_get ] at h';
      convert h' ⟨ hi, by linarith ⟩ ⟨ j, by linarith ⟩ h.1;
      simp +decide [ String.get ];
      convert h.2 using 1;
      · exact?;
      · exact?;
    · intro h;
      refine' List.pairwise_iff_get.mpr _;
      intro i j hij h_eq; specialize h j; simp_all +decide [ LLMSpec.isRepeatIndex ] ;
      specialize h ( by simp [ LLMSpec.chars ] ) i ; simp_all +decide [ LLMSpec.chars ]

lemma LLMSpec.isFirstRepeatIndex_iff_pairwise_prefix (s : String) (j : Nat) :
  LLMSpec.isFirstRepeatIndex s j ↔ LLMSpec.isRepeatIndex s j ∧ List.Pairwise (· ≠ ·) (s.data.take j) := by
    constructor <;> intro h;
    · -- If j is the first repeat index, then the list take j s.data is pairwise without duplicates.
      apply And.intro h.left;
      rw [ LLMSpec.pairwise_iff_no_repeat ];
      intro k hk; have := h.2; simp_all +decide [ LLMSpec.isRepeatIndex ] ;
      simp_all +decide [ LLMSpec.chars ];
      grind;
    · refine' ⟨ h.1, _ ⟩;
      intro k hk_lt_j hk_repeat_index
      obtain ⟨hk_lt_j', ⟨i, hi_lt_k, hi_eq⟩⟩ := hk_repeat_index;
      have := List.pairwise_iff_get.mp h.2;
      contrapose! this;
      use ⟨ i, by
        simp +zetaDelta at *;
        exact ⟨ by linarith, by linarith! ⟩ ⟩, ⟨ k, by
        rw [ List.length_take ] ; aesop ⟩
      generalize_proofs at *;
      simp_all +decide [ List.get ];
      rw [ List.getElem?_eq_getElem ] at hi_eq <;> aesop

lemma LLMSpec.secondIdx_eq_firstRepeat (s : String) (c : Char)
  (h_count : s.data.count c ≥ 2)
  (j : Nat)
  (h_first : LLMSpec.isFirstRepeatIndex s j)
  (h_val : s.data[j]! = c) :
  let cs := s.data
  let secondIdx := cs.zipIdx.findIdx (fun (x, i) => x = c && i ≠ cs.idxOf c)
  j = secondIdx := by
    refine' le_antisymm _ _ <;> simp_all +decide [ LLMSpec.isFirstRepeatIndex ];
    · have h_findIdx_ge_j : ∀ k < j, ¬(s.data.zipIdx.get! k).1 = c ∨ (s.data.zipIdx.get! k).2 = s.data.idxOf c := by
        intro k hk; specialize h_first; have := h_first.2 k hk; simp_all +decide [ LLMSpec.isRepeatIndex ] ;
        by_cases hk' : k < s.data.length <;> simp_all +decide [ LLMSpec.chars ];
        · by_cases hk'' : s.data[k] = c <;> simp_all +decide [ List.idxOf ];
          refine' le_antisymm _ _ <;> contrapose! h_first;
          · grind;
          · grind +ring;
        · linarith;
      contrapose! h_findIdx_ge_j;
      use List.findIdx (fun (x : Char × ℕ) => Decidable.decide (x.1 = c) && !Decidable.decide (x.2 = List.idxOf c s.data)) s.data.zipIdx;
      have h_findIdx_ge_j : ∀ {l : List (Char × ℕ)}, List.findIdx (fun (x : Char × ℕ) => Decidable.decide (x.1 = c) && !Decidable.decide (x.2 = List.idxOf c s.data)) l < l.length → (l.get! (List.findIdx (fun (x : Char × ℕ) => Decidable.decide (x.1 = c) && !Decidable.decide (x.2 = List.idxOf c s.data)) l)).1 = c ∧ (l.get! (List.findIdx (fun (x : Char × ℕ) => Decidable.decide (x.1 = c) && !Decidable.decide (x.2 = List.idxOf c s.data)) l)).2 ≠ List.idxOf c s.data := by
        intros l hl; induction l <;> simp_all +decide [ List.findIdx_cons ] ;
        grind +ring;
      refine' ⟨ by assumption, h_findIdx_ge_j _ ⟩;
      have h_findIdx_ge_j : j < s.data.length := by
        exact h_first.1.1;
      exact lt_of_lt_of_le ‹_› ( by simpa using h_findIdx_ge_j.le );
    · -- Since $j$ is the first repeat index, it must satisfy the predicate.
      have h_j_predicate : (s.data[j]?.getD 'A' = c) ∧ (j ≠ List.idxOf c s.data) := by
        -- If $j$ were equal to the index of $c$ in the list, then there would be no earlier occurrence of $c$, contradicting the fact that $j$ is a repeat index.
        by_contra h_eq_idx
        have h_no_earlier : ∀ i < j, s.data[i]?.getD 'A' ≠ c := by
          intros i hi; by_contra h_contra; simp_all +decide [ List.idxOf ] ;
          grind;
        obtain ⟨ i, hi, hi' ⟩ := h_first.1.2; specialize h_no_earlier i hi; simp_all +decide [ List.getElem?_eq_none ] ;
        exact h_no_earlier ( hi'.trans h_val );
      have h_findIdx_le_j : ∀ {k : ℕ}, k ≤ j → (s.data[k]?.getD 'A' = c) → (k ≠ List.idxOf c s.data) → List.findIdx (fun (x, i) => x = c && i ≠ List.idxOf c s.data) (s.data.zipIdx) ≤ k := by
        intros k hk_le_j hk_eq_c hk_ne_idxOf_c
        have h_findIdx_le_k : List.findIdx (fun (x, i) => x = c && i ≠ List.idxOf c s.data) (s.data.zipIdx) ≤ k := by
          have h_zipIdx : (s.data.zipIdx)[k]? = some (s.data[k]?.getD 'A', k) := by
            by_cases hk : k < s.data.length <;> simp_all +decide [ List.getElem?_eq_none ];
            have h_contradiction : j < s.data.length := by
              exact h_first.1.1;
            linarith
          grind
        exact h_findIdx_le_k;
      grind +ring

lemma LLMSpec.firstRepeat_eq_secondIdx (s : String) (c : Char)
  (h_count : s.data.count c ≥ 2)
  (secondIdx : Nat)
  (h_second : secondIdx = s.data.zipIdx.findIdx (fun (x, i) => x = c && i ≠ s.data.idxOf c))
  (h_pairwise : List.Pairwise (· ≠ ·) (s.data.take secondIdx)) :
  LLMSpec.isFirstRepeatIndex s secondIdx ∧ s.data[secondIdx]! = c := by
    -- From `h_count`, we have `secondIdx` is the index where `c` repeats.
    have h_secondIdx : secondIdx < s.data.length ∧ s.data[secondIdx]! = c ∧ secondIdx ≠ List.idxOf c s.data := by
      have h_secondIdx : secondIdx < s.data.length := by
        have h_secondIdx_lt_length : ∃ i, i < s.data.length ∧ (s.data[i]! = c) ∧ i ≠ s.data.idxOf c := by
          have h_count : List.count c s.data = Finset.card (Finset.filter (fun i => s.data[i]! = c) (Finset.range s.data.length)) := by
            have h_count : ∀ {l : List Char}, List.count c l = Finset.card (Finset.filter (fun i => l[i]! = c) (Finset.range l.length)) := by
              intros l; induction l <;> simp_all +decide [ Finset.sum_range_succ', List.count_cons ] ;
              rw [ Finset.card_filter, Finset.card_filter ];
              rw [ Finset.sum_range_succ' ] ; aesop;
            apply h_count;
          have h_exists_i : ∃ i ∈ Finset.filter (fun i => s.data[i]! = c) (Finset.range s.data.length), i ≠ s.data.idxOf c := by
            exact Finset.exists_mem_ne ( by linarith ) _;
          aesop;
        -- Since we have an existence of such an i, the findIdx should return that i. Therefore, secondIdx must be less than the length of the list.
        have h_findIdx_lt_length : ∀ {l : List (Char × ℕ)} {p : Char × ℕ → Bool}, (∃ i, i < l.length ∧ p (l[i]!)) → List.findIdx p l < l.length := by
          grind;
        obtain ⟨ i, hi₁, hi₂, hi₃ ⟩ := h_secondIdx_lt_length; specialize @h_findIdx_lt_length ( s.data.zipIdx ) ( fun x => x.1 = c && x.2 ≠ List.idxOf c s.data ) ; aesop;
      have h_secondIdx : ∀ {l : List (Char × ℕ)}, List.findIdx (fun (x, i) => x = c && i ≠ s.data.idxOf c) l < l.length → (l.get! (List.findIdx (fun (x, i) => x = c && i ≠ s.data.idxOf c) l)).1 = c ∧ (l.get! (List.findIdx (fun (x, i) => x = c && i ≠ s.data.idxOf c) l)).2 ≠ s.data.idxOf c := by
        intros l hl; induction l <;> simp_all +decide [ List.findIdx_cons ] ;
        grind +ring;
      specialize @h_secondIdx ( s.data.zipIdx ) ; aesop;
    refine' ⟨ ⟨ _, _ ⟩, h_secondIdx.2.1 ⟩ <;> norm_num [ LLMSpec.isRepeatIndex, LLMSpec.isFirstRepeatIndex ] at *;
    · refine' ⟨ h_secondIdx.1, List.idxOf c s.data, _, _ ⟩ <;> simp_all +decide [ LLMSpec.chars ];
      · contrapose! h_secondIdx; simp_all +decide [ List.idxOf ] ;
        grind +ring;
      · convert h_secondIdx.2.1.symm using 1;
        · have h_idx_of : c ∈ s.data := by
            exact List.count_pos_iff.mp ( pos_of_gt h_count );
          simp +decide [ h_idx_of, List.getElem?_eq_getElem ];
        · grind;
    · intro k hk₁ hk₂ x hx₁ hx₂; contrapose! hx₂; simp_all +decide [ List.pairwise_iff_get ] ;
      convert h_pairwise ⟨ x, by
        grind +ring ⟩ ⟨ k, by
        rw [ List.length_take ] ; aesop ⟩ hx₁ using 1
      generalize_proofs at *;
      rw [ List.getElem?_eq_getElem ] ; aesop;

end AristotleLemmas

theorem postcondition_equiv (s : String) (result : Option Char) : LLMSpec.precondition s →
  (VerinaSpec.findFirstRepeatedChar_postcond s result ↔ LLMSpec.postcondition s result) := by
  cases result <;> simp +decide [ LLMSpec.postcondition ] at *;
  · intro h
    simp [VerinaSpec.findFirstRepeatedChar_postcond, LLMSpec.pairwise_iff_no_repeat] at *;
    rfl;
  · rename_i c;
    intro h_precondition;
    constructor <;> intro h;
    · obtain ⟨h_count, h_pairwise⟩ := h;
      obtain ⟨j, hj⟩ : ∃ j, LLMSpec.isFirstRepeatIndex s j ∧ s.data[j]! = c := by
        have := LLMSpec.firstRepeat_eq_secondIdx s c h_count _ rfl h_pairwise; aesop;
      have h_unique : ∀ j1 j2, LLMSpec.isFirstRepeatIndex s j1 → LLMSpec.isFirstRepeatIndex s j2 → (s.data[j1]! = s.data[j2]!) := by
        intros j1 j2 hj1 hj2
        have h_unique : j1 = j2 := by
          exact le_antisymm ( le_of_not_gt fun h => hj1.2 _ h hj2.1 ) ( le_of_not_gt fun h => hj2.2 _ h hj1.1 )
        rw [h_unique];
      exact ⟨ ⟨ j, hj.1.1.1, hj.1.1 ⟩, ⟨ j, hj.1, by simpa using hj.2 ⟩, fun k hk => by simpa [ hj.2 ] using h_unique k j hk hj.1 ⟩;
    · -- By definition of `isFirstRepeatIndex`, we know that `j` is the first index where `c` appears twice.
      obtain ⟨j, hj_first, hj_eq⟩ := h.2.1
      have hj_count : s.data.count c ≥ 2 := by
        have := hj_first.1.2;
        obtain ⟨ i, hi, hi' ⟩ := this; simp_all +decide [ LLMSpec.chars ] ;
        have h_count : List.count c s.data ≥ List.count c (s.data.take j) + 1 := by
          have h_count : List.count c s.data = List.count c (s.data.take j) + List.count c (s.data.drop j) := by
            rw [ ← List.count_append, List.take_append_drop ];
          have h_count : c ∈ List.drop j s.data := by
            rw [ List.mem_iff_get ];
            use ⟨ 0, by
              simp +zetaDelta at *;
              exact hj_first.1.1 ⟩
            generalize_proofs at *;
            grind;
          exact ‹List.count c s.data = List.count c ( List.take j s.data ) + List.count c ( List.drop j s.data ) › ▸ Nat.add_le_add_left ( List.count_pos_iff.mpr h_count ) _;
        refine' le_trans _ h_count;
        refine' Nat.succ_le_succ ( List.count_pos_iff.mpr _ );
        rw [ List.mem_iff_get ];
        use ⟨ i, by
          simp +zetaDelta at *;
          exact ⟨ hi, lt_of_lt_of_le hi ( hj_first.1.1.le ) ⟩ ⟩
        generalize_proofs at *;
        grind
      have hj_pairwise : List.Pairwise (· ≠ ·) (s.data.take (s.data.zipIdx.findIdx (fun (x, i) => x = c && i ≠ s.data.idxOf c))) := by
        have hj_pairwise : j = s.data.zipIdx.findIdx (fun (x, i) => x = c && i ≠ s.data.idxOf c) := by
          apply LLMSpec.secondIdx_eq_firstRepeat;
          · exact hj_count;
          · assumption;
          · aesop;
        rw [ ← hj_pairwise ];
        exact hj_first.2 |> fun h => by simpa using LLMSpec.isFirstRepeatIndex_iff_pairwise_prefix s j |>.1 hj_first |>.2;
      exact ⟨hj_count, hj_pairwise⟩

end Proof