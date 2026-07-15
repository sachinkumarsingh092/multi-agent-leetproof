/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: ef71b0f9-42b2-4ede-b438-1362342b582e

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (arr : Array Int) : VerinaSpec.FindEvenNumbers_precond arr ↔ LLMSpec.precondition arr

- theorem postcondition_equiv (arr : Array Int) (result : Array Int) : LLMSpec.precondition arr →
  (VerinaSpec.FindEvenNumbers_postcond arr result ↔ LLMSpec.postcondition arr result)

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

def isEven (n : Int) : Bool :=
  n % 2 = 0

def FindEvenNumbers_precond (arr : Array Int) : Prop :=
  True

def FindEvenNumbers_postcond (arr : Array Int) (result: Array Int) :=
  result.all (fun x => isEven x) ∧
  result.toList.Sublist arr.toList ∧
  result.size = arr.toList.countP isEven

end VerinaSpec

namespace LLMSpec

-- Helper predicate: evenness as a Prop (Mathlib's `Even`).
def isEven (x : Int) : Prop := Even x

-- Helper predicate: evenness as a Bool (useful for `countP`).
def isEvenB (x : Int) : Bool := (x % 2) == 0

-- Order preservation expressed via an increasing index mapping from `result` indices to `arr` indices.
def orderPreserved (arr : Array Int) (result : Array Int) : Prop :=
  ∃ f : Nat → Nat,
    (∀ (i : Nat), i < result.size →
      f i < arr.size ∧ arr[f i]! = result[i]!) ∧
    (∀ (i : Nat) (j : Nat), i < j → j < result.size → f i < f j)

-- No additional preconditions.
def precondition (arr : Array Int) : Prop :=
  True

def postcondition (arr : Array Int) (result : Array Int) : Prop :=
  -- All outputs are even
  (∀ (i : Nat), i < result.size → isEven (result[i]!)) ∧
  -- Exact multiplicity of each value: even values are kept, odd values are removed
  (∀ (x : Int), (isEven x → result.count x = arr.count x) ∧ (¬ isEven x → result.count x = 0)) ∧
  -- Order is preserved relative to the input
  orderPreserved arr result ∧
  -- Size matches the number of even elements in the input
  (result.size = arr.countP isEvenB)

end LLMSpec

section Proof

theorem precondition_equiv (arr : Array Int) : VerinaSpec.FindEvenNumbers_precond arr ↔ LLMSpec.precondition arr := by
  -- Since both preconditions are True, their equivalence is trivial.
  simp [VerinaSpec.FindEvenNumbers_precond, LLMSpec.precondition]

theorem postcondition_equiv (arr : Array Int) (result : Array Int) : LLMSpec.precondition arr →
  (VerinaSpec.FindEvenNumbers_postcond arr result ↔ LLMSpec.postcondition arr result) := by
  unfold LLMSpec.postcondition VerinaSpec.FindEvenNumbers_postcond LLMSpec.precondition;
  simp +zetaDelta at *;
  constructor <;> intro h;
  · -- Show that the result array satisfies the postcondition of LLMSpec.
    apply And.intro;
    · -- Since `isEven` in `VerinaSpec` is defined as `n % 2 = 0`, which is equivalent to `Even n`, we can conclude that `result[i]!` is even for all `i < result.size`.
      have h_even : ∀ i < result.size, result[i]! % 2 = 0 := by
        unfold VerinaSpec.isEven at h; aesop;
      exact fun i hi => Int.even_iff.mpr ( h_even i hi );
    · refine' ⟨ _, _, _ ⟩;
      · intro x; by_cases hx : LLMSpec.isEven x <;> simp_all +decide [ LLMSpec.isEven ] ;
        · have h_count : List.count x result.toList = List.count x arr.toList := by
            have h_count : List.count x result.toList = List.count x (List.filter (fun x => VerinaSpec.isEven x) arr.toList) := by
              have h_count : List.count x result.toList = List.count x (List.filter (fun x => VerinaSpec.isEven x) result.toList) := by
                -- Since all elements in `result.toList` are even, the filtered list is equal to `result.toList`.
                have h_filter_eq : List.filter (fun x => VerinaSpec.isEven x) result.toList = result.toList := by
                  exact List.filter_eq_self.mpr fun x hx => by obtain ⟨ i, hi ⟩ := List.mem_iff_get.mp hx; aesop;
                generalize_proofs at *; (
                rw [h_filter_eq])
              generalize_proofs at *; (
              have h_count_eq : List.length (List.filter (fun x => VerinaSpec.isEven x) result.toList) = result.size := by
                rw [ List.filter_eq_self.mpr ] ; aesop;
                intro a ha; obtain ⟨ i, hi ⟩ := List.mem_iff_get.mp ha; aesop;
              generalize_proofs at *; (
              grind +ring));
            rw [ h_count, List.count ];
            rw [ List.countP_filter ];
            -- Since x is even, the condition (a == x && VerinaSpec.isEven a) simplifies to a == x.
            have h_cond : ∀ a : ℤ, a == x && VerinaSpec.isEven a ↔ a == x := by
              -- Since x is even, if a equals x, then a must also be even. Conversely, if a is even and equals x, then obviously a equals x.
              intros a
              simp [hx, VerinaSpec.isEven];
              exact fun h => h.symm ▸ even_iff_two_dvd.mp hx;
            exact List.countP_congr fun a => by specialize h_cond a; aesop;
          grind +ring;
        · rw [ Array.count_eq_zero ];
          intro hx'; obtain ⟨ i, hi ⟩ := Array.getElem_of_mem hx'; specialize h; have := h.1 i; simp_all +decide [ VerinaSpec.isEven ] ;
          exact absurd ( h.1 i ( by linarith [ hi.1, h.2.2 ] ) ) ( by rw [ hi.2 ] ; exact fun ⟨ k, hk ⟩ => by obtain ⟨ m, hm ⟩ := hx; omega );
      · -- Since `result` is a sublist of `arr`, there exists an order-preserving function `f` that maps indices of `result` to indices of `arr`.
        obtain ⟨f, hf⟩ : ∃ f : ℕ → ℕ, (∀ i, i < result.size → f i < arr.size ∧ arr[f i]! = result[i]!) ∧ (∀ i j, i < j → j < result.size → f i < f j) := by
          have h_sublist : result.toList.Sublist arr.toList := h.2.1
          have h_sublist_indices : ∀ {l1 l2 : List ℤ}, l1.Sublist l2 → ∃ f : ℕ → ℕ, (∀ i, i < l1.length → f i < l2.length ∧ l2.get! (f i) = l1.get! i) ∧ (∀ i j, i < j → j < l1.length → f i < f j) := by
            intros l1 l2 h_sublist
            induction' h_sublist with l1 l2 h_sublist ih;
            · exact ⟨ fun _ => 0, by norm_num ⟩;
            · obtain ⟨ f, hf1, hf2 ⟩ := ‹_›; use fun i => f i + 1; aesop;
            · rename_i k hk ih;
              obtain ⟨ f, hf₁, hf₂ ⟩ := ih;
              refine' ⟨ fun i => if i = 0 then 0 else f ( i - 1 ) + 1, _, _ ⟩ <;> simp_all +decide [ Nat.succ_eq_add_one ];
              · intro i hi; rcases i with ( _ | i ) <;> simp_all +decide [ Nat.succ_eq_add_one ] ;
                exact hf₁ i ( Nat.lt_of_succ_lt_succ hi );
              · intro i j hij hj; rcases i with ( _ | i ) <;> rcases j with ( _ | j ) <;> simp_all +decide ;
          convert h_sublist_indices h_sublist using 1;
          simp +decide [ Array.get! ];
          grind;
        exact ⟨ f, hf ⟩;
      · convert h.2.2 using 1;
  · -- To prove the sublist condition, we use the orderPreserved hypothesis.
    have h_sublist : result.toList.Sublist arr.toList := by
      obtain ⟨ f, hf₁, hf₂ ⟩ := h.2.2.1;
      have h_sublist : List.Sublist (List.map (fun i => arr[f i]!) (List.range result.size)) (List.map (fun i => arr[i]!) (List.range arr.size)) := by
        have h_sublist : List.Sublist (List.map (fun i => f i) (List.range result.size)) (List.range arr.size) := by
          have h_sublist : List.Sublist (List.map (fun i => f i) (List.range result.size)) (List.map (fun i => i) (List.range arr.size)) := by
            have h_sorted : List.Sorted (· < ·) (List.map (fun i => f i) (List.range result.size)) := by
              refine' List.pairwise_iff_get.mpr _;
              -- Since $i$ and $j$ are in the Fin type, their values are less than the size of the result array.
              intro i j hij
              have h_lt : i.val < j.val ∧ j.val < result.size := by
                exact ⟨ hij, by simpa using j.2 ⟩;
              simpa using hf₂ _ _ h_lt.1 h_lt.2
            have h_sublist : List.Sublist (List.map (fun i => f i) (List.range result.size)) (List.map (fun i => i) (List.range arr.size)) := by
              have h_perm : List.Perm (List.map (fun i => f i) (List.range result.size)) (List.filter (fun i => i ∈ List.map (fun i => f i) (List.range result.size)) (List.range arr.size)) := by
                rw [ List.perm_iff_count ];
                intro a; by_cases ha : a ∈ List.map ( fun i => f i ) ( List.range result.size ) <;> simp_all +decide [ List.count_eq_zero_of_not_mem ] ;
                rw [ List.count_eq_one_of_mem ];
                · rw [ if_pos ( by obtain ⟨ i, hi, rfl ⟩ := ha; exact hf₁ i hi |>.1 ) ];
                · exact h_sorted.nodup;
                · aesop
              have h_sublist : List.Sublist (List.map (fun i => f i) (List.range result.size)) (List.filter (fun i => i ∈ List.map (fun i => f i) (List.range result.size)) (List.range arr.size)) := by
                have h_sublist : ∀ {l1 l2 : List ℕ}, List.Sorted (· < ·) l1 → List.Sorted (· < ·) l2 → List.Perm l1 l2 → List.Sublist l1 l2 := by
                  intros l1 l2 hl1 hl2 hperm; exact (by
                  have h_sublist : ∀ {l1 l2 : List ℕ}, List.Sorted (· < ·) l1 → List.Sorted (· < ·) l2 → List.Perm l1 l2 → l1 = l2 := by
                    intros l1 l2 hl1 hl2 hperm; exact List.eq_of_perm_of_sorted hperm hl1 hl2;
                  exact h_sublist hl1 hl2 hperm ▸ List.Sublist.refl _);
                apply h_sublist h_sorted;
                · refine' List.Sorted.filter _ _;
                  exact?;
                · assumption;
              exact h_sublist.trans ( by simpa );
            exact h_sublist;
          aesop;
        simpa using h_sublist.map _;
      convert h_sublist using 1;
      · refine' List.ext_get _ _ <;> aesop;
      · refine' List.ext_get _ _ <;> aesop;
    -- Apply the hypothesis `h_sublist` directly to conclude the proof.
    exact ⟨by
    -- Since `LLMSpec.isEven` is equivalent to `VerinaSpec.isEven`, we can conclude that every element in the result array is even.
    have h_even : ∀ i (hi : i < result.size), VerinaSpec.isEven result[i]! := by
      -- Since `LLMSpec.isEven` is equivalent to `VerinaSpec.isEven`, we can conclude that every element in the result array is even by applying the hypothesis `h`.
      intros i hi
      have h_even : LLMSpec.isEven result[i]! := by
        exact h.1 i hi;
      unfold VerinaSpec.isEven; simp +decide [ h_even ] ;
      exact even_iff_two_dvd.mp h_even;
    grind, h_sublist, by
      convert h.2.2.2 using 1⟩

end Proof