/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 67c8a9b1-ea52-45f5-bbff-5505f45b71bd

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int) (b : Array Int) : VerinaSpec.LongestCommonSubsequence_precond a b ↔ LLMSpec.precondition a b

- theorem postcondition_equiv (a : Array Int) (b : Array Int) (result : Int) : LLMSpec.precondition a b →
  (VerinaSpec.LongestCommonSubsequence_postcond a b result ↔ LLMSpec.postcondition a b result)

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

def LongestCommonSubsequence_precond (a : Array Int) (b : Array Int) : Prop :=
  True

def intMax (x y : Int) : Int :=
  if x < y then y else x

def LongestCommonSubsequence_postcond (a : Array Int) (b : Array Int) (result: Int) : Prop :=
  let allSubseq (arr : Array Int) := (arr.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse
  let subseqA := allSubseq a
  let subseqB := allSubseq b
  let commonSubseqLens := subseqA.filter (fun l => subseqB.contains l) |>.map (·.length)
  commonSubseqLens.contains result ∧ commonSubseqLens.all (· ≤ result)

end VerinaSpec

namespace LLMSpec

-- `idxs` is a valid index embedding for witnessing that `sub` is a subsequence of `sup`.
-- Intuition: `idxs` lists the positions in `sup` from which we read out the elements of `sub`.

def ValidEmbedding (sub : Array Int) (sup : Array Int) (idxs : Array Nat) : Prop :=
  idxs.size = sub.size ∧
  (∀ i : Nat, i < idxs.size → idxs[i]! < sup.size) ∧
  (∀ i : Nat, i + 1 < idxs.size → idxs[i]! < idxs[i + 1]!) ∧
  (∀ i : Nat, i < sub.size → sub[i]! = sup[idxs[i]!]!)

-- `sub` is a subsequence of `sup`.
def IsSubsequence (sub : Array Int) (sup : Array Int) : Prop :=
  ∃ idxs : Array Nat, ValidEmbedding sub sup idxs

-- `c` is a common subsequence of `a` and `b`.
def IsCommonSubsequence (a : Array Int) (b : Array Int) (c : Array Int) : Prop :=
  IsSubsequence c a ∧ IsSubsequence c b

-- There are no restrictions on inputs.
def precondition (a : Array Int) (b : Array Int) : Prop :=
  True

-- The result is the maximum achievable length among common subsequences.
-- We express maximality and existence using a witness length `k : Nat` and `result = Int.ofNat k`.

def postcondition (a : Array Int) (b : Array Int) (result : Int) : Prop :=
  (∃ k : Nat,
    result = Int.ofNat k ∧
    k ≤ Nat.min a.size b.size ∧
    (∃ c : Array Int, IsCommonSubsequence a b c ∧ c.size = k) ∧
    (∀ c : Array Int, IsCommonSubsequence a b c → c.size ≤ k))

end LLMSpec

section Proof

theorem precondition_equiv (a : Array Int) (b : Array Int) : VerinaSpec.LongestCommonSubsequence_precond a b ↔ LLMSpec.precondition a b := by
  -- Since both preconditions are True, their equivalence is trivial.
  simp [VerinaSpec.LongestCommonSubsequence_precond, LLMSpec.precondition]

noncomputable section AristotleLemmas

/-
The list of subsequences generated by the fold operation in VerinaSpec corresponds exactly to the set of all sublists of the input array.
-/
lemma verina_subseqs_iff_sublist (a : Array Int) (l : List Int) :
  l ∈ (a.foldl (fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse) ↔ List.Sublist l a.toList := by
  -- We can prove this by induction on the length of `a`.
  induction' a using Array.recOn with a ih generalizing l;
  induction' a using List.reverseRecOn with a ih generalizing l <;> simp_all +decide [ List.sublist_cons_iff ];
  constructor <;> intro h <;> simp_all +decide [ List.sublist_append_iff ];
  · grind +ring;
  · rcases h with ⟨ l₁, l₂, rfl, hl₁, rfl | rfl ⟩ <;> simp_all +decide [ List.sublist_append_iff ]

/-
The subsequence definition in LLMSpec (based on valid index embeddings) is equivalent to the standard List.Sublist relation.
-/
lemma llm_subseq_iff_sublist (a : Array Int) (c : Array Int) :
  LLMSpec.IsSubsequence c a ↔ List.Sublist c.toList a.toList := by
  constructor <;> intro h;
  · obtain ⟨ idxs, hidxs ⟩ := h;
    have h_sublist : ∃ f : Fin c.size → Fin a.size, StrictMono f ∧ ∀ i, c[i]! = a[f i]! := by
      have := hidxs.2.2.1;
      have h_sublist : ∀ i j : Fin c.size, i < j → idxs[i]! < idxs[j]! := by
        intro i j hij;
        induction' j with j hj ih;
        induction' j with j hj generalizing i;
        · tauto;
        · rcases eq_or_lt_of_le ( show i ≤ ⟨ j, by linarith ⟩ from Nat.le_of_lt_succ hij ) with rfl | hij <;> [ tauto; exact lt_trans ( by solve_by_elim ) ( this _ <| by linarith [ hidxs.1 ] ) ];
          exact this _ ( by linarith [ hidxs.1 ] );
      use fun i => ⟨ idxs[i]!, by
        exact hidxs.2.1 i ( by linarith [ Fin.is_lt i, hidxs.1 ] ) ⟩
      generalize_proofs at *;
      exact ⟨ fun i j hij => h_sublist i j hij, fun i => hidxs.2.2.2 i i.2 ⟩;
    obtain ⟨ f, hf_mono, hf_eq ⟩ := h_sublist;
    have h_sublist : List.Sublist (List.map (fun i => a[f i]!) (List.finRange c.size)) (List.map (fun i => a[i]!) (List.finRange a.size)) := by
      have h_sublist : List.Sublist (List.map (fun i => f i) (List.finRange c.size)) (List.finRange a.size) := by
        have h_subseq : List.Sublist (List.map f (List.finRange c.size)) (List.map (fun i => i) (List.finRange a.size)) := by
          have h_sorted : List.Sorted (· < ·) (List.map f (List.finRange c.size)) := by
            exact List.pairwise_iff_get.mpr ( by aesop ) ;
          have h_subseq : List.Sublist (List.map f (List.finRange c.size)) (List.map (fun i => i) (List.finRange a.size)) := by
            have h_perm : List.Perm (List.map f (List.finRange c.size)) (List.map (fun i => i) (List.finRange a.size) |>.filter (fun i => i ∈ List.map f (List.finRange c.size))) := by
              rw [ List.perm_iff_count ];
              intro i; by_cases hi : i ∈ List.map f ( List.finRange c.size ) <;> simp_all +decide [ List.count_eq_zero_of_not_mem ] ;
              rw [ List.count_eq_one_of_mem ];
              · exact h_sorted.nodup;
              · aesop
            have h_subseq : List.Sublist (List.filter (fun i => i ∈ List.map f (List.finRange c.size)) (List.map (fun i => i) (List.finRange a.size))) (List.map (fun i => i) (List.finRange a.size)) := by
              exact?
            generalize_proofs at *; (
            have h_subseq : List.Sublist (List.map f (List.finRange c.size)) (List.filter (fun i => i ∈ List.map f (List.finRange c.size)) (List.map (fun i => i) (List.finRange a.size))) := by
              have h_perm : List.Perm (List.map f (List.finRange c.size)) (List.filter (fun i => i ∈ List.map f (List.finRange c.size)) (List.map (fun i => i) (List.finRange a.size))) := h_perm
              have h_sorted : List.Sorted (· < ·) (List.map f (List.finRange c.size)) := h_sorted
              have h_sorted_filter : List.Sorted (· < ·) (List.filter (fun i => i ∈ List.map f (List.finRange c.size)) (List.map (fun i => i) (List.finRange a.size))) := by
                exact List.Pairwise.filter _ ( List.pairwise_iff_get.mpr <| by aesop )
              exact List.eq_of_perm_of_sorted h_perm h_sorted h_sorted_filter ▸ List.Sublist.refl _
            generalize_proofs at *; (
            exact h_subseq.trans ‹_›))
          generalize_proofs at *; (
          exact h_subseq)
        generalize_proofs at *; (
        aesop)
      generalize_proofs at *; (
      convert h_sublist.map _ using 1 ; aesop);
    convert h_sublist using 1 <;> simp +decide [ ← hf_eq ];
    · refine' List.ext_get _ _ <;> simp +decide [ ← hf_eq ];
      grind;
    · refine' List.ext_get _ _ <;> aesop;
  · -- By definition of `IsSubsequence`, there exists an index embedding `idxs` such that `c` is a sublist of `a` and `idxs` maps the positions of `c` in `a`.
    obtain ⟨idxs, hidxs⟩ : ∃ idxs : List ℕ, idxs.length = c.size ∧ (∀ i : ℕ, i < idxs.length → idxs[i]! < a.size) ∧ (∀ i : ℕ, i + 1 < idxs.length → idxs[i]! < idxs[i + 1]!) ∧ (∀ i : ℕ, i < c.size → c[i]! = a[idxs[i]!]!) := by
      have h_sublist : ∀ {l1 l2 : List ℤ}, l1.Sublist l2 → ∃ idxs : List ℕ, idxs.length = l1.length ∧ (∀ i : ℕ, i < idxs.length → idxs[i]! < l2.length) ∧ (∀ i : ℕ, i + 1 < idxs.length → idxs[i]! < idxs[i + 1]!) ∧ (∀ i : ℕ, i < l1.length → l1[i]! = l2[idxs[i]!]!) := by
        intros l1 l2 h_sublist
        induction' l1 with x l1 ih generalizing l2 <;> induction' l2 with y l2 ih' <;> simp_all +decide [ List.sublist_cons_iff ];
        rcases h_sublist with ( h | ⟨ rfl, h ⟩ );
        · obtain ⟨ idxs, hidxs ⟩ := ih' h;
          use idxs.map (fun i => i + 1);
          grind;
        · obtain ⟨ idxs, hidxs₁, hidxs₂, hidxs₃, hidxs₄ ⟩ := ih h; use 0 :: List.map ( fun i => i + 1 ) idxs; simp_all +decide [ List.get ] ;
          refine' ⟨ _, _, _ ⟩ <;> intro i hi <;> rcases i with ( _ | i ) <;> simp_all +decide [ List.get ];
          grind +ring
      generalize_proofs at *; (
      grind);
    refine' ⟨ idxs.toArray, _, _, _, _ ⟩ <;> aesop

end AristotleLemmas

theorem postcondition_equiv (a : Array Int) (b : Array Int) (result : Int) : LLMSpec.precondition a b →
  (VerinaSpec.LongestCommonSubsequence_postcond a b result ↔ LLMSpec.postcondition a b result) := by
  -- By definition of `VerinaSpec.LongestCommonSubsequence_postcond` and `LLMSpec.postcondition`, we need to show that the two conditions are equivalent. We'll use the fact that the list of subsequences generated by the fold operation in `VerinaSpec` corresponds exactly to the set of all sublists of the input array.
  have h_subseqs : ∀ l : List Int, l ∈ (a.foldl (fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse) ↔ List.Sublist l a.toList := by
    exact?
  have h_subseqs_b : ∀ l : List Int, l ∈ (b.foldl (fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse) ↔ List.Sublist l b.toList := by
    exact?
  simp_all +decide [ VerinaSpec.LongestCommonSubsequence_postcond, LLMSpec.postcondition ];
  refine' fun _ => ⟨ _, _ ⟩;
  · rintro ⟨ ⟨ l, hl₁, hl₂ ⟩, hl₃ ⟩;
    refine' ⟨ l.length, hl₂.symm, ⟨ _, _ ⟩, _, _ ⟩;
    · simpa using hl₁.1.length_le;
    · simpa using hl₁.2.length_le;
    · refine' ⟨ l.toArray, _, _ ⟩ <;> simp_all +decide [ LLMSpec.IsCommonSubsequence ];
      exact ⟨ by simpa using llm_subseq_iff_sublist a l.toArray |>.2 hl₁.1, by simpa using llm_subseq_iff_sublist b l.toArray |>.2 hl₁.2 ⟩;
    · intro c hc; obtain ⟨ hc₁, hc₂ ⟩ := hc; simp_all +decide [ llm_subseq_iff_sublist ] ;
      grind;
  · rintro ⟨ k, rfl, ⟨ hk₁, hk₂ ⟩, ⟨ c, hc₁, hc₂ ⟩, hc₃ ⟩;
    refine' ⟨ ⟨ c.toList, ⟨ _, _ ⟩, _ ⟩, _ ⟩;
    · exact llm_subseq_iff_sublist a c |>.1 hc₁.1;
    · exact llm_subseq_iff_sublist _ _ |>.1 hc₁.2;
    · aesop;
    · contrapose! hc₃;
      obtain ⟨ x, hx₁, hx₂, hx₃ ⟩ := hc₃;
      refine' ⟨ x.reverse.toArray, _, _ ⟩ <;> simp_all +decide [ LLMSpec.IsCommonSubsequence ];
      exact ⟨ by simpa using llm_subseq_iff_sublist _ _ |>.2 ( h_subseqs _ |>.1 ( by simpa using hx₁ ) ), by simpa using llm_subseq_iff_sublist _ _ |>.2 hx₂ ⟩

end Proof