/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 7b91c10d-a777-4e99-bd9b-2f7faad9077a

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

-- Helper: strictly increasing indices for an index array.
def StrictlyIncreasing (idxs : Array Nat) : Prop :=
  ∀ (j : Nat), j + 1 < idxs.size → idxs[j]! < idxs[j + 1]!

-- Helper: s is a subsequence of arr, witnessed by an index array idxs.
def SubseqWitness (s : Array Int) (arr : Array Int) (idxs : Array Nat) : Prop :=
  idxs.size = s.size ∧
  StrictlyIncreasing idxs ∧
  (∀ (j : Nat), j < s.size → idxs[j]! < arr.size ∧ s[j]! = arr[idxs[j]!]!)

-- Helper: array subsequence relation.
def IsSubsequence (s : Array Int) (arr : Array Int) : Prop :=
  ∃ (idxs : Array Nat), SubseqWitness s arr idxs

-- Precondition: no restrictions on inputs.
def precondition (a : Array Int) (b : Array Int) : Prop :=
  True

-- Postcondition: result is the maximum possible length of any common subsequence.
-- Note: result is Int, but array sizes are Nat, so we relate them via Int.ofNat and result.toNat.
def postcondition (a : Array Int) (b : Array Int) (result : Int) : Prop :=
  result ≥ 0 ∧
  (∃ (s : Array Int), IsSubsequence s a ∧ IsSubsequence s b ∧ result = Int.ofNat s.size) ∧
  (∀ (t : Array Int), IsSubsequence t a ∧ IsSubsequence t b → (Int.ofNat t.size) ≤ result)

end LLMSpec

section Proof

theorem precondition_equiv (a : Array Int) (b : Array Int) : VerinaSpec.LongestCommonSubsequence_precond a b ↔ LLMSpec.precondition a b := by
  -- Since both preconditions are defined as True, their equivalence is trivial.
  simp [VerinaSpec.LongestCommonSubsequence_precond, LLMSpec.precondition]

noncomputable section AristotleLemmas

/-
`VerinaSpec_allSubseq` computes the list of all subsequences of an array `a`.
This theorem states that a list `s` is in `VerinaSpec_allSubseq a` if and only if `s` is a sublist of `a.toList`.
-/
def VerinaSpec_allSubseq (arr : Array Int) : List (List Int) :=
  (arr.foldl (fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]]).map List.reverse

theorem VerinaSpec_mem_allSubseq_iff_sublist (a : Array Int) (s : List Int) :
  s ∈ VerinaSpec_allSubseq a ↔ List.Sublist s a.toList := by
    -- By definition of `VerinaSpec_allSubseq`, we know that `s ∈ VerinaSpec_allSubseq a` if and only if `s` is a sublist of `a.toList`.
    have h_eq : s ∈ VerinaSpec_allSubseq a ↔ s ∈ (List.foldl (fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] a.toList |>.map List.reverse) := by
      unfold VerinaSpec_allSubseq; aesop;
    -- By definition of `List.foldl`, we know that `List.foldl (fun acc x => acc ++ List.map (fun sub => x :: sub) acc) [[]] a.toList` is the list of all subsequences of `a.toList`.
    have h_foldl : List.foldl (fun acc x => acc ++ List.map (fun sub => x :: sub) acc) [[]] a.toList = List.map List.reverse (List.sublists a.toList) := by
      induction' a.toList using List.reverseRecOn with x xs ih <;> simp_all +decide [ List.sublists_cons ];
    simp_all +decide [ List.mem_map ]

/-
`LLMSpec.IsSubsequence s a` holds if and only if `s.toList` is a sublist of `a.toList`.
This connects the index-witness definition of subsequence with the standard inductive definition.
-/
theorem LLMSpec_IsSubsequence_iff_sublist (s : Array Int) (a : Array Int) :
  LLMSpec.IsSubsequence s a ↔ List.Sublist s.toList a.toList := by
    constructor;
    · -- Given that there exists an array idxs such that SubseqWitness s a idxs holds, we can construct a list of indices that are strictly increasing and map to s.
      intro h
      obtain ⟨idxs, hidxs⟩ := h
      have h_order_embedding : ∃ f : Fin s.size → Fin a.size, StrictMono f ∧ ∀ j, s[j]! = a[f j]! := by
        use fun j => ⟨ idxs[j]!, by
          exact hidxs.2.2 j ( Fin.is_lt j ) |>.1 ⟩
        generalize_proofs at *;
        refine' ⟨ fun i j hij => _, fun j => _ ⟩;
        · have := hidxs.2.1;
          have h_lt : ∀ k l : Fin s.size, k < l → idxs[k]! < idxs[l]! := by
            intros k l hkl
            have h_lt : ∀ m n : ℕ, m < n → n < idxs.size → idxs[m]! < idxs[n]! := by
              intros m n hmn hn
              induction' hmn with m n hmn ih;
              · exact this m ( by linarith );
              · exact lt_trans ( hmn ( Nat.lt_of_succ_lt hn ) ) ( this _ ( by simpa ) );
            exact h_lt _ _ hkl ( by simpa [ hidxs.1 ] );
          exact h_lt i j hij;
        · exact hidxs.2.2 _ j.2 |>.2;
      obtain ⟨ f, hf_mono, hf_eq ⟩ := h_order_embedding;
      convert List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr _;
      refine' ⟨ _, _ ⟩;
      exact?;
      aesop;
    · intro h_sublist
      obtain ⟨f, hf⟩ : ∃ f : Fin s.size ↪o Fin a.size, ∀ j : Fin s.size, s[j] = a[f j] := by
        have := @List.sublist_iff_exists_fin_orderEmbedding_get_eq ℤ;
        aesop;
      refine' ⟨ _, _, _, _ ⟩;
      exact Array.ofFn fun j => f j;
      · simp +decide [ Array.size_ofFn ];
      · intro j hj;
        convert f.lt_iff_lt.2 ( show ( ⟨ j, by
                                  exact Nat.lt_of_succ_lt ( by simpa using hj ) ⟩ : Fin s.size ) < ⟨ j + 1, by
                                  aesop ⟩ from Nat.lt_succ_self _ ) using 1
        generalize_proofs at *;
        simp +decide [ Fin.add_def, Nat.mod_eq_of_lt, * ];
      · intro j hj; have := hf ⟨ j, hj ⟩ ; simp_all +decide [ Fin.cast_val_eq_self ] ;

end AristotleLemmas

theorem postcondition_equiv (a : Array Int) (b : Array Int) (result : Int) : LLMSpec.precondition a b →
  (VerinaSpec.LongestCommonSubsequence_postcond a b result ↔ LLMSpec.postcondition a b result) := by
  rintro -;
  constructor <;> intro h;
  · obtain ⟨s, hs⟩ : ∃ s : List Int, s ∈ VerinaSpec_allSubseq a ∧ s ∈ VerinaSpec_allSubseq b ∧ result = s.length ∧ ∀ t ∈ VerinaSpec_allSubseq a, t ∈ VerinaSpec_allSubseq b → t.length ≤ result := by
      unfold VerinaSpec.LongestCommonSubsequence_postcond at h;
      grind;
    refine' ⟨ by linarith, _, _ ⟩;
    · use s.toArray;
      exact ⟨ by simpa using LLMSpec_IsSubsequence_iff_sublist _ _ |>.2 ( VerinaSpec_mem_allSubseq_iff_sublist _ _ |>.1 hs.1 ), by simpa using LLMSpec_IsSubsequence_iff_sublist _ _ |>.2 ( VerinaSpec_mem_allSubseq_iff_sublist _ _ |>.1 hs.2.1 ), by simpa using hs.2.2.1 ⟩;
    · simp_all +decide [ LLMSpec_IsSubsequence_iff_sublist ];
      intro t ht₁ ht₂; specialize hs; have := hs.2.2.2 t.toList; simp_all +decide [ VerinaSpec_mem_allSubseq_iff_sublist ] ;
  · obtain ⟨ s, hs ⟩ := h.2.1;
    -- Since `s` is a common subsequence of `a` and `b`, `s.toList` is in both `subseqA` and `subseqB`.
    have h_subseqA : s.toList ∈ VerinaSpec_allSubseq a := by
      exact VerinaSpec_mem_allSubseq_iff_sublist a s.toList |>.2 ( LLMSpec_IsSubsequence_iff_sublist s a |>.1 hs.1 )
    have h_subseqB : s.toList ∈ VerinaSpec_allSubseq b := by
      convert VerinaSpec_mem_allSubseq_iff_sublist b s.toList |>.2 _;
      exact LLMSpec_IsSubsequence_iff_sublist s b |>.1 hs.2.1;
    have h_commonSubseqLens : ∀ t ∈ VerinaSpec_allSubseq a, t ∈ VerinaSpec_allSubseq b → t.length ≤ result := by
      intros t htA htB
      have h_subseqA : List.Sublist t a.toList := by
        exact?
      have h_subseqB : List.Sublist t b.toList := by
        exact?
      have h_subseq : LLMSpec.IsSubsequence (t.toArray) a ∧ LLMSpec.IsSubsequence (t.toArray) b := by
        exact ⟨ by simpa using LLMSpec_IsSubsequence_iff_sublist _ _ |>.2 h_subseqA, by simpa using LLMSpec_IsSubsequence_iff_sublist _ _ |>.2 h_subseqB ⟩
      have h_max : (t.length : ℤ) ≤ result := by
        exact h.2.2 _ ⟨ h_subseq.1, h_subseq.2 ⟩
      exact h_max;
    constructor;
    · grind;
    · grind

end Proof