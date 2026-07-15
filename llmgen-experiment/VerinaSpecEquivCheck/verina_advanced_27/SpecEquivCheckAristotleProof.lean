/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 4cccf982-e5d4-45bc-8eb0-910c5a128378

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (s1 : String) (s2 : String) : VerinaSpec.longestCommonSubsequence_precond s1 s2 ↔ LLMSpec.precondition s1 s2

- theorem postcondition_equiv (s1 : String) (s2 : String) (result : String) : LLMSpec.precondition s1 s2 →
  (VerinaSpec.longestCommonSubsequence_postcond s1 s2 result ↔ LLMSpec.postcondition s1 s2 result)

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

def longestCommonSubsequence_precond (s1 : String) (s2 : String) : Prop :=
  True

partial def toCharList (s : String) : List Char :=
  s.data

partial def fromCharList (cs : List Char) : String :=
  cs.foldl (fun acc c => acc.push c) ""

partial def lcsAux (xs : List Char) (ys : List Char) : List Char :=
  match xs, ys with
  | [], _ => []
  | _, [] => []
  | x :: xs', y :: ys' =>
    if x == y then
      x :: lcsAux xs' ys'
    else
      let left  := lcsAux xs' (y :: ys')
      let right := lcsAux (x :: xs') ys'
      if left.length >= right.length then left else right

def longestCommonSubsequence_postcond (s1 : String) (s2 : String) (result: String) : Prop :=
  let allSubseq (arr : List Char) := (arr.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse
  let subseqA := allSubseq s1.toList
  let subseqB := allSubseq s2.toList
  let commonSubseq := subseqA.filter (fun l => subseqB.contains l)
  commonSubseq.contains result.toList ∧ commonSubseq.all (fun l => l.length ≤ result.length)

end VerinaSpec

namespace LLMSpec

-- Helper definitions

-- `isSubseqList r s` means `r` is a subsequence of `s`.
-- It is witnessed by an order-preserving index mapping from positions of `r` to positions of `s`.
-- We use natural-number indexing via `List.get!` (safe because we require the indices are in range).
--
-- Note: This definition avoids depending on any particular library name for subsequence.
-- It also avoids mixing `Array` and `List` in specifications; we specify everything over `List Char`.
def isSubseqList (r : List Char) (s : List Char) : Prop :=
  ∃ f : Nat → Nat,
    (∀ (i : Nat), i < r.length → f i < s.length) ∧
    (∀ (i : Nat) (j : Nat), i < j → j < r.length → f i < f j) ∧
    (∀ (i : Nat), i < r.length → r.get! i = s.get! (f i))

def isCommonSubseqList (s1 : List Char) (s2 : List Char) (r : List Char) : Prop :=
  isSubseqList r s1 ∧ isSubseqList r s2

-- `r` is a longest common subsequence iff it is a common subsequence and
-- no other common subsequence is longer.
def isLCSList (s1 : List Char) (s2 : List Char) (r : List Char) : Prop :=
  isCommonSubseqList s1 s2 r ∧
  ∀ (t : List Char), isSubseqList t s1 → isSubseqList t s2 → t.length ≤ r.length

-- No input restrictions.
def precondition (s1 : String) (s2 : String) : Prop :=
  True

def postcondition (s1 : String) (s2 : String) (result : String) : Prop :=
  isLCSList s1.data s2.data result.data

end LLMSpec

section Proof

theorem precondition_equiv (s1 : String) (s2 : String) : VerinaSpec.longestCommonSubsequence_precond s1 s2 ↔ LLMSpec.precondition s1 s2 := by
  -- Since both preconditions are True, their equivalence is trivial.
  simp [VerinaSpec.longestCommonSubsequence_precond, LLMSpec.precondition]

noncomputable section AristotleLemmas

theorem LLMSpec.isSubseqList_iff_sublist (r s : List Char) : LLMSpec.isSubseqList r s ↔ List.Sublist r s := by
  constructor <;> intro h_sublist
  all_goals generalize_proofs at *;
  · obtain ⟨ f, hf₁, hf₂, hf₃ ⟩ := h_sublist;
    have h_sublist : ∃ f' : Fin r.length → Fin s.length, StrictMono f' ∧ ∀ i : Fin r.length, r.get! i.val = s.get! (f' i).val := by
      exact ⟨ fun i => ⟨ f i, hf₁ i i.2 ⟩, fun i j hij => hf₂ _ _ hij ( by simp ), fun i => hf₃ _ i.2 ⟩
    generalize_proofs at *; (
    obtain ⟨ f', hf'₁, hf'₂ ⟩ := h_sublist; have := hf'₁.injective; have := hf'₂; simp_all +decide [ List.sublist_iff_exists_fin_orderEmbedding_get_eq ] ;
    exact ⟨ OrderEmbedding.ofStrictMono f' hf'₁, fun i => rfl ⟩);
  · induction' h_sublist with r s z h;
    · exact ⟨ fun _ => 0, by norm_num ⟩;
    · obtain ⟨ f, hf₁, hf₂, hf₃ ⟩ := ‹_›; use fun i => f i + 1; aesop;
    · obtain ⟨ f, hf₁, hf₂, hf₃ ⟩ := ‹_›; use fun i => if i = 0 then 0 else f ( i - 1 ) + 1; simp_all +decide [ List.get ] ;
      refine' ⟨ _, _, _ ⟩;
      · grind +ring;
      · intro i j hij hj; rcases i with ( _ | i ) <;> rcases j with ( _ | j ) <;> simp_all +decide ;
      · grind

theorem VerinaSpec.mem_foldl_allSubseq_iff (l : List Char) (r : List Char) :
    r ∈ l.foldl (fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] ↔ List.Sublist r l.reverse := by
  induction' l using List.reverseRecOn with l ih generalizing r <;> simp_all +decide [ List.sublist_cons_iff ];
  grind +ring

theorem VerinaSpec.mem_allSubseq_iff (l : List Char) (r : List Char) :
    r ∈ (l.foldl (fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse) ↔ List.Sublist r l := by
  convert VerinaSpec.mem_foldl_allSubseq_iff _ _ using 1;
  rotate_left;
  rotate_left;
  exact?;
  exact r.reverse;
  · aesop;
  · exact?

end AristotleLemmas

theorem postcondition_equiv (s1 : String) (s2 : String) (result : String) : LLMSpec.precondition s1 s2 →
  (VerinaSpec.longestCommonSubsequence_postcond s1 s2 result ↔ LLMSpec.postcondition s1 s2 result) := by
  use fun _ => ?_;
  constructor <;> intro h;
  · constructor;
    · unfold VerinaSpec.longestCommonSubsequence_postcond at h;
      constructor <;> simp_all +decide [ VerinaSpec.mem_allSubseq_iff ];
      · exact LLMSpec.isSubseqList_iff_sublist _ _ |>.2 h.1.1;
      · exact LLMSpec.isSubseqList_iff_sublist _ _ |>.2 h.1.2;
    · obtain ⟨ h₁, h₂ ⟩ := h;
      intro t ht₁ ht₂; contrapose! h₂; simp_all +decide [ LLMSpec.isSubseqList_iff_sublist ] ;
      use t.reverse; simp_all +decide [ List.Sublist ] ; (
      exact ⟨ by simpa using VerinaSpec.mem_foldl_allSubseq_iff _ _ |>.2 ( by simpa using ht₁.reverse ), by simpa using VerinaSpec.mem_foldl_allSubseq_iff _ _ |>.2 ( by simpa using ht₂.reverse ), h₂ ⟩);
  · constructor;
    · -- Since `result` is a common subsequence of `s1` and `s2`, it must be a sublist of both `s1` and `s2`.
      have h_subseq : List.Sublist result.toList s1.toList ∧ List.Sublist result.toList s2.toList := by
        exact ⟨ LLMSpec.isSubseqList_iff_sublist _ _ |>.1 h.1.1, LLMSpec.isSubseqList_iff_sublist _ _ |>.1 h.1.2 ⟩;
      simp_all +decide [ VerinaSpec.mem_allSubseq_iff ];
    · have := h.2;
      simp_all +decide [ LLMSpec.isSubseqList_iff_sublist ];
      contrapose! this;
      obtain ⟨ t, ht₁, ht₂, ht₃ ⟩ := this;
      use t.reverse;
      have h_sublist : ∀ (l : List Char) (t : List Char), t ∈ List.foldl (fun (acc : List (List Char)) (x : Char) => acc ++ List.map (fun (sub : List Char) => x :: sub) acc) [[]] l → t.reverse.Sublist l := by
        intros l t ht; induction' l using List.reverseRecOn with l ih generalizing t <;> aesop;
      exact ⟨ h_sublist _ _ ht₁, h_sublist _ _ ht₂, by simpa using ht₃ ⟩

end Proof