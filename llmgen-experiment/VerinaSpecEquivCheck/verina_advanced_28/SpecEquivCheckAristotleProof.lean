/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 4ac95494-c59c-4294-a788-c0390a86ae9d

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (nums : List Int) : VerinaSpec.longestConsecutive_precond nums ↔ LLMSpec.precondition nums

- theorem postcondition_equiv (nums : List Int) (result : Nat) : LLMSpec.precondition nums →
  (VerinaSpec.longestConsecutive_postcond nums result ↔ LLMSpec.postcondition nums result)

At Harmonic, we use a modified version of the `generalize_proofs` tactic.
For compatibility, we include this tactic at the start of the file.
If you add the comment "-- Harmonic `generalize_proofs` tactic" to your file, we will not do this.
-/

import Mathlib.Tactic

import Std.Data.HashSet

import Mathlib


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

open Std

def longestConsecutive_precond (nums : List Int) : Prop :=
  List.Nodup nums

def isConsecutive (seq : List Int) : Bool :=
  seq.length = 0 ∨ seq.zipIdx.all (fun (x, i) => x = i + seq[0]!)

def longestConsecutive_postcond (nums : List Int) (result: Nat) : Prop :=
  let sorted_nums := nums.mergeSort
  let consec_sublist_lens := List.range nums.length |>.flatMap (fun start =>
    List.range (nums.length - start + 1) |>.map (fun len => sorted_nums.extract start (start + len))) |>.filter isConsecutive |>.map (·.length)
  (nums = [] → result = 0) ∧
  (nums ≠ [] → consec_sublist_lens.contains result ∧ consec_sublist_lens.all (· ≤ result))

end VerinaSpec

namespace LLMSpec

-- An interval [a,b] is fully contained in nums if every integer k with a ≤ k ≤ b appears in nums.
-- We include the side condition a ≤ b to avoid degenerate "backwards" intervals.
def intervalContained (nums : List Int) (a : Int) (b : Int) : Prop :=
  a ≤ b ∧ ∀ (k : Int), a ≤ k ∧ k ≤ b → k ∈ nums

-- The length of an integer interval [a,b] as a natural number.
-- This is only meaningful when a ≤ b; the definition uses Int.toNat, so we pair it with a ≤ b in specs.
def intervalLength (a : Int) (b : Int) : Nat :=
  Int.toNat (b - a + 1)

def precondition (nums : List Int) : Prop :=
  nums.Nodup

def postcondition (nums : List Int) (result : Nat) : Prop :=
  (nums = [] → result = 0) ∧
  (nums ≠ [] →
    (∃ (a : Int) (b : Int),
      intervalContained nums a b ∧
      result = intervalLength a b) ∧
    (∀ (a : Int) (b : Int),
      intervalContained nums a b → intervalLength a b ≤ result) ∧
    (1 ≤ result) ∧
    (result ≤ nums.length))

end LLMSpec

section Proof

theorem precondition_equiv (nums : List Int) : VerinaSpec.longestConsecutive_precond nums ↔ LLMSpec.precondition nums := by
  -- The longestConsecutive_precond is defined as List.Nodup nums, and the LLMSpec.precondition is also defined as List.Nodup nums. Therefore, they are equivalent.
  simp [VerinaSpec.longestConsecutive_precond, LLMSpec.precondition]

noncomputable section AristotleLemmas

/-
isConsecutive checks if the list is an arithmetic progression with step 1.
-/
theorem VerinaSpec.isConsecutive_iff (l : List Int) :
  VerinaSpec.isConsecutive l ↔ ∃ a : Int, l = (List.range l.length).map (fun (i : Nat) => a + ↑i) := by
    constructor <;> intro h;
    · by_cases h_empty : l = [];
      · aesop;
      · use l.get! 0;
        refine' List.ext_get _ _ <;> simp_all +decide [ VerinaSpec.isConsecutive ];
        intro n hn; specialize h ( l[n] ) n; simp_all +decide [ List.mem_iff_get ] ; ring;
        convert h ⟨ n, by simpa using hn ⟩ rfl rfl using 1 ; ring;
    · rcases h with ⟨ a, ha ⟩ ; rw [ ha ] ; simp +decide [ VerinaSpec.isConsecutive ] ;
      grind +ring

/-
If a consecutive sequence of integers is a sublist of a strictly sorted list, it must be a contiguous sublist (infix).
-/
theorem consecutive_sublist_is_infix {l : List Int} (h_sorted : l.Sorted (· < ·)) {s : List Int} (h_consec : VerinaSpec.isConsecutive s) (h_sub : s <:+ l) : s <:+: l := by
  obtain ⟨ k, hk ⟩ := h_sub;
  -- Since $k ++ s = l$, we can take $t = k$ to satisfy the definition of sublist.
  use k;
  exact ⟨ [ ], by simpa [ hk ] ⟩

/-
If a strictly sorted list of integers contains a sequence of n consecutive integers, then that sequence appears as a contiguous sublist.
-/
theorem sorted_contains_consecutive_implies_infix (l : List Int) (h_sorted : l.Sorted (· < ·)) (a : Int) (n : Nat) (h_mem : ∀ i : Nat, i < n → a + i ∈ l) :
  List.IsInfix ((List.range n).map (fun i => a + ↑i)) l := by
    -- Since $l$ is sorted, the list $l$ must contain the sequence $[a, a+1, ..., a+n-1]$ in order.
    have h_order : ∀ i j : ℕ, i < j → i < n → j < n → a + i < a + j := by
      aesop;
    -- Since $l$ is sorted, the elements $a, a+1, \ldots, a+n-1$ must appear in $l$ in increasing order.
    have h_elements : List.map (fun i : ℕ => a + i) (List.range n) <+: l.drop (List.idxOf (a + 0) l) := by
      have h_elements : ∀ i < n, List.idxOf (a + i) l = List.idxOf (a + 0) l + i := by
        intro i hi
        induction' i with i ih;
        · norm_num;
        · have h_succ : List.idxOf (a + (i + 1)) l > List.idxOf (a + i) l := by
            have h_succ : ∀ {x y : ℤ}, x ∈ l → y ∈ l → x < y → List.idxOf x l < List.idxOf y l := by
              intros x y hx hy hxy;
              have h_succ : ∀ {l : List ℤ}, List.Sorted (· < ·) l → ∀ {x y : ℤ}, x ∈ l → y ∈ l → x < y → List.idxOf x l < List.idxOf y l := by
                intros l hl x y hx hy hxy; induction' l with hd tl ih generalizing x y <;> simp_all +decide [ List.idxOf_cons ] ;
                grind;
              exact h_succ h_sorted hx hy hxy;
            exact h_succ ( h_mem i ( Nat.lt_of_succ_lt hi ) ) ( h_mem ( i + 1 ) hi ) ( by simp );
          have h_succ : ∀ j, List.idxOf (a + i) l < j → j < List.idxOf (a + (i + 1)) l → a + i < l.get! j ∧ l.get! j < a + (i + 1) := by
            intros j hj₁ hj₂
            have h_bounds : ∀ k, List.idxOf (a + i) l < k → k < List.idxOf (a + (i + 1)) l → a + i < l.get! k ∧ l.get! k < a + (i + 1) := by
              intros k hk₁ hk₂
              have h_bounds : ∀ m n, m < n → m < l.length → n < l.length → l.get! m < l.get! n := by
                intros m n hmn hm hn; exact (by
                have := List.pairwise_iff_get.mp h_sorted;
                simpa [ hm, hn ] using this ⟨ m, hm ⟩ ⟨ n, hn ⟩ hmn)
              have h_bounds : l.get! (List.idxOf (a + i) l) = a + i ∧ l.get! (List.idxOf (a + (i + 1)) l) = a + (i + 1) := by
                have h_bounds : ∀ x ∈ l, l.get! (List.idxOf x l) = x := by
                  aesop;
                exact ⟨ h_bounds _ ( h_mem _ ( Nat.lt_of_succ_lt hi ) ), h_bounds _ ( by simpa using h_mem _ hi ) ⟩;
              grind;
            exact h_bounds j hj₁ hj₂;
          contrapose! h_succ;
          use List.idxOf (a + i) l + 1;
          simp +zetaDelta at *;
          exact ⟨ lt_of_le_of_ne ( by linarith ) ( Ne.symm <| by omega ), fun h => by linarith ⟩;
      have h_elements : ∀ i < n, List.get! (List.drop (List.idxOf (a + 0) l) l) i = a + i := by
        intro i hi; specialize h_elements i hi; simp_all +decide [ List.get?_eq_get ] ;
        rw [ ← h_elements, List.getElem?_idxOf ] ; aesop;
        exact h_mem i hi;
      refine' ⟨ List.drop ( n : ℕ ) ( List.drop ( List.idxOf ( a + 0 ) l ) l ), _ ⟩;
      refine' List.ext_get _ _ <;> simp_all +decide [ List.get ];
      · rw [ add_comm, tsub_add_eq_add_tsub ];
        · rw [ Nat.add_sub_add_right ];
        · contrapose! h_elements;
          refine' ⟨ n - 1, _, _ ⟩ <;> rcases n with ( _ | _ | n ) <;> simp_all +decide [ List.getElem?_eq_none ];
          · grind;
          · grind +ring;
          · exact h_elements.not_le ( Nat.succ_le_of_lt ( List.idxOf_lt_length_iff.mpr h_mem ) );
          · grind;
      · intro i hi₁ hi₂; by_cases hi₃ : i < n <;> simp_all +decide [ List.getElem_append ] ;
        convert h_elements i hi₃ |> Eq.symm using 1;
        rw [ List.getElem?_eq_getElem ] ; aesop;
    obtain ⟨ k, hk ⟩ := h_elements;
    use l.take (List.idxOf (a + 0) l);
    exact ⟨ k, by rw [ List.append_assoc, hk, List.take_append_drop ] ⟩

theorem VerinaSpec.consecutive_bounds_implies_mem (sub : List Int) (a b : Int)
  (h_consec : VerinaSpec.isConsecutive sub)
  (h_head : sub.head? = some a)
  (h_last : sub.getLast? = some b) :
  ∀ k, a ≤ k ∧ k ≤ b → k ∈ sub := by
    -- We'll use that sub is an arithmetic progression with step 1 to rewrite it in terms of a and some length n.
    obtain ⟨a, n, hn⟩ : ∃ a n : ℤ, sub = List.map (fun i : ℕ => a + i) (List.range (sub.length)) := by
      have := VerinaSpec.isConsecutive_iff sub |>.1 h_consec; aesop;
    rw [ hn ] at h_head h_last ⊢; simp +decide [ List.range_succ_eq_map ] at h_head h_last ⊢;
    rcases h_head with ⟨ k₁, hk₁, rfl ⟩ ; rcases h_last with ⟨ k₂, hk₂, rfl ⟩ ; rw [ List.getLast?_range ] at *; norm_num at *;
    intro k hk₁ hk₂; use Int.toNat ( k - a ) ; rcases sub with ( _ | ⟨ _, _ | sub ⟩ ) <;> norm_num [ List.range_succ_eq_map ] at * ; omega;
    grind

theorem VerinaSpec.intervalContained_iff_infix (nums : List Int) (h_nodup : nums.Nodup) (a b : Int) :
  LLMSpec.intervalContained nums a b ↔
  ∃ sub, sub <:+: nums.mergeSort ∧ VerinaSpec.isConsecutive sub ∧ sub.length = LLMSpec.intervalLength a b ∧ sub.head? = some a ∧ sub.getLast? = some b := by
    constructor;
    · intro h_int_contained
      use List.map (fun i : ℕ => a + i) (List.range (Int.toNat (b - a + 1)));
      refine' ⟨ _, _, _, _, _ ⟩;
      · have h_sorted : List.Sorted (· < ·) (nums.mergeSort (· ≤ ·)) := by
          have h_sorted : List.Sorted (· ≤ ·) (nums.mergeSort (· ≤ ·)) := by
            exact?;
          have h_sorted : List.Nodup (nums.mergeSort (· ≤ ·)) := by
            exact?;
          exact?;
        convert sorted_contains_consecutive_implies_infix _ h_sorted _ _ _ using 1;
        intro i hi; have := h_int_contained.2 ( a + i ) ⟨ by linarith, by linarith [ Int.toNat_of_nonneg ( by linarith [ h_int_contained.1 ] : 0 ≤ b - a + 1 ) ] ⟩ ; aesop;
      · rw [ VerinaSpec.isConsecutive_iff ];
        aesop;
      · unfold LLMSpec.intervalLength; aesop;
      · rcases h_int_contained with ⟨ h₁, h₂ ⟩ ; rcases n : Int.toNat ( b - a + 1 ) with ( _ | _ | n ) <;> simp_all +decide [ List.range_succ_eq_map ];
        linarith;
      · rcases h_int_contained with ⟨ h₁, h₂ ⟩ ; rcases n : Int.toNat ( b - a + 1 ) with ( _ | n ) <;> simp_all +decide [ List.range_succ ];
        · grind;
        · linarith [ Int.toNat_of_nonneg ( by linarith : 0 ≤ b - a + 1 ) ];
    · intro h
      obtain ⟨sub, h_sub_infix, h_sub_consecutive, h_sub_len, h_sub_head, h_sub_last⟩ := h
      have h_sub_subset : ∀ k, a ≤ k ∧ k ≤ b → k ∈ nums := by
        have h_sub_subset : ∀ k, a ≤ k ∧ k ≤ b → k ∈ sub := by
          apply VerinaSpec.consecutive_bounds_implies_mem sub a b h_sub_consecutive h_sub_head h_sub_last;
        exact fun k hk => by have := h_sub_infix.subset ( h_sub_subset k hk ) ; exact List.mem_mergeSort.mp this;
      by_cases hab : a ≤ b <;> simp_all +decide [ LLMSpec.intervalLength ];
      · exact ⟨ hab, fun k hk => h_sub_subset k hk.1 hk.2 ⟩;
      · grind

/-
If a list of integers is sorted with <= and has no duplicates, it is sorted with <.
-/
theorem sorted_lt_of_sorted_le_nodup {l : List Int} (h_le : l.Sorted (· ≤ ·)) (h_nodup : l.Nodup) : l.Sorted (· < ·) := by
  exact?

/-
Assuming nums is not empty, the list of lengths of consecutive sublists computed in the postcondition contains n if and only if there exists a consecutive infix of sorted_nums with length n.
-/
theorem VerinaSpec.mem_consec_sublist_lens_iff (nums : List Int) (h_nonempty : nums ≠ []) (n : Nat) :
  n ∈ (let sorted_nums := nums.mergeSort
       List.range nums.length |>.flatMap (fun start =>
         List.range (nums.length - start + 1) |>.map (fun len => sorted_nums.extract start (start + len)))
       |>.filter isConsecutive |>.map (·.length)) ↔
  ∃ sub, sub <:+: nums.mergeSort ∧ VerinaSpec.isConsecutive sub ∧ sub.length = n := by
    constructor <;> intro H1 ; contrapose! H1 ; simp_all +decide [ List.mem_flatMap, List.mem_filter, List.mem_range ] ; (
    intro x y hy z hz hx hy' hz'; specialize H1 x; simp_all +decide [ List.IsInfix ] ;
    contrapose! H1; use List.take y ( nums.mergeSort fun a b => Decidable.decide ( a ≤ b ) ), List.drop ( y + z ) ( nums.mergeSort fun a b => Decidable.decide ( a ≤ b ) ) ; aesop;);
    rcases H1 with ⟨ sub, hsub₁, hsub₂, rfl ⟩ ; (
    obtain ⟨start, len, h_sub⟩ : ∃ start len, sub = (nums.mergeSort (fun a b => a ≤ b)).extract start (start + len) := by
      obtain ⟨ start, hstart ⟩ := hsub₁;
      obtain ⟨ t, ht ⟩ := hstart; use start.length, sub.length; simp +decide [ ← ht ] ;
    by_cases hstart : start < nums.length <;> simp_all +decide [ List.extract ];
    · by_cases hlen : len ≤ nums.length - start <;> simp_all +decide [ List.length_take, List.length_drop ];
      · exact ⟨ _, ⟨ ⟨ start, hstart, len, Nat.lt_succ_of_le hlen, rfl ⟩, hsub₂ ⟩, by simp +decide [ List.length_take, hlen ] ⟩;
      · refine' ⟨ _, ⟨ ⟨ start, hstart, nums.length - start, _, rfl ⟩, _ ⟩, _ ⟩ <;> norm_num [ hstart, hlen ];
        · convert hsub₂ using 1;
          rw [ List.take_of_length_le ( by simpa using by omega ) ];
          rw [ List.take_of_length_le ( by simpa using by omega ) ];
        · omega;
    · exact ⟨ 0, List.length_pos_iff.mpr h_nonempty, 0, Nat.zero_lt_succ _, Or.inl rfl ⟩)

end AristotleLemmas

theorem postcondition_equiv (nums : List Int) (result : Nat) : LLMSpec.precondition nums →
  (VerinaSpec.longestConsecutive_postcond nums result ↔ LLMSpec.postcondition nums result) := by
  -- Apply the equivalence of the postconditions under the precondition.
  intros h_pre
  apply Iff.intro;
  · -- Assume the VerinaSpec's postcondition holds. We need to show that the LLMSpec's postcondition holds.
    intro hverina
    constructor;
    · exact hverina.1;
    · intro h_nonempty
      obtain ⟨h_consec_sublist, h_max_length⟩ := hverina
      have h_consec_sublist_len : ∃ sub, sub <:+: nums.mergeSort ∧ VerinaSpec.isConsecutive sub ∧ sub.length = result := by
        have := VerinaSpec.mem_consec_sublist_lens_iff nums h_nonempty result; aesop;
      obtain ⟨sub, h_sub_infix, h_sub_consec, h_sub_len⟩ := h_consec_sublist_len
      have h_interval : ∃ a b : ℤ, LLMSpec.intervalContained nums a b ∧ result = LLMSpec.intervalLength a b := by
        obtain ⟨a, b, h_interval_contained, h_interval_len⟩ : ∃ a b : ℤ, sub.length = LLMSpec.intervalLength a b ∧ sub.head? = some a ∧ sub.getLast? = some b := by
          obtain ⟨a, ha⟩ : ∃ a : ℤ, sub = (List.range sub.length).map (fun i => a + i) := by
            convert VerinaSpec.isConsecutive_iff sub |>.1 h_sub_consec using 1;
            norm_num [ Function.comp, List.map_flatMap ];
            exact funext fun x => by rw [ List.map_eq_flatMap ] ;
          rcases sub <;> simp +decide [ List.range_succ_eq_map ] at *;
          · contrapose! h_max_length;
            refine' ⟨ h_nonempty, _ ⟩;
            rintro ⟨ a, ⟨ ⟨ i, hi, rfl | ⟨ j, hj, hj' ⟩ ⟩, ha ⟩, ha' ⟩ <;> norm_num [ ← h_sub_len ] at *;
            · use 0, by linarith, 0, by omega; ; simp +decide [ VerinaSpec.isConsecutive ] ;
              grind;
            · aesop;
          · rename_i k hk;
            rcases hk <;> simp +decide [ List.getLast? ] at *;
            · unfold LLMSpec.intervalLength; norm_num;
            · simp +decide [ List.getLast_eq_getElem, ha ];
              simp +decide [ List.range_succ, List.map ];
              unfold LLMSpec.intervalLength; norm_num; ring;
              norm_cast;
        use a, b;
        rw [ VerinaSpec.intervalContained_iff_infix ];
        · exact ⟨ ⟨ sub, h_sub_infix, h_sub_consec, h_interval_contained, h_interval_len ⟩, h_sub_len.symm.trans h_interval_contained ⟩;
        · exact h_pre
      obtain ⟨a, b, h_interval_contained, h_interval_len⟩ := h_interval
      have h_max_interval : ∀ a b : ℤ, LLMSpec.intervalContained nums a b → LLMSpec.intervalLength a b ≤ result := by
        intros a b h_interval_contained
        have h_consec_sublist_len : ∃ sub, sub <:+: nums.mergeSort ∧ VerinaSpec.isConsecutive sub ∧ sub.length = LLMSpec.intervalLength a b := by
          have := VerinaSpec.intervalContained_iff_infix nums h_pre a b; aesop;
        obtain ⟨sub, h_sub_infix, h_sub_consec, h_sub_len⟩ := h_consec_sublist_len
        have h_max_length : LLMSpec.intervalLength a b ≤ result := by
          have h_max_length : sub.length ∈ List.map (fun x => x.length) (List.filter VerinaSpec.isConsecutive (List.flatMap (fun start => List.map (fun len => (nums.mergeSort fun (a b : ℤ) => Decidable.decide (a ≤ b)).extract start (start + len)) (List.range (nums.length - start + 1))) (List.range nums.length))) := by
            apply VerinaSpec.mem_consec_sublist_lens_iff nums h_nonempty (sub.length) |>.2 ⟨sub, h_sub_infix, h_sub_consec, rfl⟩ |> fun h => by simpa using h;
          grind
        exact h_max_length
      have h_bounds : 1 ≤ result ∧ result ≤ nums.length := by
        have h_bounds : sub.length ≤ nums.length := by
          have := h_sub_infix.length_le; aesop;
        exact ⟨by
        exact h_interval_len ▸ Nat.succ_le_of_lt ( by unfold LLMSpec.intervalLength; linarith [ h_interval_contained.1, Int.toNat_of_nonneg ( by linarith [ h_interval_contained.1 ] : 0 ≤ b - a + 1 ) ] ) ;, by
          linarith⟩
      exact ⟨⟨a, b, h_interval_contained, h_interval_len⟩, h_max_interval, h_bounds⟩;
  · intro h_post
    obtain ⟨h_empty, h_nonempty⟩ := h_post
    by_cases h_empty' : nums = [] <;> simp_all +decide [ VerinaSpec.longestConsecutive_postcond ];
    constructor;
    · obtain ⟨ ⟨ a, b, h₁, rfl ⟩, h₂, h₃, h₄ ⟩ := h_nonempty;
      -- By definition of `intervalContained`, there exists a consecutive sublist of `nums.mergeSort` with length `LLMSpec.intervalLength a b`.
      obtain ⟨sub, h_sub⟩ : ∃ sub : List ℤ, sub <:+: nums.mergeSort ∧ VerinaSpec.isConsecutive sub ∧ sub.length = LLMSpec.intervalLength a b ∧ sub.head? = some a ∧ sub.getLast? = some b := by
        convert VerinaSpec.intervalContained_iff_infix nums h_pre a b |>.1 h₁ using 1;
      use sub;
      obtain ⟨ k, hk ⟩ := h_sub.1;
      obtain ⟨ t, ht ⟩ := hk; use ⟨ ⟨ k.length, by
        replace ht := congr_arg List.length ht ; simp_all +decide [ List.length_append ] ; linarith;, sub.length, by
        have := congr_arg List.length ht; norm_num at this; omega;, by
        simp +decide [ ← ht, List.take_append ] ⟩, h_sub.2.1 ⟩, h_sub.2.2.1;
    · -- If the length of the sublist is greater than result, then it cannot be a consecutive sequence.
      intros x hx x_1 hx_1
      by_contra h_contra
      push_neg at h_contra
      have h_consecutive : VerinaSpec.isConsecutive (List.take x_1 (List.drop x (nums.mergeSort fun (a b : ℤ) => Decidable.decide (a ≤ b)))) := by
        aesop
      have h_interval : ∃ a b : ℤ, LLMSpec.intervalContained nums a b ∧ x_1 = LLMSpec.intervalLength a b := by
        have h_interval : ∃ a b : ℤ, List.take x_1 (List.drop x (nums.mergeSort fun (a b : ℤ) => Decidable.decide (a ≤ b))) = (List.range x_1).map (fun i => a + ↑i) ∧ a ≤ b ∧ b - a + 1 = x_1 := by
          obtain ⟨a, ha⟩ : ∃ a : ℤ, List.take x_1 (List.drop x (nums.mergeSort fun (a b : ℤ) => Decidable.decide (a ≤ b))) = (List.range x_1).map (fun i => a + ↑i) := by
            convert VerinaSpec.isConsecutive_iff _ |>.1 h_consecutive using 1
            generalize_proofs at *; (
            simp +zetaDelta at *;
            rw [ min_eq_left ( by omega ) ])
          generalize_proofs at *; (
          exact ⟨ a, a + x_1 - 1, ha, by linarith, by linarith ⟩)
        generalize_proofs at *; (
        obtain ⟨ a, b, h₁, h₂, h₃ ⟩ := h_interval; use a, b; simp_all +decide [ LLMSpec.intervalContained ] ;
        have h_interval : ∀ k : ℤ, a ≤ k → k ≤ b → k ∈ List.take x_1 (List.drop x (nums.mergeSort fun (a b : ℤ) => Decidable.decide (a ≤ b))) := by
          intro k hk₁ hk₂; rw [ h₁ ] ; simp +decide [ List.mem_map, List.mem_range ] ; exact ⟨ Int.toNat ( k - a ), by linarith [ Int.toNat_of_nonneg ( sub_nonneg.mpr hk₁ ) ], by linarith [ Int.toNat_of_nonneg ( sub_nonneg.mpr hk₁ ) ] ⟩ ;
        generalize_proofs at *; (
        exact ⟨ fun k hk₁ hk₂ => by have := h_interval k hk₁ hk₂; exact List.mem_of_mem_take this |> List.mem_of_mem_drop |> fun h => by simpa using List.mem_mergeSort.mp h, by unfold LLMSpec.intervalLength; omega ⟩ ;))
      obtain ⟨a, b, h_interval, h_len⟩ := h_interval
      have h_le : LLMSpec.intervalLength a b ≤ result := by
        exact h_nonempty.2.1 a b h_interval
      linarith [h_len]

end Proof