/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 9d5cc954-ae2c-4944-8388-71a3cd5b42d7

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (height : List Nat) : VerinaSpec.trapRainWater_precond height ↔ LLMSpec.precondition height

- theorem postcondition_equiv (height : List Nat) (result : Nat) : LLMSpec.precondition height →
  (VerinaSpec.trapRainWater_postcond height result ↔ LLMSpec.postcondition height result)

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

def trapRainWater_precond (height : List Nat) : Prop :=
  True

def trapRainWater_postcond (height : List Nat) (result: Nat) : Prop :=
  let waterAt := List.range height.length |>.map (fun i =>
    let lmax := List.take (i+1) height |>.foldl Nat.max 0
    let rmax := List.drop i height |>.foldl Nat.max 0
    Nat.min lmax rmax - height[i]!)
  result - (waterAt.foldl (· + ·) 0) = 0 ∧ (waterAt.foldl (· + ·) 0) ≤ result

end VerinaSpec

namespace LLMSpec

-- A characterization that `m` is the maximum height on the prefix {0..i} (inclusive),
-- assuming `i` is a valid index (< height.length).
-- This is expressed as:
--   (1) every prefix element is ≤ m (upper bound)
--   (2) some prefix element equals m (attainment)
def isPrefixMax (height : List Nat) (i : Nat) (m : Nat) : Prop :=
  i < height.length ∧
  (∀ (j : Nat), j ≤ i → j < height.length → height[j]! ≤ m) ∧
  (∃ (j : Nat), j ≤ i ∧ j < height.length ∧ height[j]! = m)

-- A characterization that `m` is the maximum height on the suffix {i..n-1} (inclusive),
-- assuming `i` is a valid index (< height.length).
def isSuffixMax (height : List Nat) (i : Nat) (m : Nat) : Prop :=
  i < height.length ∧
  (∀ (j : Nat), i ≤ j → j < height.length → height[j]! ≤ m) ∧
  (∃ (j : Nat), i ≤ j ∧ j < height.length ∧ height[j]! = m)

-- Water trapped at index i; defined as 0 for out-of-bounds indices to keep it total.
def waterAt (height : List Nat) (i : Nat) : Nat :=
  if h : i < height.length then
    let hi : Nat := height[i]!
    -- Choose left/right maxima concretely for the computation; the postcondition will relate them
    -- to the abstract maximum characterization.
    let lmax : Nat := (height.take (i + 1)).foldl Nat.max 0
    let rmax : Nat := (height.drop i).foldl Nat.max 0
    (Nat.min lmax rmax) - hi
  else
    0

-- Precondition: no restrictions beyond the stated domain (List Nat is already non-negative).
-- We mention `height` to avoid unused-variable warnings.
def precondition (height : List Nat) : Prop :=
  height.length = height.length

-- Postcondition:
-- There exist functions L and R giving, for each valid index i,
-- the prefix and suffix maxima respectively.
-- The result is the sum over indices of min(L i, R i) - height[i] (truncated subtraction).
def postcondition (height : List Nat) (result : Nat) : Prop :=
  let n : Nat := height.length
  (∃ (L : Nat → Nat),
    (∀ (i : Nat), i < n → isPrefixMax height i (L i)) ∧
    (∃ (R : Nat → Nat),
      (∀ (i : Nat), i < n → isSuffixMax height i (R i)) ∧
      result = (List.range n).foldl
        (fun (acc : Nat) (i : Nat) => acc + (Nat.min (L i) (R i) - height[i]!))
        0))

end LLMSpec

section Proof

theorem precondition_equiv (height : List Nat) : VerinaSpec.trapRainWater_precond height ↔ LLMSpec.precondition height := by
  -- The preconditions are equivalent because they both state that the length of the height list is equal to itself, which is trivially true.
  simp [VerinaSpec.trapRainWater_precond, LLMSpec.precondition]

theorem postcondition_equiv (height : List Nat) (result : Nat) : LLMSpec.precondition height →
  (VerinaSpec.trapRainWater_postcond height result ↔ LLMSpec.postcondition height result) := by
  rintro -;
  constructor <;> intro h;
  · refine' ⟨ fun i => List.foldl Nat.max 0 ( List.take ( i + 1 ) height ), _, fun i => List.foldl Nat.max 0 ( List.drop i height ), _, _ ⟩ <;> simp_all +decide [ LLMSpec.isPrefixMax, LLMSpec.isSuffixMax ];
    · intro i hi
      constructor
      all_goals generalize_proofs at *;
      · intro j hj a;
        have h_le_max : ∀ {l : List ℕ}, j < l.length → l[j]! ≤ List.foldl Nat.max 0 l := by
          -- By induction on the list, we can show that the maximum of the list is at least as large as any element in the list.
          intros l hl
          induction' l using List.reverseRecOn with l ih;
          · contradiction;
          · by_cases hj : j < l.length <;> simp_all +decide [ List.getElem_append ];
        grind +ring;
      · -- By definition of `List.foldl Nat.max 0 (List.take (i + 1) height)`, there exists some `j` in the range `0` to `i` such that `height[j]!` is equal to this maximum value.
        obtain ⟨j, hj⟩ : ∃ j ∈ List.range (i + 1), height[j]! = List.foldl Nat.max 0 (List.take (i + 1) height) := by
          have h_max : ∀ {l : List ℕ}, l ≠ [] → ∃ j ∈ List.range l.length, l[j]! = List.foldl Nat.max 0 l := by
            intros l hl_nonempty
            induction' l using List.reverseRecOn with l ih
            generalize_proofs at *; (
            contradiction);
            by_cases hl : l = [] <;> simp_all +decide [ List.foldl_append ];
            cases max_choice ( List.foldl Nat.max 0 l ) ih <;> simp_all +decide [ List.getElem?_append ];
            · obtain ⟨ j, hj₁, hj₂ ⟩ := ‹∃ j < l.length, l[j]?.getD 0 = List.foldl Nat.max 0 l›; exact ⟨ j, Nat.lt_succ_of_lt hj₁, by aesop ⟩ ;
            · exact ⟨ l.length, Nat.lt_succ_self _, by aesop ⟩
          generalize_proofs at *; (
          -- Apply the hypothesis `h_max` to the list `List.take (i + 1) height`, which is non-empty.
          have h_nonempty : List.take (i + 1) height ≠ [] := by
            aesop
          generalize_proofs at *; (
          obtain ⟨ j, hj₁, hj₂ ⟩ := h_max h_nonempty; use j; aesop;));
        exact ⟨ j, by linarith [ List.mem_range.mp hj.1 ], by linarith [ List.mem_range.mp hj.1 ], by aesop ⟩;
    · intro i hi
      constructor
      all_goals generalize_proofs at *;
      · -- Since the maximum of a list is an upper bound for all elements in the list, we have height[j] ≤ List.foldl Nat.max 0 (List.drop i height) for any j in the range i to height.length - 1.
        intros j hj a
        have h_max : ∀ x ∈ List.drop i height, x ≤ List.foldl Nat.max 0 (List.drop i height) := by
          induction' ( List.drop i height ) using List.reverseRecOn with x xs ih <;> aesop;
        convert h_max _ _;
        -- Since $j \geq i$, the element at position $j$ in the original list is in the drop of the list starting at $i$.
        have h_drop : height[j] ∈ List.drop i height := by
          have h_pos : j - i < List.length (List.drop i height) := by
            grind
          rw [ List.mem_iff_get ];
          exact ⟨ ⟨ j - i, h_pos ⟩, by simp +decide [ List.getElem_drop, hj ] ⟩;
        exact h_drop;
      · -- By definition of `List.foldl`, there exists some index `j` in the range `i` to `height.length - 1` such that `height[j]!` is equal to the maximum of the elements in `List.drop i height`.
        obtain ⟨j, hj⟩ : ∃ j ∈ List.drop i height, j = List.foldl Nat.max 0 (List.drop i height) := by
          have h_max_exists : ∀ {l : List ℕ}, l ≠ [] → ∃ j ∈ l, j = List.foldl Nat.max 0 l := by
            -- We can prove this by induction on the list.
            intro l hl_nonempty
            induction' l with x l ih
            all_goals generalize_proofs at *;
            · contradiction;
            · cases l <;> simp_all +decide [ List.foldl ];
              cases ih <;> simp_all +decide [ List.foldl_assoc ];
              · grind +ring;
              · cases max_choice x ( List.foldl Nat.max ‹_› ‹_› ) <;> aesop;
          exact h_max_exists ( by aesop );
        obtain ⟨ k, hk ⟩ := List.mem_iff_get.mp hj.1;
        use i + k.val;
        grind;
    · -- By definition of `trapRainWater_postcond`, we know that `result` is equal to the sum of the water trapped at each index.
      have h_sum : result = List.foldl (fun acc i => acc + (Nat.min (List.foldl Nat.max 0 (List.take (i + 1) height)) (List.foldl Nat.max 0 (List.drop i height)) - height[i]!)) 0 (List.range height.length) := by
        -- By definition of `trapRainWater_postcond`, we know that `result` is equal to the sum of the water trapped at each index. Therefore, we can use `h` directly to conclude the proof.
        apply Eq.symm; exact (by
        obtain ⟨h₁, h₂⟩ := h;
        convert Nat.sub_eq_zero_iff_le.mp h₁ |> le_antisymm h₂ using 1;
        rw [ List.foldl_map ]);
      aesop;
  · obtain ⟨ L, hL, R, hR, h_eq ⟩ := h;
    -- By definition of `L` and `R`, we know that `L i` and `R i` are the maximum heights on the left and right of index `i`, respectively.
    have h_max_left : ∀ i < height.length, List.foldl Nat.max 0 (List.take (i + 1) height) = L i := by
      intro i hi
      have h_max_left : ∀ j ≤ i, height[j]! ≤ L i := by
        exact fun j hj => hL i hi |>.2.1 j hj ( by linarith )
      have h_max_left_eq : ∃ j ≤ i, height[j]! = L i := by
        exact hL i hi |>.2.2.imp fun j hj => ⟨ hj.1, hj.2.2 ⟩
      have h_max_left_fold : List.foldl Nat.max 0 (List.take (i + 1) height) ≤ L i := by
        have h_max_left_fold : ∀ {l : List ℕ}, (∀ x ∈ l, x ≤ L i) → List.foldl Nat.max 0 l ≤ L i := by
          intros l hl; induction' l using List.reverseRecOn with l ih <;> aesop;
        apply h_max_left_fold;
        -- Since the list take (i+1) height is exactly the list of elements from index 0 to i, inclusive, each element in this list is height[j]! for some j ≤ i.
        have h_elements : ∀ x ∈ List.take (i + 1) height, ∃ j ≤ i, x = height[j]! := by
          -- By definition of `List.take`, the elements of `List.take (i + 1) height` are exactly the elements of `height` from index 0 to i.
          have h_take : List.take (i + 1) height = List.map (fun j => height[j]!) (List.range (i + 1)) := by
            refine' List.ext_get _ _ <;> simp +decide [ List.get ];
            · linarith;
            · exact fun n hn hn' hn'' => by rw [ List.getElem?_eq_getElem hn' ] ; rfl;
          simp [h_take];
          exact fun a ha => ⟨ a, Nat.le_of_lt_succ ha, rfl ⟩;
        exact fun x hx => by obtain ⟨ j, hj₁, rfl ⟩ := h_elements x hx; exact h_max_left j hj₁;
      have h_max_left_fold_eq : L i ≤ List.foldl Nat.max 0 (List.take (i + 1) height) := by
        -- Since $L i$ is in the list of heights up to $i$, the maximum of the list must be at least $L i$.
        have h_max_left_fold_eq : ∀ {l : List ℕ}, L i ∈ l → L i ≤ List.foldl Nat.max 0 l := by
          intros l hl; induction' l using List.reverseRecOn with l ih <;> aesop;
        -- Since $j \leq i$ and $height[j]! = L i$, and the list is List.take (i + 1) height, which includes all elements up to $i$, then $height[j]!$ must be in the list.
        have h_j_in_list : ∀ j ≤ i, j < height.length → height[j]! ∈ List.take (i + 1) height := by
          intro j hj₁ hj₂; rw [ List.mem_iff_get ] ; use ⟨ j, by
            rw [ List.length_take ] ; omega ⟩ ; aesop;
        exact h_max_left_fold_eq ( by obtain ⟨ j, hj₁, hj₂ ⟩ := h_max_left_eq; exact hj₂ ▸ h_j_in_list j hj₁ ( by linarith ) )
      exact le_antisymm h_max_left_fold h_max_left_fold_eq
    have h_max_right : ∀ i < height.length, List.foldl Nat.max 0 (List.drop i height) = R i := by
      intro i hi
      have h_max_right_i : R i ∈ List.drop i height ∧ ∀ j ∈ List.drop i height, j ≤ R i := by
        -- By definition of `isSuffixMax`, we know that `R i` is the maximum of the suffix starting at `i`, so it must be in the suffix and all elements in the suffix are less than or equal to `R i`.
        obtain ⟨hR_in_suffix, hR_max⟩ := hR i hi;
        -- Since $R i$ is in the suffix starting at $i$, it must be in the drop of $i$ from $height$.
        have hR_in_drop : R i ∈ List.drop i height := by
          obtain ⟨ j, hj₁, hj₂, hj₃ ⟩ := hR_max.2; rw [ List.mem_iff_get ] ; use ⟨ j - i, by
            rw [ List.length_drop ] ; omega ⟩ ; aesop;
        refine ⟨ hR_in_drop, ?_ ⟩;
        intro j hj; rw [ List.mem_iff_get ] at hj; aesop;
      refine' le_antisymm _ _;
      · have h_foldl_le : ∀ {l : List ℕ}, (∀ j ∈ l, j ≤ R i) → List.foldl Nat.max 0 l ≤ R i := by
          intros l hl; induction' l using List.reverseRecOn with l ih <;> aesop;
        exact h_foldl_le h_max_right_i.2;
      · have h_max_right_i : ∀ {l : List ℕ}, R i ∈ l → R i ≤ List.foldl Nat.max 0 l := by
          intros l hl; induction' l using List.reverseRecOn with l ih <;> aesop;
        exact h_max_right_i ( by tauto );
    -- By definition of `trapRainWater_postcond`, we need to show that the result is equal to the sum of the water at each index.
    simp [h_eq, VerinaSpec.trapRainWater_postcond];
    rw [ List.foldl_map ];
    rw [ show List.foldl ( fun x y => x + ( ( List.foldl Nat.max 0 ( List.take ( y + 1 ) height ) ).min ( List.foldl Nat.max 0 ( List.drop y height ) ) - height[y]?.getD 0 ) ) 0 ( List.range height.length ) = List.foldl ( fun ( acc i : ℕ ) => acc + ( ( L i ).min ( R i ) - height[i]?.getD 0 ) ) 0 ( List.range height.length ) from ?_ ] ; aesop;
    have h_foldl_eq : ∀ (l : List ℕ), (∀ i ∈ l, i < height.length) → List.foldl (fun (x y : ℕ) => x + ((List.foldl Nat.max 0 (List.take (y + 1) height)).min (List.foldl Nat.max 0 (List.drop y height)) - height[y]?.getD 0)) 0 l = List.foldl (fun (acc i : ℕ) => acc + ((L i).min (R i) - height[i]?.getD 0)) 0 l := by
      intro l hl; induction' l using List.reverseRecOn with l ih <;> aesop;
    exact h_foldl_eq _ fun i hi => List.mem_range.mp hi

end Proof