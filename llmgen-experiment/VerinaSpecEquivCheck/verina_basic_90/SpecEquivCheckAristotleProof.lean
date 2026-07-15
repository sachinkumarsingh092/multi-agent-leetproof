/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: d1774542-64be-4062-9a33-e53d60319119

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array (Array Int)) (key : Int) : VerinaSpec.SlopeSearch_precond a key ↔ LLMSpec.precondition a key

- theorem postcondition_equiv (a : Array (Array Int)) (key : Int) (result : (Int × Int)) : LLMSpec.precondition a key →
  (VerinaSpec.SlopeSearch_postcond a key result ↔ LLMSpec.postcondition a key result)

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

def get2d (a : Array (Array Int)) (i j : Int) : Int :=
  (a[Int.toNat i]!)[Int.toNat j]!

def SlopeSearch_precond (a : Array (Array Int)) (key : Int) : Prop :=
  a.size > 0 ∧
  (a[0]!).size > 0 ∧  -- non-empty inner arrays
  List.Pairwise (·.size = ·.size) a.toList ∧
  a.all (fun x => List.Pairwise (· ≤ ·) x.toList) ∧
  (List.range (a[0]!.size)).all (fun i =>
    List.Pairwise (· ≤ ·) (a.map (fun x => x[i]!)).toList
  )

def SlopeSearch_postcond (a : Array (Array Int)) (key : Int) (result: (Int × Int)) :=
  let (m, n) := result;
  (m ≥ 0 ∧ m < a.size ∧ n ≥ 0 ∧ n < (a[0]!).size ∧ get2d a m n = key) ∨
  (m = -1 ∧ n = -1 ∧ a.all (fun x => x.all (fun e => e ≠ key)))

end VerinaSpec

namespace LLMSpec

-- Number of columns; defined safely even for empty outer arrays.
-- When `a.size = 0`, we define `ncols a = 0`.
-- When `a.size > 0`, we define `ncols a = (a[0]!).size`.
def ncols (a : Array (Array Int)) : Nat :=
  if h : a.size > 0 then
    (a[0]!).size
  else
    0

-- Matrix has at least one row, and all rows have the same positive length.
def isRectangularNonempty (a : Array (Array Int)) : Prop :=
  a.size > 0 ∧
  ncols a > 0 ∧
  (∀ (r : Nat), r < a.size → a[r]!.size = ncols a)

-- Row-wise nondecreasing ordering.
def rowsNondecreasing (a : Array (Array Int)) : Prop :=
  ∀ (r : Nat) (c1 : Nat) (c2 : Nat),
    r < a.size → c1 < c2 → c2 < ncols a → (a[r]!)[c1]! ≤ (a[r]!)[c2]!

-- Column-wise nondecreasing ordering.
def colsNondecreasing (a : Array (Array Int)) : Prop :=
  ∀ (c : Nat) (r1 : Nat) (r2 : Nat),
    c < ncols a → r1 < r2 → r2 < a.size → (a[r1]!)[c]! ≤ (a[r2]!)[c]!

-- The key appears somewhere in the matrix.
def keyOccurs (a : Array (Array Int)) (key : Int) : Prop :=
  ∃ (r : Nat) (c : Nat),
    r < a.size ∧ c < ncols a ∧ (a[r]!)[c]! = key

-- Preconditions: rectangular non-empty matrix, sorted by rows and by columns.
def precondition (a : Array (Array Int)) (key : Int) : Prop :=
  isRectangularNonempty a ∧
  rowsNondecreasing a ∧
  colsNondecreasing a

-- Postcondition:
-- Either the key does not occur and result is (-1,-1),
-- or the key occurs and result is an (Int.ofNat r, Int.ofNat c) pointing to a key cell.
def postcondition (a : Array (Array Int)) (key : Int) (result : Int × Int) : Prop :=
  ((¬ keyOccurs a key) ∧ result = (-1, -1)) ∨
  (∃ (r : Nat) (c : Nat),
    r < a.size ∧
    c < ncols a ∧
    result = (Int.ofNat r, Int.ofNat c) ∧
    (a[r]!)[c]! = key)

end LLMSpec

section Proof

theorem precondition_equiv (a : Array (Array Int)) (key : Int) : VerinaSpec.SlopeSearch_precond a key ↔ LLMSpec.precondition a key := by
  constructor <;> intro h;
  · -- By definition of `VerinaSpec.SlopeSearch_precond`, we know that `a` is rectangular, non-empty, and sorted by rows and columns.
    obtain ⟨h_rect, h_nonempty, h_sorted_rows, h_sorted_cols, h_all_rows⟩ := h;
    refine' ⟨ ⟨ h_rect, _, _ ⟩, _, _ ⟩;
    · unfold LLMSpec.ncols; aesop;
    · -- Since all rows have the same size, we can conclude that for any row r, the size of a[r]! is equal to the size of a[0]!.
      have h_row_size : ∀ r < a.size, (a[r]!).size = (a[0]!).size := by
        intro r hr; induction' r with r ih <;> simp_all +decide [ List.pairwise_iff_get ] ;
        exact h_sorted_rows ⟨ 0, by linarith ⟩ ⟨ r + 1, by linarith ⟩ ( Nat.zero_lt_succ _ ) ▸ rfl;
      unfold LLMSpec.ncols; aesop;
    · intro r c1 c2 hr hc1c2 hc2; have := h_sorted_cols; simp_all +decide [ List.pairwise_iff_get ] ;
      -- Apply the hypothesis `h_sorted_cols` with `i = r`, `i_1 = c1`, and `j = c2`.
      specialize h_sorted_cols r hr ⟨c1, by
        -- Since all rows have the same length, we have a[r].size = a[0].size.
        have h_row_size : a[r].size = a[0].size := by
          -- Since all rows have the same size, we can apply the hypothesis `h_sorted_rows` with `i = 0` and `j = r`.
          by_cases hr0 : r = 0;
          · grind;
          · exact Eq.symm ( h_sorted_rows ⟨ 0, by linarith ⟩ ⟨ r, by linarith ⟩ ( Nat.pos_of_ne_zero hr0 ) );
        exact lt_trans hc1c2 ( lt_of_lt_of_le hc2 ( by unfold LLMSpec.ncols; aesop ) )⟩ ⟨c2, by
        -- Since $a$ is a rectangular array, all rows have the same length. Therefore, $a[r].size = a[0].size$.
        have h_row_size : a[r].size = a[0].size := by
          -- Since all rows have the same size, we can apply the hypothesis `h_sorted_rows` with `i = 0` and `j = r`.
          by_cases hr0 : r = 0;
          · grind;
          · exact Eq.symm ( h_sorted_rows ⟨ 0, by linarith ⟩ ⟨ r, by linarith ⟩ ( Nat.pos_of_ne_zero hr0 ) );
        unfold LLMSpec.ncols at hc2; aesop;⟩ hc1c2
      generalize_proofs at *;
      grind;
    · intro c r1 r2 hc hr1 hr2; simp_all +decide [ List.pairwise_iff_get ] ;
      convert h_all_rows c _ ⟨ r1, _ ⟩ ⟨ r2, _ ⟩ hr1 using 1 <;> simp_all +decide [ LLMSpec.ncols ];
      grind;
      linarith;
  · rcases h with ⟨ ⟨ h₁, h₂, h₃ ⟩, h₄, h₅ ⟩;
    refine' ⟨ h₁, _, _, _, _ ⟩;
    · exact h₃ 0 h₁ ▸ h₂;
    · rw [ List.pairwise_iff_get ] ; aesop;
    · -- Since `h₄` states that the rows are non-decreasing, we can conclude that each row is sorted.
      have h_sorted_rows : ∀ r < a.size, List.Pairwise (· ≤ ·) (a[r]!.toList) := by
        -- By definition of `rowsNondecreasing`, for any row `r` and any columns `c1` and `c2` where `c1 < c2`, we have `(a[r]!)[c1]! ≤ (a[r]!)[c2]!`.
        intros r hr
        have h_sorted : ∀ c1 c2 : ℕ, c1 < c2 → c2 < a[r]!.size → (a[r]!)[c1]! ≤ (a[r]!)[c2]! := by
          exact fun c1 c2 h1 h2 => h₄ r c1 c2 hr h1 ( by linarith [ h₃ r hr ] );
        refine' List.pairwise_iff_get.mpr _;
        -- Since `i` and `j` are in the `Fin` type, they are valid indices into the list. Therefore, we can apply `h_sorted` directly.
        intros i j hij
        have h_bounds : i.val < j.val ∧ j.val < a[r]!.size := by
          exact ⟨ hij, by simp ⟩;
        grind;
      grind;
    · simp_all +decide [ List.pairwise_iff_get ];
      -- By definition of `colsNondecreasing`, for any column `x`, if `i < j`, then `a[i][x] ≤ a[j][x]`.
      intros x hx i j hij
      have h_col : ∀ (r1 r2 : ℕ), r1 < r2 → r2 < a.size → (a[r1]!)[x]! ≤ (a[r2]!)[x]! := by
        exact fun r1 r2 hr1 hr2 => h₅ x r1 r2 hx hr1 hr2;
      grind

theorem postcondition_equiv (a : Array (Array Int)) (key : Int) (result : (Int × Int)) : LLMSpec.precondition a key →
  (VerinaSpec.SlopeSearch_postcond a key result ↔ LLMSpec.postcondition a key result) := by
  -- By definition of `precondition`, if the precondition holds, then the matrix is rectangular and sorted.
  intro h_precondition
  simp [VerinaSpec.SlopeSearch_postcond, LLMSpec.postcondition];
  constructor <;> intro h;
  · rcases h with ( ⟨ h₁, h₂, h₃, h₄, h₅ ⟩ | ⟨ h₁, h₂, h₃ ⟩ ) <;> simp_all +decide [ LLMSpec.keyOccurs ];
    · refine Or.inr ⟨ Int.toNat result.1, ?_, Int.toNat result.2, ?_, ?_, ?_ ⟩ <;> try linarith [ Int.toNat_of_nonneg h₁, Int.toNat_of_nonneg h₃ ];
      · unfold LLMSpec.ncols; aesop;
      · exact Prod.ext ( by rw [ Int.toNat_of_nonneg h₁ ] ) ( by rw [ Int.toNat_of_nonneg h₃ ] );
      · convert h₅ using 1;
    · -- Since the matrix is rectangular and non-empty, the size of each row is equal to ncols a.
      have h_row_size : ∀ i < a.size, (a[i]!).size = LLMSpec.ncols a := by
        exact h_precondition.1.2.2;
      grind +ring;
  · -- Let's split into the two cases from h.
    cases' h with h_no_key h_key;
    · unfold LLMSpec.keyOccurs at h_no_key;
      -- Since `a[i].size = ncols a` by the precondition, we can apply `h_no_key` directly.
      have h_size_eq : ∀ i < a.size, a[i]!.size = LLMSpec.ncols a := by
        exact h_precondition.1.2.2;
      grind;
    · obtain ⟨ r, hr, x, hx, rfl, h ⟩ := h_key; use Or.inl ⟨ by linarith, by linarith, by linarith, ?_, ?_ ⟩ <;> simp_all +decide [ VerinaSpec.get2d ] ;
      unfold LLMSpec.ncols at hx; aesop;

end Proof