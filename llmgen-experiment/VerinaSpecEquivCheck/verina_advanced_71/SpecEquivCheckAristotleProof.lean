/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 97e3f09a-1e16-4969-831a-07e4a7888072

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (s : String) (k : Nat) : VerinaSpec.shortestBeautifulSubstring_precond s k ↔ LLMSpec.precondition s.toList k

The following was negated by Aristotle:

- theorem postcondition_equiv (s : String) (k : Nat) (result : String) : LLMSpec.precondition s.toList k →
  (VerinaSpec.shortestBeautifulSubstring_postcond s k result ↔ LLMSpec.postcondition s.toList k result.toList)

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

def countOnes (lst : List Char) : Nat :=
  lst.foldl (fun acc c => if c = '1' then acc + 1 else acc) 0

def shortestBeautifulSubstring_precond (s : String) (k : Nat) : Prop :=
  s.toList.all (fun c => c = '0' ∨ c = '1')

def listToString (lst : List Char) : String :=
  String.mk lst

def isLexSmaller (a b : List Char) : Bool :=
  listToString a < listToString b

def allSubstrings (s : List Char) : List (List Char) :=
  let n := s.length
  (List.range n).flatMap (fun i =>
    (List.range (n - i)).map (fun j =>
      s.drop i |>.take (j + 1)))

def shortestBeautifulSubstring_postcond (s : String) (k : Nat) (result: String) : Prop :=
  let chars := s.data
  let substrings := (List.range chars.length).flatMap (fun i =>
    (List.range (chars.length - i + 1)).map (fun len =>
      chars.drop i |>.take len))
  let isBeautiful := fun sub => countOnes sub = k
  let beautiful := substrings.filter (fun sub => isBeautiful sub)
  let targets := beautiful.map (·.asString) |>.filter (fun s => s ≠ "")
  (result = "" ∧ targets = []) ∨
  (result ∈ targets ∧
   ∀ r ∈ targets, r.length ≥ result.length ∨ (r.length = result.length ∧ result ≤ r))

end VerinaSpec

namespace LLMSpec

-- We model the input/output "string" as `List Char` to avoid `String` indexing with `String.Pos`.
-- A contiguous substring is described by a start index `i` and a length `len`.

def sliceChars (s : List Char) (i : Nat) (len : Nat) : List Char :=
  (s.drop i).take len

def isBinaryChars (s : List Char) : Prop :=
  ∀ (c : Char), c ∈ s → c = '0' ∨ c = '1'

def onesCount (t : List Char) : Nat :=
  t.count '1'

def isSubstringByRange (s : List Char) (t : List Char) : Prop :=
  ∃ (i : Nat) (len : Nat),
    len > 0 ∧ i + len ≤ s.length ∧ t = sliceChars s i len

def isValidCandidate (s : List Char) (k : Nat) (t : List Char) : Prop :=
  isSubstringByRange s t ∧ onesCount t = k

def precondition (s : List Char) (k : Nat) : Prop :=
  isBinaryChars s

def postcondition (s : List Char) (k : Nat) (result : List Char) : Prop :=
  (¬ (∃ (t : List Char), isValidCandidate s k t) ∧ result = []) ∨
  ((∃ (t : List Char), isValidCandidate s k t) ∧
    isValidCandidate s k result ∧
    (∀ (t : List Char), isValidCandidate s k t →
      (result.length < t.length) ∨ (result.length = t.length ∧ result ≤ t)))

end LLMSpec

section Proof

theorem precondition_equiv (s : String) (k : Nat) : VerinaSpec.shortestBeautifulSubstring_precond s k ↔ LLMSpec.precondition s.toList k := by
  -- The preconditions are equivalent because they both check if all characters in the list are '0' or '1'.
  simp [VerinaSpec.shortestBeautifulSubstring_precond, LLMSpec.precondition];
  -- The two conditions are equivalent because they both check if all characters in the list are '0' or '1'.
  simp [LLMSpec.isBinaryChars]

theorem VerinaSpec.postcondition_equiv_false : ¬ (∀ (s : String) (k : Nat) (result : String),
  LLMSpec.precondition s.toList k →
  (VerinaSpec.shortestBeautifulSubstring_postcond s k result ↔ LLMSpec.postcondition s.toList k result.toList)) := by
    simp +zetaDelta at *;
    -- Consider the string `s = "11011"`, `k = 3`, and `result = "1101"`.
    use "11011", 3, by
      exact fun c hc => by fin_cases hc <;> trivial;
    generalize_proofs at *;
    -- Let's choose the result string "1101".
    use "1101";
    unfold LLMSpec.postcondition VerinaSpec.shortestBeautifulSubstring_postcond; simp +decide ;
    intro x hx hx'; use [ '1', '0', '1', '1' ] ; simp_all +decide ;
    exact ⟨ ⟨ 1, 4, by decide, by decide, rfl ⟩, by decide ⟩


/- Aristotle found this block to be false. Here is a proof of the negation:

noncomputable section AristotleLemmas

def VerinaSpec.candidates (s : String) (k : Nat) : List String :=
  let chars := s.data
  let substrings := (List.range chars.length).flatMap (fun i =>
    (List.range (chars.length - i + 1)).map (fun len =>
      chars.drop i |>.take len))
  let isBeautiful := fun sub => VerinaSpec.countOnes sub = k
  let beautiful := substrings.filter (fun sub => isBeautiful sub)
  beautiful.map (·.asString) |>.filter (fun s => s ≠ "")

theorem VerinaSpec.candidates_iff (s : String) (k : Nat) (r : String) :
  r ∈ VerinaSpec.candidates s k ↔ r ≠ "" ∧ LLMSpec.isValidCandidate s.toList k r.toList := by
    -- By definition of candidates, r is in the candidates list if and only if it is a beautiful substring of s and not empty.
    simp [VerinaSpec.candidates];
    constructor <;> intro h;
    · obtain ⟨ ⟨ a, ⟨ ⟨ i, hi, j, hj, rfl ⟩, ha ⟩, rfl ⟩, hr ⟩ := h;
      refine' ⟨ hr, ⟨ ⟨ i, j, _, _, rfl ⟩, _ ⟩ ⟩;
      · contrapose! hr; aesop;
      · omega;
      · convert ha using 1;
        -- The foldl operation is equivalent to the count function when the list is being processed in the same order.
        have h_foldl_eq_count : ∀ (l : List Char), List.foldl (fun acc c => if c = '1' then acc + 1 else acc) 0 l = List.count '1' l := by
          intro l; induction' l using List.reverseRecOn with l ih <;> aesop;
        convert h_foldl_eq_count _ |> Eq.symm using 1;
    · obtain ⟨ i, len, hlen, hi, hr ⟩ := h.2.1;
      unfold LLMSpec.isValidCandidate at h; simp_all +decide [ LLMSpec.sliceChars ] ;
      refine' ⟨ _, ⟨ ⟨ i, by linarith, len, by omega, rfl ⟩, _ ⟩, _ ⟩;
      · convert h.2.2 using 1;
        -- By definition of `countOnes`, we have `countOnes l = List.foldl (fun acc c => if c = '1' then acc + 1 else acc) 0 l`.
        simp [VerinaSpec.countOnes, LLMSpec.onesCount];
        induction' ( List.take len ( List.drop i s.data ) ) using List.reverseRecOn with c l ih <;> aesop;
      · exact?

theorem VerinaSpec.candidates_empty_iff (s : String) (k : Nat) :
  VerinaSpec.candidates s k = [] ↔ ¬ ∃ t, LLMSpec.isValidCandidate s.toList k t := by
    constructor;
    · intro h
      by_contra h_contra
      obtain ⟨t, ht⟩ := h_contra
      have h_candidate : (t.asString ∈ VerinaSpec.candidates s k) := by
        have h_candidate : t.asString ≠ "" := by
          obtain ⟨ i, len, hlen, hle, rfl ⟩ := ht.1;
          simp +decide [ LLMSpec.sliceChars, List.asString ];
          simp +decide [ String.ext_iff, hlen.ne' ];
          linarith!;
        exact VerinaSpec.candidates_iff s k _ |>.2 ⟨ h_candidate, ht ⟩
      aesop;
    · exact fun h => List.eq_nil_iff_forall_not_mem.mpr fun t h' => h <| by rcases VerinaSpec.candidates_iff s k t |>.1 h' with ⟨ _, ⟨ i, len, hlen, hsum, hsub ⟩, hones ⟩ ; exact ⟨ _, ⟨ ⟨ i, len, hlen, hsum, hsub ⟩, hones ⟩ ⟩ ;

theorem VerinaSpec.postcond_iff_candidates (s : String) (k : Nat) (result : String) :
  VerinaSpec.shortestBeautifulSubstring_postcond s k result ↔
  (result = "" ∧ VerinaSpec.candidates s k = []) ∨
  (result ∈ VerinaSpec.candidates s k ∧
   ∀ r ∈ VerinaSpec.candidates s k, r.length ≥ result.length ∨ (r.length = result.length ∧ result ≤ r)) := by
     unfold VerinaSpec.candidates VerinaSpec.shortestBeautifulSubstring_postcond; aesop;

theorem VerinaSpec.isValidCandidate_implies_nonempty (s : List Char) (k : Nat) (t : List Char) :
  LLMSpec.isValidCandidate s k t → t ≠ [] := by
    intro ht
    obtain ⟨i, len, hlen_pos, hlen_le, ht_eq⟩ := ht.left
    have h_len : t.length = len := by
      simp [ht_eq, LLMSpec.sliceChars];
      exact le_tsub_of_add_le_left hlen_le
    have h_nonempty : t ≠ [] := by
      grind +ring
    exact h_nonempty

theorem VerinaSpec.string_le_iff_list_le (a b : String) :
  a ≤ b ↔ a.toList ≤ b.toList := by
    convert Iff.rfl using 1

theorem VerinaSpec.string_length_eq_list_length (s : String) :
  s.length = s.toList.length := by
    exact?

theorem VerinaSpec.string_empty_iff_list_empty (s : String) :
  s = "" ↔ s.toList = [] := by
    simp +decide [ String.ext_iff ]

theorem VerinaSpec.isValidCandidate_iff_mem_candidates (s : String) (k : Nat) (r : String) :
  LLMSpec.isValidCandidate s.toList k r.toList ↔ r ∈ VerinaSpec.candidates s k := by
    rw [ VerinaSpec.candidates_iff ];
    -- If theisValidCandidate holds, then r must be non-empty because theisValidCandidate requires that the substring is non-empty.
    have h_nonempty : LLMSpec.isValidCandidate s.toList k r.toList → r ≠ "" := by
      exact fun h => by rintro rfl; exact absurd ( VerinaSpec.isValidCandidate_implies_nonempty _ _ _ h ) ( by simp +decide ) ;
    grind

theorem VerinaSpec.postcondition_equiv_false : ¬ (∀ (s : String) (k : Nat) (result : String),
  LLMSpec.precondition s.toList k →
  (VerinaSpec.shortestBeautifulSubstring_postcond s k result ↔ LLMSpec.postcondition s.toList k result.toList)) := by
    simp +zetaDelta at *;
    -- Consider the string `s = "11011"`, `k = 3`, and `result = "1101"`.
    use "11011", 3, by
      exact fun c hc => by fin_cases hc <;> trivial;
    generalize_proofs at *;
    -- Let's choose the result string "1101".
    use "1101";
    unfold LLMSpec.postcondition VerinaSpec.shortestBeautifulSubstring_postcond; simp +decide ;
    intro x hx hx'; use [ '1', '0', '1', '1' ] ; simp_all +decide ;
    exact ⟨ ⟨ 1, 4, by decide, by decide, rfl ⟩, by decide ⟩

end AristotleLemmas

theorem postcondition_equiv (s : String) (k : Nat) (result : String) : LLMSpec.precondition s.toList k →
  (VerinaSpec.shortestBeautifulSubstring_postcond s k result ↔ LLMSpec.postcondition s.toList k result.toList) := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Let's choose any $s$ and $k$ such that the conditions are not satisfied.
  by_contra h_contra;
  -- Apply the equivalence of the postconditions to derive a contradiction.
  apply VerinaSpec.postcondition_equiv_false;
  grind +ring

-/
theorem postcondition_equiv (s : String) (k : Nat) (result : String) : LLMSpec.precondition s.toList k →
  (VerinaSpec.shortestBeautifulSubstring_postcond s k result ↔ LLMSpec.postcondition s.toList k result.toList) := by
  sorry

end Proof
