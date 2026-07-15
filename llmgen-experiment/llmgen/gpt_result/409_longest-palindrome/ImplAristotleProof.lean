/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 39bdf820-7d0c-423f-9d94-749ce245d16c

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem goal_7_0_0 (s : List Char) (require_1 : True) (hasOdd : Bool) (i : ℕ) (invariant_lp_outer_i_le_n : i ≤ s.length) (invariant_lp_outer_hasOdd_def : hasOdd = true ↔ ∃ c ∈ List.take i s, List.count c s % OfNat.ofNat 2 = OfNat.ofNat 1) (if_pos : i < s.length) (i_1 : ℕ) (seenBefore_1 : Bool) (j_1 : ℕ) (invariant_lp_seen_k_le_i : i_1 ≤ i) (invariant_lp_cnt_j_le_n : j_1 ≤ s.length) (if_neg : ¬s = []) (if_neg_1 : seenBefore_1 = false) (invariant_lp_seen_nohit : seenBefore_1 = false → ∀ p < i_1, ¬s[p]?.getD 'A' = s[i]?.getD 'A') (invariant_lp_seen_hit : seenBefore_1 = true → ∃ p < i_1, s[p]?.getD 'A' = s[i]?.getD 'A') (done_2 : i_1 < i → seenBefore_1 = true) (done_3 : s.length ≤ j_1) (if_pos_1 : List.count (s[i]?.getD 'A') (List.take j_1 s) % OfNat.ofNat 2 = OfNat.ofNat 1) (htake_j : List.take j_1 s = s) (hci_not_mem_take : s[i]?.getD 'A' ∉ List.take i s) (htake_succ_getD : List.take (i + 1) s = List.take i s ++ [s[i]?.getD 'A']) : ∀ (l : List Char), ∀ a ∉ l, (l ++ [a]).eraseDups = l.eraseDups ++ [a]

- theorem goal_11 (s : List Char) (require_1 : True) (i_2 : ℕ) (invariant_lp_outer_i_le_n : i_2 ≤ s.length) (if_neg : ¬s = []) (done_1 : s.length ≤ i_2) (invariant_lp_outer_hasOdd_def : ∃ c ∈ List.take i_2 s, List.count c s % OfNat.ofNat 2 = OfNat.ofNat 1) : postcondition s (OfNat.ofNat 2 * (List.map (fun c => List.count c s / OfNat.ofNat 2) (List.take i_2 s).eraseDups).sum + OfNat.ofNat 1)

- theorem goal_12 (s : List Char) (require_1 : True) (i_1 : Bool) (i_2 : ℕ) (invariant_lp_outer_i_le_n : i_2 ≤ s.length) (invariant_lp_outer_hasOdd_def : i_1 = true ↔ ∃ c ∈ List.take i_2 s, List.count c s % OfNat.ofNat 2 = OfNat.ofNat 1) (if_neg : ¬s = []) (if_neg_1 : i_1 = false) (done_1 : s.length ≤ i_2) : postcondition s (OfNat.ofNat 2 * (List.map (fun c => List.count c s / OfNat.ofNat 2) (List.take i_2 s).eraseDups).sum)

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

-- Never add new imports here

set_option maxHeartbeats 10000000

set_option pp.coercions false

/- Problem Description
    409. Longest Palindrome: Given a sequence of case-sensitive letters, compute the maximum length of a palindrome buildable from those letters.
    **Important: complexity should be O(n ^ 2) time and O(1) space**.
    Natural language breakdown:
    1. Input is a list of characters; characters are case sensitive (e.g., 'A' and 'a' are distinct).
    2. We may reorder the input characters and select any multiset of them, using each character at most as many times as it appears in the input.
    3. A list of characters is a palindrome exactly when it equals its reverse.
    4. A candidate palindrome is buildable from the input when, for every character c, its count in the candidate is at most its count in the input.
    5. The function returns the maximum possible length among all buildable palindromes.
    6. If the input is empty, the maximum palindrome length is 0.
-/

section Specs

-- A list is a palindrome iff it equals its reverse.
-- We use reverse-equality rather than `List.Palindrome` to ensure compatibility with the environment.
def isPalindrome (t : List Char) : Prop :=
  t.reverse = t

-- A list `t` can be built from `s` if it does not use any character more times than `s` provides.
-- `List.count` counts occurrences of a character.
def usesLetters (s : List Char) (t : List Char) : Prop :=
  ∀ (c : Char), t.count c ≤ s.count c

-- `t` is a palindrome buildable from `s`.
def buildablePalindrome (s : List Char) (t : List Char) : Prop :=
  isPalindrome t ∧ usesLetters s t

-- No input restrictions.
def precondition (s : List Char) : Prop :=
  True

-- `result` is exactly the maximum length of any buildable palindrome.
-- This is expressed by:
-- (1) existence of a buildable palindrome with length = result
-- (2) every buildable palindrome has length ≤ result
-- Together these uniquely determine `result`.
def postcondition (s : List Char) (result : Nat) : Prop :=
  (∃ (t : List Char), buildablePalindrome s t ∧ t.length = result) ∧
  (∀ (t : List Char), buildablePalindrome s t → t.length ≤ result)

end Specs

section TestCases

-- Test case 1: Example 1
-- Input: s = "abccccdd"; Output: 7
-- One longest palindrome is "dccaccd" (length 7).
def test1_s : List Char := ['a','b','c','c','c','c','d','d']

def test1_Expected : Nat := 7

-- Test case 2: Example 2
-- Input: s = "a"; Output: 1

def test2_s : List Char := ['a']

def test2_Expected : Nat := 1

-- Test case 3: Empty input
-- Input: []; Output: 0

def test3_s : List Char := []

def test3_Expected : Nat := 0

-- Test case 4: Case sensitivity
-- Input: ['A','a']; Output: 1 (cannot pair because 'A' ≠ 'a')

def test4_s : List Char := ['A','a']

def test4_Expected : Nat := 1

-- Test case 5: All characters occur an even number of times
-- Input: "aaBB"; Output: 4

def test5_s : List Char := ['a','a','B','B']

def test5_Expected : Nat := 4

-- Test case 6: All characters are distinct
-- Input: "abc"; Output: 1

def test6_s : List Char := ['a','b','c']

def test6_Expected : Nat := 1

-- Test case 7: Multiple pairs, no leftover
-- Input: "aabbcc"; Output: 6

def test7_s : List Char := ['a','a','b','b','c','c']

def test7_Expected : Nat := 6

-- Test case 8: One leftover can be used as the center
-- Input: "aabbccd"; Output: 7

def test8_s : List Char := ['a','a','b','b','c','c','d']

def test8_Expected : Nat := 7

-- Test case 9: Multiple odd counts; only one odd can contribute a center
-- Input: "aaabbbbcc"; counts a=3, b=4, c=2 -> 8 from pairs + 1 center = 9

def test9_s : List Char := ['a','a','a','b','b','b','b','c','c']

def test9_Expected : Nat := 9

-- Recommend to validate: empty input handling, case sensitivity, multiple-odd-count behavior
end TestCases

section Proof

theorem goal_7_0_0 (s : List Char) (require_1 : True) (hasOdd : Bool) (i : ℕ) (invariant_lp_outer_i_le_n : i ≤ s.length) (invariant_lp_outer_hasOdd_def : hasOdd = true ↔ ∃ c ∈ List.take i s, List.count c s % OfNat.ofNat 2 = OfNat.ofNat 1) (if_pos : i < s.length) (i_1 : ℕ) (seenBefore_1 : Bool) (j_1 : ℕ) (invariant_lp_seen_k_le_i : i_1 ≤ i) (invariant_lp_cnt_j_le_n : j_1 ≤ s.length) (if_neg : ¬s = []) (if_neg_1 : seenBefore_1 = false) (invariant_lp_seen_nohit : seenBefore_1 = false → ∀ p < i_1, ¬s[p]?.getD 'A' = s[i]?.getD 'A') (invariant_lp_seen_hit : seenBefore_1 = true → ∃ p < i_1, s[p]?.getD 'A' = s[i]?.getD 'A') (done_2 : i_1 < i → seenBefore_1 = true) (done_3 : s.length ≤ j_1) (if_pos_1 : List.count (s[i]?.getD 'A') (List.take j_1 s) % OfNat.ofNat 2 = OfNat.ofNat 1) (htake_j : List.take j_1 s = s) (hci_not_mem_take : s[i]?.getD 'A' ∉ List.take i s) (htake_succ_getD : List.take (i + 1) s = List.take i s ++ [s[i]?.getD 'A']) : ∀ (l : List Char), ∀ a ∉ l, (l ++ [a]).eraseDups = l.eraseDups ++ [a] := by
    simp_all +decide [ List.eraseDups_append ];
    simp_all +decide [ List.removeAll ];
    grind

noncomputable section AristotleLemmas

theorem palindrome_odd_counts (t : List Char) (h : isPalindrome t) :
    (t.eraseDups.filter (fun c => t.count c % 2 = 1)).length ≤ 1 := by
  -- Let's denote the number of times each character appears in `t` by `f`.
  set f : Char → ℕ := fun c => t.count c;
  -- Since `t` is a palindrome, the number of characters with an odd count is at most 1.
  have h_odd_count : (Finset.filter (fun c => f c % 2 = 1) (List.toFinset t)).card ≤ 1 := by
    -- Since `t` is a palindrome, the number of characters with an odd count is at most 1. We can prove this by considering the symmetry of the palindrome.
    have h_symm : ∀ c ∈ List.toFinset t, f c = (List.count c (t.take (t.length / 2))) + (if t.length % 2 = 1 then if c = t.get! (t.length / 2) then 1 else 0 else 0) + (List.count c (t.drop (t.length / 2 + (if t.length % 2 = 1 then 1 else 0)))) := by
      intro c hc; split_ifs <;> simp_all +decide [ List.count ] ;
      · have h_split : List.count c (List.drop (t.length / 2) t) = List.count c (List.drop (t.length / 2 + 1) t) + (if c = t.get! (t.length / 2) then 1 else 0) := by
          rw [ List.drop_eq_getElem_cons ];
          all_goals norm_num [ List.count_cons ];
          grind;
          exact Nat.div_lt_self ( Nat.pos_of_ne_zero ( by aesop_cat ) ) ( by decide );
        simp_all +decide [ add_comm, add_left_comm, add_assoc ];
        convert congr_arg ( · + List.count ( t[t.length / 2]?.getD 'A' ) ( List.take ( t.length / 2 ) t ) ) h_split using 1 ; ring!;
        · rw [ add_comm, ← List.count_append, List.take_append_drop ];
        · simp +decide [ add_assoc, List.count ];
      · have h_split : List.countP (fun x => x == c) t = List.countP (fun x => x == c) (List.take (t.length / 2) t) + List.countP (fun x => x == c) (List.drop (t.length / 2) t) := by
          rw [ ← List.countP_append, List.take_append_drop ];
        rw [ show List.drop ( t.length / 2 ) t = t.get! ( t.length / 2 ) :: List.drop ( t.length / 2 + 1 ) t from ?_, List.countP_cons ] at h_split ; aesop;
        all_goals norm_num [ Nat.div_lt_self ( List.length_pos_iff.mpr ( show t ≠ [] from by rintro rfl; contradiction ) ) ];
      · rw [ ← List.countP_append, List.take_append_drop ];
        exact?;
    -- Since `t` is a palindrome, the counts of characters in the first half and the second half are equal.
    have h_eq_counts : ∀ c ∈ List.toFinset t, List.count c (t.take (t.length / 2)) = List.count c (t.drop (t.length / 2 + (if t.length % 2 = 1 then 1 else 0))) := by
      intro c hc
      have h_eq_counts : List.take (t.length / 2) t = List.reverse (List.drop (t.length / 2 + (if t.length % 2 = 1 then 1 else 0)) t) := by
        have h_eq_counts : List.take (t.length / 2) t = List.reverse (List.drop (t.length / 2 + (if t.length % 2 = 1 then 1 else 0)) t) := by
          have h_rev : List.reverse t = t := by
            exact h
          rw [ ← h_rev, List.reverse_drop ];
          grind +ring;
        exact h_eq_counts;
      rw [ h_eq_counts, List.count_reverse ];
    refine' Finset.card_le_one.mpr _;
    grind +ring;
  convert h_odd_count using 1;
  -- Since `List.eraseDups` removes duplicates, the resulting list is a permutation of the unique elements of `t`.
  have h_perm : List.toFinset (List.eraseDups t) = List.toFinset t := by
    ext c; simp [List.eraseDups];
    -- By definition of `List.eraseDupsBy.loop`, the elements of `t` are preserved in the resulting list.
    have h_eraseDupsBy_loop : ∀ (l : List Char) (acc : List Char), c ∈ List.eraseDupsBy.loop (fun x1 x2 => x1 == x2) l acc ↔ c ∈ l ∨ c ∈ acc := by
      intros l acc; induction' l with hd tl ih generalizing acc <;> simp [List.eraseDupsBy.loop] ; aesop;
    simpa using h_eraseDupsBy_loop t [ ];
  rw [ ← h_perm, ← Multiset.coe_card ];
  rw [ ← Multiset.toFinset_card_of_nodup ] ; aesop;
  refine' List.Nodup.filter _ _;
  -- By definition of `List.eraseDupsBy.loop`, the resulting list is nodup.
  have h_nodup : ∀ (l : List Char) (acc : List Char), List.Nodup acc → List.Nodup (List.eraseDupsBy.loop (fun x1 x2 => x1 == x2) l acc) := by
    intros l acc hacc; induction' l with hd tl ih generalizing acc <;> simp_all +decide [ List.eraseDupsBy.loop ] ;
    cases h : acc.any fun x2 => hd == x2 <;> aesop;
  exact h_nodup _ _ ( by simp +decide )

theorem palindrome_len_upper_bound (s t : List Char) (h : buildablePalindrome s t) :
    t.length ≤ 2 * (List.map (fun c => s.count c / 2) s.eraseDups).sum + 1 := by
  -- Let's denote the set of characters in `t` as `C`.
  set C := t.eraseDups with hC_def
  have hC_subset : C ⊆ s.eraseDups := by
    intro c hc; have := h.2 c; simp_all +decide [ List.count ] ;
    have h_count_pos : List.countP (fun x => x == c) t > 0 := by
      contrapose! hc; simp_all +decide [ List.countP_eq_zero ] ;
      have h_eraseDups : ∀ {l : List Char}, (∀ a ∈ l, ¬a = c) → c ∉ l.eraseDups := by
        intros l hl; induction' l using List.reverseRecOn with l ih <;> simp_all +decide [ List.eraseDups_append ] ;
        simp_all +decide [ List.removeAll ];
        grind
      exact h_eraseDups hc |> fun h => by simpa using h;
    have h_count_pos_s : List.countP (fun x => x == c) s > 0 := by
      exact lt_of_lt_of_le h_count_pos this
    have h_mem_s : c ∈ s := by
      exact?
    have h_mem_s_eraseDups : c ∈ s.eraseDups := by
      have h_mem_s_eraseDups : ∀ {l : List Char}, c ∈ l → c ∈ l.eraseDups := by
        intros l hl; induction' l using List.reverseRecOn with l ih <;> simp_all +decide [ List.eraseDups_append ] ;
        grind
      exact h_mem_s_eraseDups h_mem_s;
    exact h_mem_s_eraseDups
  have hC_card : t.length = ∑ c ∈ C.toFinset, t.count c := by
    have h_sum_count : ∀ (l : List Char), l.length = ∑ c ∈ l.toFinset, l.count c := by
      exact?
    generalize_proofs at *; (
    convert h_sum_count t using 1
    generalize_proofs at *; (
    congr! 1
    generalize_proofs at *; (
    ext c; simp [C];
    -- By definition of `List.eraseDupsBy.loop`, the list `t.eraseDups` contains exactly the same elements as `t`, but with duplicates removed.
    have h_erase_dups_loop : ∀ (l : List Char) (acc : List Char), c ∈ List.eraseDupsBy.loop (fun x1 x2 => x1 == x2) l acc ↔ c ∈ l ∨ c ∈ acc := by
      intros l acc; induction' l with hd tl ih generalizing acc <;> simp +decide [ List.eraseDupsBy.loop ] ; aesop;
    generalize_proofs at *; (
    simpa using h_erase_dups_loop t []))))
  have h_odd_count : (C.filter (fun c => t.count c % 2 = 1)).length ≤ 1 := by
    convert palindrome_odd_counts t h.1 using 1
  have h_bound : ∀ c ∈ C.toFinset, t.count c ≤ 2 * (s.count c / 2) + (if t.count c % 2 == 1 then 1 else 0) := by
    intro c hc; split_ifs <;> simp_all +decide [ Nat.div_add_mod ] ;
    · have := h.2 c; norm_num at *; omega;
    · have := h.2 c; norm_num at *; omega;
  have h_sum_bound : t.length ≤ ∑ c ∈ C.toFinset, (2 * (s.count c / 2) + (if t.count c % 2 == 1 then 1 else 0)) := by
    exact hC_card.symm ▸ Finset.sum_le_sum h_bound
  have h_final_bound : t.length ≤ 2 * (∑ c ∈ s.eraseDups.toFinset, (s.count c / 2)) + (C.filter (fun c => t.count c % 2 = 1)).length := by
    refine le_trans h_sum_bound ?_ ; simp_all +decide [ Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_ite ] ; ring; (
    refine' add_le_add ( Finset.sum_le_sum_of_subset _ ) _ <;> norm_num [ Finset.subset_iff, List.count ] at * ; aesop; (
    exact le_trans ( Finset.card_le_card <| show _ ⊆ List.toFinset ( List.filter ( fun c => List.countP ( fun x => x == c ) t % 2 = 1 ) t.eraseDups ) from fun x hx => by aesop ) ( List.toFinset_card_le _ ) |> le_trans <| by simp +decide [ List.filter_eq ] ;));
  have h_final_bound' : t.length ≤ 2 * (∑ c ∈ s.eraseDups.toFinset, (s.count c / 2)) + 1 := by
    exact h_final_bound.trans ( add_le_add_left h_odd_count _ )
  exact h_final_bound' |> le_trans <| by
    refine' add_le_add_right ( Nat.mul_le_mul_left _ _ ) _;
    have h_sum_le : ∀ (l : List Char), (∑ c ∈ l.toFinset, List.count c s / 2) ≤ (List.map (fun c => List.count c s / 2) l).sum := by
      intro l; induction l <;> simp +decide [ *, Finset.sum_insert, List.count_cons ] ;
      by_cases h : ‹Char› ∈ ‹List Char›.toFinset <;> simp_all +decide [ Finset.sum_insert ] ; linarith! [ Nat.zero_le ( List.count ‹Char› s / 2 ) ] ;
    generalize_proofs at *; (
    exact h_sum_le _ |> le_trans <| by simp +decide [ List.sum_map_mul_right ] ;); -- This completes the proof.

theorem palindrome_construction (s : List Char) (c : Char) (hc : c ∈ s) (hodd : s.count c % 2 = 1) :
    ∃ t, buildablePalindrome s t ∧ t.length = 2 * (List.map (fun x => s.count x / 2) s.eraseDups).sum + 1 := by
  revert c hc hodd;
  intro c hc hodd
  obtain ⟨t, ht⟩ : ∃ t : List Char, (List.reverse t = t) ∧ (∀ x ∈ t, x ∈ s) ∧ (∀ x ∈ s, t.count x ≤ s.count x) ∧ (∑ x ∈ s.toFinset, t.count x) = 2 * (∑ x ∈ s.toFinset, s.count x / 2) + 1 := by
    -- Let's construct the palindrome `t` as follows:
    -- 1. For each character `x` in `s.eraseDups`, take `k_x = s.count x / 2` copies of `x`.
    -- 2. Concatenate these to form a list `half`.
    -- 3. Let `t = half ++ [c] ++ half.reverse`.
    obtain ⟨half, h_half⟩ : ∃ half : List Char, (∀ x ∈ half, x ∈ s) ∧ (∀ x ∈ s, half.count x = s.count x / 2) ∧ (∑ x ∈ s.toFinset, half.count x) = ∑ x ∈ s.toFinset, s.count x / 2 := by
      use s.toFinset.toList.flatMap (fun x => List.replicate (s.count x / 2) x);
      simp +zetaDelta at *;
      refine' ⟨ fun x hx hx' => hx, fun x hx => _, _ ⟩ <;> simp_all +decide [ List.count_flatMap ];
      · rw [ Finset.sum_eq_single x ] <;> simp +contextual [ List.count_replicate ] ; aesop;
      · simp +decide [ List.count_replicate ];
        exact Finset.sum_congr rfl fun x hx => if_pos <| List.mem_toFinset.mp hx
    generalize_proofs at *; (
    refine' ⟨ half ++ [ c ] ++ half.reverse, _, _, _, _ ⟩ <;> simp_all +decide [ Finset.sum_add_distrib, two_mul ];
    · grind +ring;
    · grind +ring;
    · simp_all +decide [ List.count_cons, Finset.sum_add_distrib ] ; ring;)
  generalize_proofs at *; (
  refine' ⟨ t, _, _ ⟩ <;> simp_all +decide [ List.count ];
  · refine' ⟨ ht.1, _ ⟩
    generalize_proofs at *; (
    intro x; by_cases hx : x ∈ s <;> simp_all +decide [ List.count ] ;
    rw [ List.countP_eq_zero.mpr, List.countP_eq_zero.mpr ] <;> aesop);
  · convert ht.2.2.2 using 1
    generalize_proofs at *;
    · have h_count : ∀ l : List Char, l.length = ∑ x ∈ l.toFinset, List.count x l := by
        exact?
      generalize_proofs at *; (
      rw [ h_count t, Finset.sum_subset ( show t.toFinset ⊆ s.toFinset from fun x hx => by aesop ) ] ; aesop;
      simp +contextual [ List.count_eq_zero ]);
    · -- Since `eraseDups` removes duplicates, the sum over `eraseDups` is the same as the sum over the `Finset`.
      have h_eraseDups_finset : s.eraseDups.toFinset = s.toFinset := by
        -- By definition of `List.eraseDupsBy.loop`, the elements in the resulting list are exactly the elements of the original list, but without duplicates.
        have h_eraseDupsBy_loop : ∀ (l : List Char) (acc : List Char), List.toFinset (List.eraseDupsBy.loop (fun x1 x2 => x1 == x2) l acc) = List.toFinset l ∪ List.toFinset acc := by
          intros l acc; induction' l with hd tl ih generalizing acc <;> simp +decide [ *, List.eraseDupsBy.loop ] ; aesop;
        generalize_proofs at *; (
        simpa using h_eraseDupsBy_loop s [ ])
      generalize_proofs at *; (
      rw [ ← h_eraseDups_finset, List.sum_toFinset ];
      -- By definition of `List.eraseDupsBy.loop`, the list `s.eraseDups` is nodup.
      have h_nodup : ∀ (l : List Char) (acc : List Char), List.Nodup acc → List.Nodup (List.eraseDupsBy.loop (fun x1 x2 => x1 == x2) l acc) := by
        intros l acc hacc; induction' l with x l ih generalizing acc <;> simp_all +decide [ List.eraseDupsBy.loop ] ;
        cases h : acc.any fun x2 => x == x2 <;> simp_all +decide [ List.eraseDupsBy.loop ] ; aesop;
      generalize_proofs at *; (
      exact h_nodup _ _ ( by simp +decide ))))

end AristotleLemmas

theorem goal_11 (s : List Char) (require_1 : True) (i_2 : ℕ) (invariant_lp_outer_i_le_n : i_2 ≤ s.length) (if_neg : ¬s = []) (done_1 : s.length ≤ i_2) (invariant_lp_outer_hasOdd_def : ∃ c ∈ List.take i_2 s, List.count c s % OfNat.ofNat 2 = OfNat.ofNat 1) : postcondition s (OfNat.ofNat 2 * (List.map (fun c => List.count c s / OfNat.ofNat 2) (List.take i_2 s).eraseDups).sum + OfNat.ofNat 1) := by
    constructor;
    · obtain ⟨ c, hc₁, hc₂ ⟩ := invariant_lp_outer_hasOdd_def;
      convert palindrome_construction s c _ _;
      · rw [ List.take_of_length_le ( by linarith ) ];
      · exact List.mem_of_mem_take hc₁;
      · exact hc₂;
    · intros t ht;
      convert palindrome_len_upper_bound s t ht using 1;
      rw [ show List.take i_2 s = s from List.take_of_length_le done_1 ]

noncomputable section AristotleLemmas

/-
If every character in `s` appears an even number of times, then the sum of half-counts multiplied by 2 equals the total length of `s`.
-/
theorem helper_even_counts_formula (s : List Char) (h : ∀ c ∈ s, s.count c % 2 = 0) :
  2 * (s.eraseDups.map (fun c => s.count c / 2)).sum = s.length := by
    -- Since each character in `s` appears an even number of times, the sum of the counts of the characters in `s` is equal to `s.length`.
    have h_sum_counts : List.sum (List.map (fun c => List.count c s) s.eraseDups) = s.length := by
      -- By definition of `List.eraseDupsBy.loop`, we know that `List.eraseDupsBy.loop (fun x1 x2 => x1 == x2) s []` is the list of unique elements in `s`.
      have h_unique : List.sum (List.map (fun c => List.count c s) (List.eraseDupsBy.loop (fun x1 x2 => x1 == x2) s [])) = List.sum (List.map (fun c => List.count c s) s.toFinset.toList) := by
        have h_unique : List.toFinset (List.eraseDupsBy.loop (fun x1 x2 => x1 == x2) s []) = s.toFinset := by
          -- By definition of `List.eraseDupsBy.loop`, we know that `List.eraseDupsBy.loop (fun x1 x2 => x1 == x2) s []` is the list of unique elements in `s`, so their Finsets are equal.
          have h_unique : ∀ (l : List Char) (acc : List Char), List.toFinset (List.eraseDupsBy.loop (fun x1 x2 => x1 == x2) l acc) = List.toFinset l ∪ List.toFinset acc := by
            intros l acc; induction' l with hd tl ih generalizing acc <;> simp_all +decide [ List.eraseDupsBy.loop ] ;
            by_cases h : acc.any fun x2 => hd == x2 <;> simp_all +decide [ Finset.ext_iff ];
            · rw [ List.any_eq_true.mpr ] <;> aesop;
            · intro a; specialize ih ( hd :: acc ) a; by_cases ha : a = hd <;> simp_all +decide [ List.any_eq ] ;
          aesop;
        rw [ ← h_unique, Finset.sum_map_toList ];
        rw [ List.sum_toFinset ];
        -- By definition of `List.eraseDupsBy.loop`, the resulting list is nodup.
        have h_nodup : ∀ (l : List Char) (acc : List Char), List.Nodup acc → List.Nodup (List.eraseDupsBy.loop (fun x1 x2 => x1 == x2) l acc) := by
          intros l acc hacc; induction' l with hd tl ih generalizing acc <;> simp_all +decide [ List.eraseDupsBy.loop ] ;
          cases h : acc.any fun x2 => hd == x2 <;> simp_all +decide [ List.eraseDupsBy.loop ];
          grind;
        exact h_nodup _ _ ( by decide );
      aesop;
    convert h_sum_counts using 1;
    rw [ ← List.sum_map_mul_left ];
    congr! 2;
    exact funext fun x => if hx : x ∈ s then Nat.mul_div_cancel' ( Nat.dvd_of_mod_eq_zero ( h x hx ) ) else by rw [ List.count_eq_zero_of_not_mem hx ] ; norm_num;

theorem exists_palindrome_of_even_counts (s : List Char) (h : ∀ c ∈ s, s.count c % 2 = 0) :
  ∃ t, buildablePalindrome s t ∧ t.length = s.length := by
    by_contra h_contra;
    obtain ⟨t, ht_palindrome, ht_length⟩ : ∃ t : List Char, isPalindrome t ∧ t.length = s.length ∧ ∀ c : Char, t.count c ≤ s.count c := by
      -- Let's denote the list of characters in s by cList.
      set cList := s.toFinset with hcList_def;
      -- For each character c in cList, let's take half of its count in s and append it to the list t.
      have h_half_append : ∃ t : List Char, t.length = (cList.sum (fun c => s.count c)) / 2 ∧ ∀ c : Char, t.count c = s.count c / 2 := by
        use cList.toList.flatMap (fun c => List.replicate (s.count c / 2) c);
        constructor <;> simp +decide [ List.count_flatMap ];
        · rw [ Nat.div_eq_of_eq_mul_left ] <;> norm_num;
          rw [ Finset.sum_mul _ _ _ ] ; exact Finset.sum_congr rfl fun x hx => by rw [ Nat.div_mul_cancel ] ; exact Nat.dvd_of_mod_eq_zero ( h x <| by aesop ) ;
        · intro c; rw [ Finset.sum_eq_single c ] <;> simp_all +decide [ List.count_replicate ] ;
          exact fun hc => by rw [ List.count_eq_zero_of_not_mem hc ] ; decide;
      obtain ⟨t, ht_palindrome, ht_length⟩ := h_half_append;
      refine' ⟨ t ++ t.reverse, _, _, _ ⟩ <;> simp_all +decide [ isPalindrome ];
      · rw [ ← two_mul, Nat.mul_div_cancel' ];
        have h_sum_even : s.length = Finset.sum cList (fun c => s.count c) := by
          exact?;
        exact h_sum_even.symm ▸ Finset.dvd_sum fun x hx => Nat.dvd_of_mod_eq_zero ( h x <| List.mem_toFinset.mp hx );
      · grind;
    exact h_contra ⟨ t, ⟨ ht_palindrome, ht_length.2 ⟩, ht_length.1 ⟩

theorem length_le_of_usesLetters (s t : List Char) (h : usesLetters s t) : t.length ≤ s.length := by
  convert List.Subperm.length_le _;
  exact?

end AristotleLemmas

theorem goal_12 (s : List Char) (require_1 : True) (i_1 : Bool) (i_2 : ℕ) (invariant_lp_outer_i_le_n : i_2 ≤ s.length) (invariant_lp_outer_hasOdd_def : i_1 = true ↔ ∃ c ∈ List.take i_2 s, List.count c s % OfNat.ofNat 2 = OfNat.ofNat 1) (if_neg : ¬s = []) (if_neg_1 : i_1 = false) (done_1 : s.length ≤ i_2) : postcondition s (OfNat.ofNat 2 * (List.map (fun c => List.count c s / OfNat.ofNat 2) (List.take i_2 s).eraseDups).sum) := by
    constructor;
    · convert exists_palindrome_of_even_counts s _ using 1;
      · rw [ show i_2 = s.length by linarith ] ; norm_num [ helper_even_counts_formula ] ;
        rw [ ← helper_even_counts_formula s ];
        grind +ring;
      · grind +ring;
    · intro t ht;
      convert length_le_of_usesLetters s t ht.2 using 1;
      convert helper_even_counts_formula s _;
      · rw [ List.take_of_length_le ( by linarith ) ];
      · grind

end Proof