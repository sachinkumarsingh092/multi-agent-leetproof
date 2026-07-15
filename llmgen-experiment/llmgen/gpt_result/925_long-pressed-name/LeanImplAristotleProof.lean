import Lean

import Mathlib.Tactic

set_option maxHeartbeats 10000000

section Specs
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false
set_option pp.funBinderTypes true

/- Problem Description
    925. Long Pressed Name: determine whether `typed` could result from typing `name` where each key press may repeat a character one or more times.
    **Important: complexity should be O((m + n)^2) time and O(1) space**
    Natural language breakdown:
    1. Inputs are two sequences of characters: `name` and `typed`.
    2. Typing `name` produces characters in the same order as `name`.
    3. Each character `name[k]` is produced at least once in `typed` (normal press) and may be repeated additional times contiguously (long press).
    4. The overall `typed` output must be exactly the concatenation of these contiguous blocks, one block per character position in `name`.
    5. Therefore, `typed` can be partitioned into exactly `name.size` nonempty consecutive segments; the k-th segment contains only copies of `name[k]`.
    6. If such a partition exists, return true; otherwise return false.
-/

-- `segmentAllEq typed start stop c` means: the slice typed[start..stop) is within bounds
-- and every element in that slice equals `c`.
-- We keep this as a Prop (not a reference implementation).
def segmentAllEq (typed : Array Char) (start : Nat) (stop : Nat) (c : Char) : Prop :=
  start ≤ stop ∧ stop ≤ typed.size ∧
    ∀ (i : Nat), start ≤ i ∧ i < stop → typed[i]! = c

-- A partition `breaks` of `typed` into `name.size` consecutive nonempty segments.
-- `breaks` has length `name.size + 1`.
-- Segment k is typed[breaks[k] .. breaks[k+1]) and must be all equal to name[k].
def validBreaks (name : Array Char) (typed : Array Char) (breaks : Array Nat) : Prop :=
  breaks.size = name.size + 1 ∧
  breaks[0]! = 0 ∧
  breaks[name.size]! = typed.size ∧
  (∀ (k : Nat), k < name.size → breaks[k]! < breaks[k+1]!) ∧
  (∀ (k : Nat), k < name.size → segmentAllEq typed breaks[k]! breaks[k+1]! name[k]!)

-- Main correctness predicate: such a valid partition exists.
def isLongPressed (name : Array Char) (typed : Array Char) : Prop :=
  ∃ (breaks : Array Nat), validBreaks name typed breaks

-- No domain restrictions were stated beyond the types.
def precondition (name : Array Char) (typed : Array Char) : Prop :=
  True

-- Result is true iff the long-pressed predicate holds.
def postcondition (name : Array Char) (typed : Array Char) (result : Bool) : Prop :=
  (result = true ↔ isLongPressed name typed)
end Specs

section Impl
def implementation (name : Array Char) (typed : Array Char) : Bool :=
  -- Pure functional scan with O(1) auxiliary space.
  --
  -- State:
  -- * i  : number of characters of `name` already consumed
  -- * ok : validity flag
  --
  -- For each character `t` in `typed`:
  -- * if i < name.size and t = name[i], consume it (i := i+1)
  -- * else if i > 0 and t = name[i-1], accept as a long-press repetition
  -- * else invalid
  --
  -- Additionally, once i = name.size (name fully consumed), we may still
  -- accept further `typed` characters only if they repeat the last character
  -- of `name` (long-press of the final key).
  if h0 : name.size = 0 then
    typed.size = 0
  else
    let last : Char := name[name.size - 1]!

    let step (st : Nat × Bool) (t : Char) : Nat × Bool :=
      let (i, ok) := st
      if !ok then
        (i, false)
      else
        if hi : i < name.size then
          let need := name[i]!
          if t = need then
            (i + 1, true)
          else
            if hprev : 0 < i then
              let prev := name[i - 1]!
              if t = prev then (i, true) else (i, false)
            else
              (i, false)
        else
          -- name already consumed; only allow long-press repetition of last char
          if t = last then (i, true) else (i, false)

    let (iFinal, okFinal) := typed.foldl step (0, true)
    okFinal && (iFinal = name.size)
end Impl

section TestCases
-- Test case 1: Example 1
-- name = "alex", typed = "aaleex" -> true
-- 'a' and 'e' can be long-pressed.
def test1_name : Array Char := #['a', 'l', 'e', 'x']
def test1_typed : Array Char := #['a', 'a', 'l', 'e', 'e', 'x']
def test1_Expected : Bool := true

-- Test case 2: Example 2
-- name = "saeed", typed = "ssaaedd" -> false
-- The second 'e' in name is missing in typed (cannot be explained by long-press).
def test2_name : Array Char := #['s', 'a', 'e', 'e', 'd']
def test2_typed : Array Char := #['s', 's', 'a', 'a', 'e', 'd', 'd']
def test2_Expected : Bool := false

-- Test case 3: Exact match (no long presses)
def test3_name : Array Char := #['a', 'l', 'e', 'x']
def test3_typed : Array Char := #['a', 'l', 'e', 'x']
def test3_Expected : Bool := true

-- Test case 4: Typed shorter than name -> impossible
-- name = "alex", typed = "alx" (missing 'e')
def test4_name : Array Char := #['a', 'l', 'e', 'x']
def test4_typed : Array Char := #['a', 'l', 'x']
def test4_Expected : Bool := false

-- Test case 5: Empty name and empty typed -> valid (zero characters typed)
def test5_name : Array Char := #[]
def test5_typed : Array Char := #[]
def test5_Expected : Bool := true

-- Test case 6: Empty name but nonempty typed -> impossible (extra characters)
def test6_name : Array Char := #[]
def test6_typed : Array Char := #['a']
def test6_Expected : Bool := false

-- Test case 7: Repeated characters in name; typed splits a long run into multiple presses
-- name = "aa", typed = "aaaa" -> true (split into 1+3, 2+2, etc.)
def test7_name : Array Char := #['a', 'a']
def test7_typed : Array Char := #['a', 'a', 'a', 'a']
def test7_Expected : Bool := true

-- Test case 8: Wrong order -> impossible
-- name = "ab", typed = "ba"
def test8_name : Array Char := #['a', 'b']
def test8_typed : Array Char := #['b', 'a']
def test8_Expected : Bool := false

-- Test case 9: Extra trailing different character -> impossible
-- name = "alex", typed = "aaleexy" (extra 'y' at end)
def test9_name : Array Char := #['a', 'l', 'e', 'x']
def test9_typed : Array Char := #['a', 'a', 'l', 'e', 'e', 'x', 'y']
def test9_Expected : Bool := false
end TestCases

/-
  We define a recursive two-pointer checker equivalent to the implementation,
  prove it correct (both directions), and use it to prove the main theorems.
-/
section RecursiveChecker

-- Recursive two-pointer checker.
-- ni = index into name (number of name characters consumed)
-- ti = index into typed (number of typed characters consumed)
-- Returns true iff typed[ti..] can be produced by long-pressing name[ni..],
-- possibly continuing a long-press of name[ni-1] (when ni > 0).
def checkRec (name : Array Char) (typed : Array Char) (ni : Nat) (ti : Nat) : Bool :=
  if hti : ti < typed.size then
    let t := typed[ti]
    if hni : ni < name.size then
      -- Can consume next name char?
      if t = name[ni]! then
        checkRec name typed (ni + 1) (ti + 1)
      -- Long press of previous?
      else if 0 < ni ∧ t = name[ni - 1]! then
        checkRec name typed ni (ti + 1)
      else
        false
    else
      -- name fully consumed, only allow long press of last char
      if t = name[name.size - 1]! then
        checkRec name typed ni (ti + 1)
      else
        false
  else
    -- typed exhausted, need name also exhausted
    ni == name.size
termination_by typed.size - ti

/-
PROBLEM
The implementation equals checkRec when name.size > 0

PROVIDED SOLUTION
Both `implementation` and `checkRec` are two-pointer algorithms processing typed left-to-right while tracking position in name.

The implementation uses Array.foldl with state (i, ok), while checkRec uses recursion on ti.

To prove equivalence:
1. Unfold implementation (since name.size ≠ 0, we're in the else branch)
2. Show the foldl over typed equals checkRec by converting foldl to a recursive form
3. Key: Array.foldl can be expressed as iterating over indices 0, 1, ..., typed.size-1
4. Show that the fold state after processing typed[0..ti) equals the state that checkRec would compute

The fold state (i, ok) after processing typed[0..ti) satisfies:
- If ok = false at any point, it stays false (and checkRec would have returned false earlier)
- If ok = true, then i tracks the name position, exactly matching checkRec's ni

Use Array.foldl_eq_foldl_toList and induction on typed.toList to show the fold result equals checkRec.

Actually the simplest approach: unfold implementation, show the foldl step function is the same as lpStep, and show foldl with lpStep gives the same as checkRec by induction on the list.
-/
lemma implementation_eq_checkRec (name typed : Array Char) (h0 : name.size ≠ 0) :
    implementation name typed = checkRec name typed 0 0 := by
  -- By definition of `checkRec`, we can rewrite the goal in terms of the foldl operation.
  have h_checkRec_foldl : ∀ {name typed : Array Char} {ni ti : Nat}, checkRec name typed ni ti =
    if hti : ti < typed.size then
      let t := typed[ti]!
      if hni : ni < name.size then
        if t = name[ni]! then
          checkRec name typed (ni + 1) (ti + 1)
        else if 0 < ni ∧ t = name[ni - 1]! then
          checkRec name typed ni (ti + 1)
        else
          false
      else
        if t = name[name.size - 1]! then
          checkRec name typed ni (ti + 1)
        else
          false
    else
      ni == name.size := by
        intro name typed ni ti; rw [ checkRec ] ; aesop;
  norm_num +zetaDelta at *;
  have h_checkRec_foldl_eq : ∀ {name typed : Array Char} {ni ti : Nat}, checkRec name typed ni ti = (let step (st : Nat × Bool) (t : Char) : Nat × Bool :=
    let (i, ok) := st
    if !ok then
      (i, false)
    else
      if hi : i < name.size then
        let need := name[i]!
        if t = need then
          (i + 1, true)
        else
          if hprev : 0 < i then
            let prev := name[i - 1]!
            if t = prev then (i, true) else (i, false)
          else
            (i, false)
      else
        -- name already consumed; only allow long-press repetition of last char
        if t = name[name.size - 1]! then (i, true) else (i, false);
    let (iFinal, okFinal) := (typed.toList.drop ti).foldl step (ni, true);
    okFinal && (iFinal = name.size)) := by
      intros name typed ni ti; induction' n : typed.size - ti with n ih generalizing ni ti;
      · rw [ h_checkRec_foldl ];
        rw [ Nat.sub_eq_zero_iff_le ] at n;
        rw [ List.drop_eq_nil_of_le ] <;> norm_num [ n ];
        grind;
      · rw [ h_checkRec_foldl ];
        split_ifs <;> simp +decide [ ‹_› ];
        · rw [ ih ];
          · rw [ show List.drop ti typed.toList = typed[ti]! :: List.drop ( ti + 1 ) typed.toList from ?_ ];
            · simp +decide [ ‹typed[ti]! = name[ni]!› ];
              rw [ if_pos ‹_› ];
            · rw [ List.drop_eq_getElem_cons ];
              all_goals simp +decide [ *, Array.getElem?_eq_getElem ];
          · omega;
        · rw [ show List.drop ti typed.toList = typed[ti]! :: List.drop ( ti + 1 ) typed.toList from ?_, List.foldl_cons ];
          · rw [ ih ( by omega ) ] ; simp +decide [ ‹_› ] ;
            split_ifs <;> simp +decide [ ‹_› ] at *;
            · exact?;
            · intro h;
              contrapose! h;
              induction' ( List.drop ( ti + 1 ) typed.toList ) using List.reverseRecOn with t ts ih <;> simp +decide [ * ];
            · intro h;
              contrapose! h;
              induction' ( List.drop ( ti + 1 ) typed.toList ) using List.reverseRecOn with t ts ih <;> simp +decide [ * ];
          · cases h : typed ; simp +decide [ h ] at *;
            rw [ List.drop_eq_getElem_cons ];
            rw [ List.getElem?_eq_getElem ];
            all_goals norm_cast;
        · rw [ ih ];
          · rw [ show List.drop ti typed.toList = typed[ti]! :: List.drop ( ti + 1 ) typed.toList from ?_ ];
            · simp +decide [ List.foldl ];
              split_ifs ; simp +decide [ ‹_› ];
              rw [ show ( List.foldl ( fun st t => if st.2 = false then ( st.1, false ) else if st.1 < name.size then if t = name[st.1]! then ( st.1 + 1, true ) else if 0 < st.1 then if t = name[st.1 - 1]! then ( st.1, true ) else ( st.1, false ) else ( st.1, false ) else if t = name[name.size - 1]! then ( st.1, true ) else ( st.1, false ) ) ( ni, false ) ( List.drop ( ti + 1 ) typed.toList ) ) = ( ni, false ) from ?_ ] ; simp +decide [ ‹¬typed[ti]! = name[name.size - 1]!› ];
              induction' ( List.drop ( ti + 1 ) typed.toList ) using List.reverseRecOn with t ts ih <;> simp +decide [ * ];
            · rw [ List.drop_eq_getElem_cons ];
              grind;
              simpa;
          · omega;
        · omega;
  unfold implementation; simp +decide [ h_checkRec_foldl_eq ] ;
  grind

/-
PROBLEM
Soundness: checkRec returns true → isLongPressed (with appropriate offset handling)
More precisely: if checkRec name typed ni ti = true,
then there exist breaks for name[ni..] and typed[ti..].
We state the main version for ni=0, ti=0.

PROVIDED SOLUTION
We prove a stronger generalized version by well-founded induction on (typed.size - ti):

For all ni ≤ name.size and ti ≤ typed.size, if checkRec name typed ni ti = true, then:
∃ breaks of size (name.size - ni + 1) such that:
  - breaks[name.size - ni]! = typed.size
  - strictly increasing
  - segments valid for name[ni..name.size-1]
  - when ni = 0: breaks[0]! = ti
  - when ni > 0: breaks[0]! ≥ ti and ∀ j ∈ [ti, breaks[0]!), typed[j]! = name[ni-1]!

Then specialize to ni=0, ti=0, which gives isLongPressed (with breaks[0]! = 0).

Proof of the generalized version by induction on typed.size - ti:

Base case: ti ≥ typed.size. Then checkRec returns (ni == name.size), so ni = name.size.
Use breaks = #[typed.size]. Size = 1 = name.size - name.size + 1. No segments. Conditions trivially hold.

Inductive case: ti < typed.size.

Case A: ni < name.size, typed[ti] = name[ni]. checkRec recurses with (ni+1, ti+1).
  By IH: breaks' of size (name.size - ni - 1 + 1) = (name.size - ni) for (ni+1, ti+1).
  - breaks'[name.size-ni-1]! = typed.size
  - ni+1 > 0 → breaks'[0]! ≥ ti+1 and gap is all name[ni]
  Construct breaks = #[ti] ++ breaks'.
  - breaks.size = 1 + (name.size - ni) = name.size - ni + 1 ✓
  - breaks[0]! = ti, breaks[name.size-ni]! = breaks'[name.size-ni-1]! = typed.size ✓
  - Strictly increasing: ti < breaks'[0]! (since breaks'[0]! ≥ ti+1 > ti) ✓
  - Segment 0: segmentAllEq typed ti breaks'[0]! name[ni]!
    typed[ti] = name[ni] and all j ∈ [ti+1, breaks'[0]!) have typed[j]! = name[ni]! from IH gap. ✓
  - Segments k>0: from IH. ✓
  - ni = 0 → breaks[0]! = ti = 0. ✓
  - ni > 0 → breaks[0]! = ti ≥ ti, gap is empty (breaks[0]! = ti). ✓

Case B: ni < name.size, typed[ti] ≠ name[ni], ni > 0, typed[ti] = name[ni-1]. Long press. Recurse with (ni, ti+1).
  By IH: breaks' for (ni, ti+1).
  - breaks'[0]! ≥ ti+1 and ∀ j ∈ [ti+1, breaks'[0]!), typed[j]! = name[ni-1]!
  Use breaks = breaks'.
  - breaks[0]! ≥ ti+1 > ti ✓
  - Gap: ∀ j ∈ [ti, breaks[0]!), typed[j]! = name[ni-1]!. For j=ti: typed[ti] = name[ni-1] ✓. For j > ti: from IH. ✓

Case C: ni ≥ name.size. typed[ti] = name[name.size-1]. Recurse with (ni, ti+1).
  By IH: breaks' for (name.size, ti+1). breaks' = #[typed.size] (since name.size - name.size + 1 = 1).
  gap: ∀ j ∈ [ti+1, typed.size), typed[j]! = name[name.size-1]!.
  Use breaks = #[typed.size].
  Gap extends: ∀ j ∈ [ti, typed.size), typed[j]! = name[name.size-1]!. j=ti: typed[ti] = name[name.size-1] ✓. j > ti: from IH. ✓
-/
lemma checkRec_sound (name typed : Array Char) (h0 : name.size ≠ 0) :
    checkRec name typed 0 0 = true → isLongPressed name typed := by
  intro h;
  have h_partition : ∃ breaks : Array Nat, validBreaks name typed breaks := by
    have h_rec : ∀ ni ti, ni ≤ name.size → ti ≤ typed.size → checkRec name typed ni ti = true → ∃ breaks : Array Nat, breaks.size = name.size - ni + 1 ∧ breaks[name.size - ni]! = typed.size ∧ (∀ k, k < name.size - ni → breaks[k]! < breaks[k + 1]!) ∧ (∀ k, k < name.size - ni → segmentAllEq typed breaks[k]! breaks[k + 1]! name[ni + k]!) ∧ (ni = 0 → breaks[0]! = ti) ∧ (ni > 0 → breaks[0]! ≥ ti ∧ ∀ j, ti ≤ j ∧ j < breaks[0]! → typed[j]! = name[ni - 1]!) := by
      intros ni ti hni hti h_check
      induction' h : typed.size - ti using Nat.strong_induction_on with m ih generalizing ni ti;
      unfold checkRec at h_check;
      split_ifs at h_check ; simp_all +decide;
      · split_ifs at h_check;
        · obtain ⟨ breaks, hbreaks ⟩ := ih ( typed.size - ( ti + 1 ) ) ( by omega ) ( ni + 1 ) ( ti + 1 ) ( by omega ) ( by omega ) h_check rfl;
          use #[ti] ++ breaks;
          refine' ⟨ _, _, _, _, _ ⟩;
          · grind;
          · rw [ show name.size - ni = name.size - ( ni + 1 ) + 1 by omega ];
            cases breaks ; aesop;
          · intro k hk; rcases k with ( _ | k ) <;> simp_all +decide [ Nat.sub_add_comm ] ;
            · grind;
            · convert hbreaks.2.2.1 k ( by omega ) using 1;
              · cases breaks ; aesop;
              · cases breaks ; aesop;
          · intro k hk; rcases k with ( _ | k ) <;> simp_all +decide [ Nat.sub_add_comm ] ;
            · refine' ⟨ _, _, _ ⟩;
              · grind;
              · have h_le : ∀ k < breaks.size, breaks[k]! ≤ breaks[breaks.size - 1]! := by
                  intro k hk;
                  have h_le : ∀ k l, k ≤ l → l < breaks.size → breaks[k]! ≤ breaks[l]! := by
                    intros k l hkl hl;
                    induction' hkl with k hk ih;
                    · norm_num;
                    · exact le_trans ( ih ( Nat.lt_of_succ_lt hl ) ) ( le_of_lt ( hbreaks.2.2.1 k ( by omega ) ) );
                  exact h_le _ _ ( Nat.le_sub_one_of_lt hk ) ( Nat.sub_lt ( by linarith ) zero_lt_one );
                grind;
              · intro i hi; cases lt_or_eq_of_le hi.1 <;> aesop;
            · convert hbreaks.2.2.2.1 k ( by omega ) using 1;
              · cases breaks ; aesop;
              · cases breaks ; aesop;
              · ac_rfl;
          · cases breaks ; aesop;
        · obtain ⟨breaks, hbreaks⟩ := ih (typed.size - (ti + 1)) (by
          omega) ni (ti + 1) hni (by
          linarith) h_check.right (by
          rfl);
          grind;
      · grind;
      · use #[typed.size];
        grind
    -- Apply the recursive checker with ni=0 and ti=0.
    specialize h_rec 0 0 (Nat.zero_le _) (Nat.zero_le _) h;
    unfold validBreaks; aesop;
  exact h_partition

-- The key predicate for completeness:
-- There exists a partition of typed from some position ≥ ti into segments
-- for name[ni..name.size-1], with a gap of name[ni-1] chars before the first segment.
def hasSolutionFrom (name typed : Array Char) (ni ti : Nat) : Prop :=
  ∃ (breaks : Array Nat),
    breaks.size = name.size - ni + 1 ∧
    breaks[name.size - ni]! = typed.size ∧
    (∀ k, k < name.size - ni → breaks[k]! < breaks[k + 1]!) ∧
    (∀ k, k < name.size - ni → segmentAllEq typed (breaks[k]!) (breaks[k + 1]!) (name[ni + k]!)) ∧
    (ni = 0 → breaks[0]! = ti) ∧
    (ni > 0 → breaks[0]! ≥ ti ∧ (∀ j, ti ≤ j → j < breaks[0]! → typed[j]! = name[ni - 1]!))

/-
PROBLEM
isLongPressed implies hasSolutionFrom at (0, 0)

PROVIDED SOLUTION
This is straightforward repackaging. Given isLongPressed name typed, we have breaks with validBreaks name typed breaks.

validBreaks gives: breaks.size = name.size + 1, breaks[0]! = 0, breaks[name.size]! = typed.size, strictly increasing, segments valid for name[k] at breaks[k]..breaks[k+1].

hasSolutionFrom name typed 0 0 needs: ∃ breaks with breaks.size = name.size - 0 + 1 = name.size + 1, breaks[name.size]! = typed.size, strictly increasing, segments valid (with ni+k = 0+k = k), (0 = 0 → breaks[0]! = 0), and the ni > 0 clause is vacuously true.

So just use the same breaks array! The conditions match directly.
- breaks.size = name.size + 1 ✓
- breaks[name.size-0]! = breaks[name.size]! = typed.size ✓
- k < name.size → breaks[k]! < breaks[k+1]! ✓ (same)
- k < name.size → segmentAllEq typed breaks[k]! breaks[k+1]! name[0+k]! = name[k]! ✓ (same)
- 0 = 0 → breaks[0]! = 0 ✓ (from validBreaks)
- 0 > 0 is false, so vacuously true ✓

Just unfold the definitions, destructure the hypothesis, and provide the same witness.
-/
lemma isLP_to_hasSol (name typed : Array Char) (h0 : 0 < name.size) :
    isLongPressed name typed → hasSolutionFrom name typed 0 0 := by
  intro h
  obtain ⟨breaks, h_valid⟩ := h
  use breaks;
  cases h_valid ; aesop

/-
PROBLEM
hasSolutionFrom implies checkRec returns true

PROVIDED SOLUTION
Prove by well-founded induction on typed.size - ti.

Unfold checkRec and split on whether ti < typed.size.

Base case: ti ≥ typed.size (¬ ti < typed.size):
  checkRec returns (ni == name.size). We need ni = name.size.
  From hasSolutionFrom: breaks with breaks[0]! ≥ ti (when ni > 0) or breaks[0]! = ti (when ni = 0).
  And breaks[name.size-ni]! = typed.size, and strictly increasing.

  When ni = 0: breaks[0]! = ti ≥ typed.size = breaks[name.size]!. Since breaks is strictly increasing with name.size entries, and breaks[0]! ≥ breaks[name.size]!, we need name.size = 0, contradicting h0.

  Actually wait, when ni = 0: breaks[0]! = 0 (since ti = 0 and ni = 0 → breaks[0]! = ti = 0). But hti says ti ≤ typed.size and ¬(ti < typed.size) means ti = typed.size. So breaks[0]! = typed.size. And breaks[name.size]! = typed.size. Since breaks is strictly increasing with name.size entries between breaks[0] and breaks[name.size], if name.size > 0 then breaks[0]! < breaks[1]! ≤ ... ≤ breaks[name.size]! = typed.size = breaks[0]!. Contradiction. So name.size = 0, contradicting h0.

  Wait, this case shouldn't happen when ni = 0 and ti = typed.size > 0. Actually, ti can be typed.size when ni = 0 if typed.size = 0. Then name.size = 0 follows.

  OK the point is: when ti ≥ typed.size, the strictly increasing property forces ni = name.size.

  When ni > 0: breaks[0]! ≥ ti ≥ typed.size = breaks[name.size-ni]!. If name.size > ni, breaks[0]! < breaks[1]! < ... < breaks[name.size-ni]! = typed.size ≤ breaks[0]!. Contradiction. So name.size = ni.

  When ni = 0: same argument. breaks[0]! = ti ≥ typed.size = breaks[name.size]!. If name.size > 0, contradiction. But h0 says name.size > 0. So... this case is impossible when ni = 0, ti ≥ typed.size, and name.size > 0.

  Actually this case CAN happen if typed is empty and ni = name.size. Then ti = 0 = typed.size, and checkRec returns (name.size == name.size) = true.

  So: when ti ≥ typed.size, the invariant forces ni = name.size, and checkRec returns true. ✓

Inductive case: ti < typed.size.

Case ni < name.size:
  From hasSolutionFrom: breaks with breaks[0]! ≥ ti (or = ti when ni=0).

  Sub-case breaks[0]! = ti:
    Segment 0: segmentAllEq typed ti breaks[1]! name[ni]!.
    So typed[ti]! = name[ni]! (since ti ≤ ti < breaks[1]!).

    checkRec: typed[ti] = name[ni]! (note: typed[ti] the getElem vs typed[ti]! the getElem!; they should be equal when ti < typed.size).

    So checkRec recurses to (ni+1, ti+1).

    Need hasSolutionFrom for (ni+1, ti+1):
    Use breaks' where breaks'[k] = breaks[k+1] (drop first element).
    breaks'.size = breaks.size - 1 = name.size - ni + 1 - 1 = name.size - ni = name.size - (ni+1) + 1.
    breaks'[name.size-(ni+1)]! = breaks[name.size-ni]! = typed.size.
    Strictly increasing: inherited.
    Segments: k < name.size-(ni+1) → segmentAllEq typed breaks'[k]! breaks'[k+1]! name[(ni+1)+k]!
      = segmentAllEq typed breaks[k+1]! breaks[k+2]! name[ni+1+k]!. From original: breaks[k+1]! etc for segment k+1. ✓
    ni+1 > 0: breaks'[0]! = breaks[1]! ≥ ti+1 (since breaks[0]! = ti < breaks[1]! and they're naturals).
    Gap: ∀ j, ti+1 ≤ j < breaks[1]! → typed[j]! = name[ni]! = name[(ni+1)-1]!.
      From segment 0: segmentAllEq typed ti breaks[1]! name[ni]!, so for ti ≤ j < breaks[1]!, typed[j]! = name[ni]!. In particular for ti+1 ≤ j < breaks[1]!. ✓
    Apply IH (typed.size - (ti+1) < typed.size - ti). ✓

  Sub-case breaks[0]! > ti (only possible when ni > 0):
    From gap: typed[ti]! = name[ni-1]! (since ti ≤ ti < breaks[0]!).

    Sub-sub-case typed[ti]! = name[ni]! (i.e., name[ni-1]! = name[ni]!):
      checkRec sees typed[ti] = name[ni], consumes, recurses to (ni+1, ti+1).
      Need hasSolutionFrom for (ni+1, ti+1).
      Use breaks' = breaks (tail won't work since breaks.size = name.size-ni+1 but we need name.size-(ni+1)+1 = name.size-ni).
      Actually use breaks' = Array.extract breaks 1 breaks.size (drop first element).
      breaks'.size = name.size-ni = name.size-(ni+1)+1.
      breaks'[name.size-(ni+1)]! = breaks[name.size-ni]! = typed.size.
      Strictly increasing: inherited.
      Segments: from original segments (shifted by 1).
      ni+1 > 0: breaks'[0]! = breaks[1]! > breaks[0]! > ti, so breaks'[0]! > ti+1? Not necessarily. breaks[1]! ≥ breaks[0]! + 1 > ti + 1. Actually breaks[0]! > ti and breaks[1]! > breaks[0]!, so breaks[1]! ≥ breaks[0]! + 1 ≥ ti + 2 > ti + 1. So breaks'[0]! ≥ ti + 2 > ti + 1. ✓
      Gap: ∀ j, ti+1 ≤ j < breaks[1]! → typed[j]! = name[ni]!.
        For j < breaks[0]!: typed[j]! = name[ni-1]! = name[ni]! (from original gap and name[ni-1]=name[ni]).
        For j ≥ breaks[0]!: typed[j]! = name[ni]! (from segment 0). ✓
      Apply IH. ✓

    Sub-sub-case typed[ti]! ≠ name[ni]!:
      typed[ti]! = name[ni-1]! ≠ name[ni]!.
      checkRec: typed[ti] ≠ name[ni]. Check long press: 0 < ni (yes) ∧ typed[ti] = name[ni-1] (yes).
      Recurse to (ni, ti+1).
      Need hasSolutionFrom for (ni, ti+1).
      Use same breaks. breaks[0]! > ti, so breaks[0]! ≥ ti+1.
      Gap: ∀ j, ti+1 ≤ j < breaks[0]! → typed[j]! = name[ni-1]! (subset of original gap). ✓
      Apply IH. ✓

Case ni ≥ name.size (ni = name.size):
  hasSolutionFrom: breaks has size 1. breaks[0]! = typed.size.
  ni > 0 (since name.size > 0): breaks[0]! ≥ ti and gap: ∀ j, ti ≤ j < typed.size → typed[j]! = name[name.size-1]!.
  ti < typed.size: typed[ti]! = name[name.size-1]!.
  checkRec: ni ≥ name.size. Check typed[ti] = name[name.size-1]!.
  Note: typed[ti] (getElem) should equal typed[ti]! (getElem!) when ti < typed.size.
  So checkRec recurses to (name.size, ti+1).
  hasSolutionFrom for (name.size, ti+1): same breaks. Gap shrinks. ✓
  Apply IH. ✓

KEY IMPLEMENTATION DETAIL: When checkRec checks `typed[ti] = name[ni]!` (using getElem for typed[ti] but getElem! for name[ni]!), note that typed[ti] uses the proof hti : ti < typed.size via getElem. We need `typed[ti] = typed[ti]!` which holds when ti < typed.size. Use Array.getElem!_pos or similar.
-/
lemma hasSol_to_checkRec (name typed : Array Char) (ni ti : Nat)
    (hni : ni ≤ name.size) (hti : ti ≤ typed.size) (h0 : 0 < name.size)
    (hsol : hasSolutionFrom name typed ni ti) :
    checkRec name typed ni ti = true := by
  -- By induction on the size of the typed array, we can show that if there's a valid partition (hasSolutionFrom), then the checkRec function will return true.
  induction' n : typed.size - ti with n ih generalizing ni ti;
  · obtain ⟨ breaks, hbreaks ⟩ := hsol;
    cases hni.eq_or_lt <;> simp_all +decide [ Nat.sub_eq_iff_eq_add ];
    · unfold checkRec; aesop;
    · have h_contra : ∀ k < name.size - ni, breaks[k]! < breaks[k + 1]! := by
        exact hbreaks.2.2.1;
      have h_contra : ∀ k < name.size - ni + 1, breaks[k]! ≥ breaks[0]! + k := by
        intro k hk;
        induction' k with k ih;
        · norm_num;
        · linarith [ ih ( Nat.lt_of_succ_lt hk ), h_contra k ( Nat.lt_of_succ_lt_succ hk ) ];
      grind +ring;
  · obtain ⟨ breaks, h1, h2, h3, h4, h5 ⟩ := hsol;
    unfold checkRec; split_ifs <;> simp_all +decide [ Nat.sub_add_comm hni ] ;
    · split_ifs <;> simp_all +decide [ segmentAllEq ];
      · convert ih ( ni + 1 ) ( ti + 1 ) ( by linarith ) ( by omega ) _ _ using 1;
        · use breaks.drop 1;
          simp_all +decide [ Nat.sub_sub, add_comm ];
          refine' ⟨ _, _, _, _, _ ⟩
          all_goals generalize_proofs at *;
          · omega;
          · grind +ring;
          · grind +ring;
          · intro k hk; specialize h4 ( k + 1 ) ( by omega ) ; simp_all +decide [ add_comm, add_left_comm, add_assoc ] ;
            refine' ⟨ _, _, _ ⟩
            all_goals generalize_proofs at *;
            · grind;
            · grind +ring;
            · grind +ring;
          · rcases ni <;> simp_all +decide [ Nat.sub_add_comm ];
            · grind +ring;
            · grind +ring;
        · omega;
      · have h_gap : typed[ti]! = name[ni - 1]! := by
          specialize h4 0 ; simp_all +decide [ Nat.sub_add_comm ] ;
          grind +ring
        generalize_proofs at *; (
        by_cases hni_pos : 0 < ni <;> simp_all +decide [ Array.getElem?_eq_getElem ];
        convert ih ni ( ti + 1 ) hni ( by linarith ) _ _ using 1
        generalize_proofs at *; (
        use breaks
        generalize_proofs at *; (
        refine' ⟨ h1, _, _, _, _, _ ⟩ <;> simp_all +decide [ segmentAllEq ];
        · exact fun k hk i hi₁ hi₂ => h4 k hk |>.2.2 i hi₁ hi₂ ▸ rfl;
        · linarith;
        · specialize h4 0 ; simp_all +decide [ Nat.sub_add_comm hni ] ; (
          grind)));
        omega);
    · cases lt_or_eq_of_le hni <;> simp_all +decide [ Nat.sub_eq_zero_of_le ];
      -- Apply the induction hypothesis with the appropriate parameters.
      apply ih name.size (ti + 1) (by linarith) (by linarith) (by
      use #[typed.size];
      grind) (by
      omega)

-- Completeness: isLongPressed → checkRec returns true
lemma checkRec_complete (name typed : Array Char) (h0 : name.size ≠ 0) :
    isLongPressed name typed → checkRec name typed 0 0 = true := by
  intro hlp
  exact hasSol_to_checkRec name typed 0 0 (Nat.zero_le _) (Nat.zero_le _) (by omega)
    (isLP_to_hasSol name typed (by omega) hlp)

end RecursiveChecker

section Proof

theorem correctness_goal_1_0 (name : Array Char) (typed : Array Char)
    (h_precond : precondition name typed) (h0 : ¬name.size = 0) :
    implementation name typed = true → isLongPressed name typed := by
  rw [implementation_eq_checkRec name typed h0]
  exact checkRec_sound name typed h0

theorem correctness_goal_1_1 (name : Array Char) (typed : Array Char)
    (h_precond : precondition name typed) (h0 : ¬name.size = 0)
    (h_sound : implementation name typed = true → isLongPressed name typed) :
    isLongPressed name typed → implementation name typed = true := by
  rw [implementation_eq_checkRec name typed h0]
  exact checkRec_complete name typed h0

end Proof