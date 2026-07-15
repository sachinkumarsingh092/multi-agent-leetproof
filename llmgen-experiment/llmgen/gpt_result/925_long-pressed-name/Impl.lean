import Velvet.Std
import Extensions.Tactics
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false
set_option pp.funBinderTypes true
set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

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

section Specs
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
method LongPressedName (name : Array Char) (typed : Array Char)
  return (result : Bool)
  require precondition name typed
  ensures postcondition name typed result
  do
  -- Greedy two-pointer scan over runs of equal characters.
  -- For each run of a character in `name`, `typed` must have a run of the same
  -- character with length at least as large.

  -- Empty name: only valid if typed is also empty (zero segments).
  if name.size = 0 then
    if typed.size = 0 then
      return true
    else
      return false

  let mut i : Nat := 0
  let mut j : Nat := 0
  let mut ok : Bool := true

  while (ok = true ∧ i < name.size)
    -- Bounds needed for safe indexing and arithmetic measures.
    invariant "lp_outer_bounds" (i ≤ name.size ∧ j ≤ typed.size)
    -- Soundness for the processed prefix: when `ok` is still true, the already-consumed
    -- prefix typed[0..j) can be partitioned into i nonempty segments matching name[0..i).
    invariant "lp_outer_sound_prefix"
      (ok = true →
        ∃ (breaks : Array Nat),
          breaks.size = i + 1 ∧
          breaks[0]! = 0 ∧
          breaks[i]! = j ∧
          (∀ (k : Nat), k < i → breaks[k]! < breaks[k+1]!) ∧
          (∀ (k : Nat), k < i → segmentAllEq typed breaks[k]! breaks[k+1]! (name[k]!)))
    -- Completeness hook: if a full valid partition exists, then `ok` stays true and
    -- the current cursor `j` coincides with the partition boundary at position `i`.
    invariant "lp_outer_complete"
      (isLongPressed name typed →
        ok = true ∧
        ∃ (breaks : Array Nat), validBreaks name typed breaks ∧ breaks[i]! = j)
    done_with (ok = false ∨ i = name.size)
    -- Termination: either we make progress in i/j, or we set ok := false and exit.
    decreasing (if ok then (name.size - i) + (typed.size - j) + 1 else 0)
  do
    -- If typed is exhausted before name, impossible.
    if j >= typed.size then
      ok := false
    else
      let c : Char := name[i]!
      if typed[j]! != c then
        ok := false
      else
        -- Consume a maximal run of `c` in name starting at i.
        let mut nextI : Nat := i
        while (nextI < name.size ∧ name[nextI]! = c)
          invariant "lp_nameRun_bounds" (i ≤ nextI ∧ nextI ≤ name.size)
          invariant "lp_nameRun_allEq" (∀ (k : Nat), i ≤ k ∧ k < nextI → name[k]! = c)
          -- `nextI` increases and is bounded by `name.size`.
          decreasing name.size - nextI
        do
          nextI := nextI + 1

        -- Consume a maximal run of `c` in typed starting at j.
        let mut nextJ : Nat := j
        while (nextJ < typed.size ∧ typed[nextJ]! = c)
          invariant "lp_typedRun_bounds" (j ≤ nextJ ∧ nextJ ≤ typed.size)
          invariant "lp_typedRun_allEq" (∀ (k : Nat), j ≤ k ∧ k < nextJ → typed[k]! = c)
          decreasing typed.size - nextJ
        do
          nextJ := nextJ + 1

        let cntName : Nat := nextI - i
        let cntTyped : Nat := nextJ - j

        if cntTyped < cntName then
          ok := false
        else
          i := nextI
          j := nextJ

  if (ok = true ∧ i = name.size ∧ j = typed.size) then
    return true
  else
    return false
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

section Assertions
-- Test case 1

#assert_same_evaluation #[((LongPressedName test1_name test1_typed).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((LongPressedName test2_name test2_typed).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((LongPressedName test3_name test3_typed).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((LongPressedName test4_name test4_typed).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((LongPressedName test5_name test5_typed).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((LongPressedName test6_name test6_typed).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((LongPressedName test7_name test7_typed).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((LongPressedName test8_name test8_typed).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((LongPressedName test9_name test9_typed).run), DivM.res test9_Expected ]
end Assertions

section Pbt
velvet_plausible_test LongPressedName (config := { maxMs := some 5000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000

theorem goal_0
    (name : Array Char)
    (typed : Array Char)
    (if_pos : name = #[])
    (if_pos_1 : typed = #[])
    : postcondition name typed true := by
  -- simplify the postcondition using the given equalities
  simp [postcondition, if_pos, if_pos_1, isLongPressed]
  refine ⟨#[0], ?_⟩
  simp [validBreaks, segmentAllEq]

theorem goal_1
    (name : Array Char)
    (typed : Array Char)
    (i : ℕ)
    (j : ℕ)
    (a : i ≤ name.size)
    (nextI : ℕ)
    (a_4 : i ≤ nextI)
    (a_5 : nextI ≤ name.size)
    (invariant_lp_nameRun_allEq : ∀ (k : ℕ), i ≤ k → k < nextI → name[k]! = name[i]!)
    (nextJ : ℕ)
    (a_6 : j ≤ nextJ)
    (if_pos : nextJ - j < nextI - i)
    (done_3 : nextJ < typed.size → ¬typed[nextJ]! = name[i]!)
    (invariant_lp_outer_complete : ∀ (x : Array ℕ), x.size = name.size + OfNat.ofNat 1 → x[OfNat.ofNat 0]! = OfNat.ofNat 0 → x[name.size]! = typed.size → (∀ k < name.size, x[k]! < x[k + OfNat.ofNat 1]!) → (∀ k < name.size, x[k]! ≤ x[k + OfNat.ofNat 1]! ∧ x[k + OfNat.ofNat 1]! ≤ typed.size ∧ ∀ (i : ℕ), x[k]! ≤ i → i < x[k + OfNat.ofNat 1]! → typed[i]! = name[k]!) → ∃ (breaks : Array ℕ), (breaks.size = name.size + OfNat.ofNat 1 ∧ breaks[OfNat.ofNat 0]! = OfNat.ofNat 0 ∧ breaks[name.size]! = typed.size ∧ (∀ k < name.size, breaks[k]! < breaks[k + OfNat.ofNat 1]!) ∧ ∀ k < name.size, breaks[k]! ≤ breaks[k + OfNat.ofNat 1]! ∧ breaks[k + OfNat.ofNat 1]! ≤ typed.size ∧ ∀ (i : ℕ), breaks[k]! ≤ i → i < breaks[k + OfNat.ofNat 1]! → typed[i]! = name[k]!) ∧ breaks[i]! = j)
    : ∀ (x : Array ℕ), x.size = name.size + OfNat.ofNat 1 → x[OfNat.ofNat 0]! = OfNat.ofNat 0 → x[name.size]! = typed.size → (∀ k < name.size, x[k]! < x[k + OfNat.ofNat 1]!) → ∃ x_1 < name.size, x[x_1]! ≤ x[x_1 + OfNat.ofNat 1]! → x[x_1 + OfNat.ofNat 1]! ≤ typed.size → ∃ (x_2 : ℕ), x[x_1]! ≤ x_2 ∧ x_2 < x[x_1 + OfNat.ofNat 1]! ∧ ¬typed[x_2]! = name[x_1]! := by
  intro x hxsize hx0 hxLast hxInc
  classical

  -- Monotonicity of `x` derived from strict step increases.
  have x_le_of_le : ∀ {m n : Nat}, m ≤ n → n ≤ name.size → x[m]! ≤ x[n]! := by
    intro m n hmn hn
    have hP : ∀ n (hmn : m ≤ n), n ≤ name.size → x[m]! ≤ x[n]! := by
      refine Nat.le_induction (m := m)
        (P := fun n hmn => n ≤ name.size → x[m]! ≤ x[n]! ) ?_ ?_
      · intro _
        exact le_rfl
      · intro n hmn ih hnSucc
        have hn' : n ≤ name.size := Nat.le_trans (Nat.le_succ n) hnSucc
        have hnlt : n < name.size := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hnSucc
        have hm_le_n : x[m]! ≤ x[n]! := ih hn'
        have hn_le_succ : x[n]! ≤ x[n+1]! := Nat.le_of_lt (hxInc n hnlt)
        exact le_trans hm_le_n hn_le_succ
    exact hP n hmn hn

  -- Stronger mismatch statement: some segment contains a mismatching character.
  have hmismatch : ∃ k < name.size, ∃ t : Nat,
      x[k]! ≤ t ∧ t < x[k+1]! ∧ ¬ typed[t]! = name[k]! := by
    by_contra hNo
    have hAllEq : ∀ k, k < name.size → ∀ t : Nat, x[k]! ≤ t → t < x[k+1]! → typed[t]! = name[k]! := by
      push_neg at hNo
      simpa using hNo

    have hSeg : ∀ k, k < name.size →
        x[k]! ≤ x[k+1]! ∧ x[k+1]! ≤ typed.size ∧
          ∀ t : Nat, x[k]! ≤ t → t < x[k+1]! → typed[t]! = name[k]! := by
      intro k hk
      refine ⟨Nat.le_of_lt (hxInc k hk), ?_, hAllEq k hk⟩
      have hk1 : k+1 ≤ name.size := Nat.succ_le_of_lt hk
      have : x[k+1]! ≤ x[name.size]! := x_le_of_le hk1 (le_rfl)
      simpa [hxLast] using this

    obtain ⟨breaks, hbreaks, hbreaks_i⟩ :=
      invariant_lp_outer_complete x hxsize hx0 hxLast hxInc (by
        intro k hk
        simpa using hSeg k hk)

    rcases hbreaks with ⟨hbsz, hb0, hbLast, hbStrict, hbAll⟩
    have hbEq : ∀ k, k < name.size → ∀ t : Nat, breaks[k]! ≤ t → t < breaks[k+1]! → typed[t]! = name[k]! := by
      intro k hk
      have h := hbAll k hk
      exact h.2.2

    -- Monotonicity of breaks.
    have breaks_le_of_le : ∀ {m n : Nat}, m ≤ n → n ≤ name.size → breaks[m]! ≤ breaks[n]! := by
      intro m n hmn hn
      have hP : ∀ n (hmn : m ≤ n), n ≤ name.size → breaks[m]! ≤ breaks[n]! := by
        refine Nat.le_induction (m := m)
          (P := fun n hmn => n ≤ name.size → breaks[m]! ≤ breaks[n]! )
          (base := by
            intro _
            exact le_rfl)
          (succ := by
            intro n hmn ih hnSucc
            have hn' : n ≤ name.size := Nat.le_trans (Nat.le_succ n) hnSucc
            have hnlt : n < name.size := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hnSucc
            have hm_le_n : breaks[m]! ≤ breaks[n]! := ih hn'
            have hn_le_succ : breaks[n]! ≤ breaks[n+1]! := Nat.le_of_lt (hbStrict n hnlt)
            exact le_trans hm_le_n hn_le_succ)
      exact hP n hmn hn

    -- From strictness, each step increases by at least 1.
    have hb_step : ∀ k, k < name.size → breaks[k]! + 1 ≤ breaks[k+1]! := by
      intro k hk
      have hlt : breaks[k]! < breaks[k+1]! := hbStrict k hk
      simpa [Nat.succ_eq_add_one] using (Nat.succ_le_of_lt hlt)

    -- Advancing n indices from i increases the boundary by at least n.
    have hb_add_le : ∀ n : Nat, i + n ≤ name.size → breaks[i]! + n ≤ breaks[i+n]! := by
      intro n hn
      induction n with
      | zero =>
          simp
      | succ n ih =>
          have hn' : i + n ≤ name.size := by
            have : i + n ≤ i + (n+1) := by
              simpa [Nat.add_assoc] using (Nat.le_succ (i+n))
            exact le_trans this hn
          have ih' : breaks[i]! + n ≤ breaks[i+n]! := ih hn'
          have hltIdx : i + n < name.size := Nat.lt_of_lt_of_le (Nat.lt_succ_self (i+n)) (by
            simpa [Nat.add_assoc] using hn)
          have hstep : breaks[i+n]! + 1 ≤ breaks[i+n+1]! := hb_step (i+n) hltIdx
          calc
            breaks[i]! + (n+1) = (breaks[i]! + n) + 1 := by
              simp [Nat.add_assoc]
            _ ≤ breaks[i+n]! + 1 := by
              exact Nat.add_le_add_right ih' 1
            _ ≤ breaks[i+n+1]! := hstep

    have hiNext : i + (nextI - i) = nextI := Nat.add_sub_of_le a_4
    have hnNext : i + (nextI - i) ≤ name.size := by
      simpa [hiNext] using a_5
    have hbreaks_nextI_lower : breaks[i]! + (nextI - i) ≤ breaks[nextI]! := by
      simpa [hiNext] using (hb_add_le (nextI - i) hnNext)

    have hbreaks_i' : breaks[i]! = j := hbreaks_i
    have hJplus : j + (nextI - i) ≤ breaks[nextI]! := by
      simpa [hbreaks_i'] using hbreaks_nextI_lower

    -- Key: breaks[nextI] cannot pass nextJ.
    have hbreaks_nextI_le_nextJ : breaks[nextI]! ≤ nextJ := by
      by_contra hgt
      have hlt : nextJ < breaks[nextI]! := Nat.lt_of_not_ge hgt
      -- nextJ is in bounds
      have hbreaks_nextI_le_typed : breaks[nextI]! ≤ typed.size := by
        have : breaks[nextI]! ≤ breaks[name.size]! := breaks_le_of_le a_5 (le_rfl)
        simpa [hbLast] using this
      have hnextJ_lt_typed : nextJ < typed.size := Nat.lt_of_lt_of_le hlt hbreaks_nextI_le_typed

      -- Find the first boundary strictly greater than nextJ.
      let p : Nat → Prop := fun m => nextJ < breaks[m]!
      have hp_ex : ∃ m, p m := ⟨nextI, by simpa [p] using hlt⟩
      let m : Nat := Nat.find hp_ex
      have hm_spec : p m := Nat.find_spec hp_ex
      have hm_le_nextI : m ≤ nextI := Nat.find_min' hp_ex (by simpa [p] using hlt)

      -- Show i < m (since breaks[i]=j ≤ nextJ).
      have him : i < m := by
        by_contra hmi
        have hmi' : m ≤ i := Nat.le_of_not_gt hmi
        have hbreaks_m_le_i : breaks[m]! ≤ breaks[i]! := breaks_le_of_le hmi' a
        have h1 : nextJ < breaks[i]! := lt_of_lt_of_le (by simpa [p, m] using hm_spec) hbreaks_m_le_i
        have h2 : ¬ nextJ < breaks[i]! := by
          simpa [hbreaks_i'] using (Nat.not_lt_of_ge a_6)
        exact h2 h1

      have hm_pos : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le i) him
      have hm1 : 1 ≤ m := Nat.succ_le_of_lt hm_pos
      let k : Nat := m - 1
      have hk_succ : k + 1 = m := Nat.sub_add_cancel hm1

      -- k lies in [i, nextI)
      have hk_lt_nextI : k < nextI := by
        have : k + 1 ≤ nextI := by simpa [hk_succ] using hm_le_nextI
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self k) this
      have hi_le_k : i ≤ k := by
        have : i < k + 1 := by simpa [hk_succ] using him
        exact Nat.le_of_lt_succ this

      -- breaks[k] ≤ nextJ < breaks[k+1]
      have hnextJ_lt_bk1 : nextJ < breaks[k+1]! := by
        simpa [hk_succ, k, p] using hm_spec
      have hk_lt_m : k < m := by
        have : m - 1 < m := Nat.sub_lt (Nat.succ_le_of_lt hm_pos) (Nat.succ_pos 0)
        simpa [k] using this
      have hnot_nextJ_lt_bk : ¬ nextJ < breaks[k]! := by
        have : ¬ p k := Nat.find_min hp_ex hk_lt_m
        simpa [p] using this
      have hb_k_le_nextJ : breaks[k]! ≤ nextJ := Nat.le_of_not_gt hnot_nextJ_lt_bk

      have hk_lt_name : k < name.size := lt_of_lt_of_le hk_lt_nextI a_5
      have htyped_nextJ_eq_namek : typed[nextJ]! = name[k]! :=
        hbEq k hk_lt_name nextJ hb_k_le_nextJ (by simpa using hnextJ_lt_bk1)
      have hnamek : name[k]! = name[i]! := invariant_lp_nameRun_allEq k hi_le_k hk_lt_nextI
      have htyped_nextJ_eq : typed[nextJ]! = name[i]! := by simpa [hnamek] using htyped_nextJ_eq_namek
      exact (done_3 hnextJ_lt_typed) (by simpa [htyped_nextJ_eq])

    -- Now derive cntName ≤ cntTyped, contradicting if_pos.
    have hJplus_le_nextJ : j + (nextI - i) ≤ nextJ := le_trans hJplus hbreaks_nextI_le_nextJ
    have hcnt : nextI - i ≤ nextJ - j := by
      have h := (Nat.le_sub_iff_add_le' (n := nextI - i) (k := j) (m := nextJ) a_6).2 ?_
      · simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
      · simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hJplus_le_nextJ
    exact (Nat.not_lt_of_ge hcnt) if_pos

  -- Conclude the original statement from the stronger mismatch.
  rcases hmismatch with ⟨k, hk, t, ht0, ht1, htNe⟩
  refine ⟨k, hk, ?_⟩
  intro _ _
  exact ⟨t, ht0, ht1, htNe⟩

lemma Array.getElem!_ofFn {α : Type} [Inhabited α] {n : Nat} (f : Fin n → α)
    (i : Nat) (hi : i < n) : (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  -- reduce getElem! to getElem?
  have hi' : i < (Array.ofFn f).size := by
    simpa [Array.size_ofFn] using hi
  -- `simp` through `getD`/`getElem?` and `ofFn`
  simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getD_getElem?, Array.getElem?_ofFn,
    Array.size_ofFn, hi, hi']


theorem goal_2
    (name : Array Char)
    (typed : Array Char)
    (i : ℕ)
    (j : ℕ)
    (a : i ≤ name.size)
    (a_1 : j ≤ typed.size)
    (a_3 : i < name.size)
    (nextI : ℕ)
    (a_4 : i ≤ nextI)
    (invariant_lp_nameRun_allEq : ∀ (k : ℕ), i ≤ k → k < nextI → name[k]! = name[i]!)
    (nextJ : ℕ)
    (a_6 : j ≤ nextJ)
    (a_7 : nextJ ≤ typed.size)
    (invariant_lp_typedRun_allEq : ∀ (k : ℕ), j ≤ k → k < nextJ → typed[k]! = name[i]!)
    (if_neg_1 : j < typed.size)
    (if_neg_2 : typed[j]! = name[i]!)
    (done_2 : nextI < name.size → ¬name[nextI]! = name[i]!)
    (done_3 : nextJ < typed.size → ¬typed[nextJ]! = name[i]!)
    (if_neg_3 : nextI ≤ nextJ - j + i)
    (invariant_lp_outer_sound_prefix : ∃ (breaks : Array ℕ), breaks.size = i + OfNat.ofNat 1 ∧ breaks[OfNat.ofNat 0]! = OfNat.ofNat 0 ∧ breaks[i]! = j ∧ (∀ k < i, breaks[k]! < breaks[k + OfNat.ofNat 1]!) ∧ ∀ k < i, breaks[k]! ≤ breaks[k + OfNat.ofNat 1]! ∧ breaks[k + OfNat.ofNat 1]! ≤ typed.size ∧ ∀ (i : ℕ), breaks[k]! ≤ i → i < breaks[k + OfNat.ofNat 1]! → typed[i]! = name[k]!)
    (invariant_lp_outer_complete : ∀ (x : Array ℕ), x.size = name.size + OfNat.ofNat 1 → x[OfNat.ofNat 0]! = OfNat.ofNat 0 → x[name.size]! = typed.size → (∀ k < name.size, x[k]! < x[k + OfNat.ofNat 1]!) → (∀ k < name.size, x[k]! ≤ x[k + OfNat.ofNat 1]! ∧ x[k + OfNat.ofNat 1]! ≤ typed.size ∧ ∀ (i : ℕ), x[k]! ≤ i → i < x[k + OfNat.ofNat 1]! → typed[i]! = name[k]!) → ∃ (breaks : Array ℕ), (breaks.size = name.size + OfNat.ofNat 1 ∧ breaks[OfNat.ofNat 0]! = OfNat.ofNat 0 ∧ breaks[name.size]! = typed.size ∧ (∀ k < name.size, breaks[k]! < breaks[k + OfNat.ofNat 1]!) ∧ ∀ k < name.size, breaks[k]! ≤ breaks[k + OfNat.ofNat 1]! ∧ breaks[k + OfNat.ofNat 1]! ≤ typed.size ∧ ∀ (i : ℕ), breaks[k]! ≤ i → i < breaks[k + OfNat.ofNat 1]! → typed[i]! = name[k]!) ∧ breaks[i]! = j)
    : ∃ (breaks : Array ℕ), breaks.size = nextI + OfNat.ofNat 1 ∧ breaks[OfNat.ofNat 0]! = OfNat.ofNat 0 ∧ breaks[nextI]! = nextJ ∧ (∀ k < nextI, breaks[k]! < breaks[k + OfNat.ofNat 1]!) ∧ ∀ k < nextI, breaks[k]! ≤ breaks[k + OfNat.ofNat 1]! ∧ breaks[k + OfNat.ofNat 1]! ≤ typed.size ∧ ∀ (i : ℕ), breaks[k]! ≤ i → i < breaks[k + OfNat.ofNat 1]! → typed[i]! = name[k]! := by
  classical
  rcases invariant_lp_outer_sound_prefix with ⟨b, hbSize, hb0, hbLast, hbLt, hbSeg⟩

  have hi_lt_nextI : i < nextI := by
    have hne : nextI ≠ i := by
      intro hEq
      have hnlt : nextI < name.size := by simpa [hEq] using a_3
      have hcontra : ¬ name[nextI]! = name[i]! := done_2 hnlt
      exact hcontra (by simpa [hEq])
    exact lt_of_le_of_ne a_4 (Ne.symm hne)

  have hj_lt_nextJ : j < nextJ := by
    have hne : nextJ ≠ j := by
      intro hEq
      have hnlt : nextJ < typed.size := by simpa [hEq] using if_neg_1
      have hcontra : ¬ typed[nextJ]! = name[i]! := done_3 hnlt
      exact hcontra (by simpa [hEq] using if_neg_2)
    exact lt_of_le_of_ne a_6 (Ne.symm hne)

  have hrun : nextI - i ≤ nextJ - j :=
    (Nat.sub_le_iff_le_add (a := nextI) (b := i) (c := nextJ - j)).2 if_neg_3

  let f : Fin (nextI + 1) → Nat := fun idx =>
    let k : Nat := idx
    if hk : k = nextI then
      nextJ
    else if hk' : k < i then
      b[k]!
    else
      j + (k - i)

  let breaks : Array Nat := Array.ofFn f

  have breaks_val (k : Nat) (hk : k < nextI + 1) :
      breaks[k]! = (if hkN : k = nextI then nextJ else if hklt : k < i then b[k]! else j + (k - i)) := by
    simpa [breaks, f] using (Array.getElem!_ofFn f k hk)

  have hsize : breaks.size = nextI + 1 := by
    simp [breaks, Array.size_ofFn]

  have h0 : breaks[0]! = 0 := by
    have h0lt : 0 < nextI + 1 := Nat.succ_pos _
    have hposNextI : 0 < nextI := Nat.lt_of_le_of_lt (Nat.zero_le i) hi_lt_nextI
    have hne0 : (0 : Nat) ≠ nextI := Nat.ne_of_lt hposNextI
    by_cases hi0 : 0 < i
    · have : breaks[0]! = b[0]! := by
        simp [breaks_val 0 h0lt, hne0, hi0]
      simpa [this, hb0]
    · have hiEq : i = 0 := by omega
      have hj0 : j = 0 := by
        calc
          j = b[0]! := by simpa [hiEq] using hbLast.symm
          _ = 0 := by simpa using hb0
      subst hiEq
      subst hj0
      simp [breaks_val 0 h0lt, hne0]

  have hLast : breaks[nextI]! = nextJ := by
    have hN : nextI < nextI + 1 := Nat.lt_succ_self _
    simp [breaks_val nextI hN]

  have hStrict : ∀ k < nextI, breaks[k]! < breaks[k+1]! := by
    intro k hk
    have hk0 : k < nextI + 1 := Nat.lt_trans hk (Nat.lt_succ_self _)
    have hk1 : k + 1 < nextI + 1 := Nat.succ_lt_succ hk
    have hk_ne : k ≠ nextI := Nat.ne_of_lt hk
    have hk1_le_nextI : k + 1 ≤ nextI := Nat.succ_le_of_lt hk
    by_cases hkLast : k + 1 = nextI
    · have hk_ge_i : i ≤ k := by omega
      have hk_not_lt_i : ¬ k < i := Nat.not_lt.mpr hk_ge_i
      have hkLeft : breaks[k]! = j + (k - i) := by
        simp [breaks_val k hk0, hk_ne, hk_not_lt_i]
      have hkRight : breaks[k+1]! = nextJ := by
        have : breaks[nextI]! = nextJ := hLast
        simpa [hkLast] using this
      have hkj : j + (k - i) < nextJ := by omega
      simpa [hkLeft, hkRight] using hkj
    · have hk1_lt_nextI : k + 1 < nextI := lt_of_le_of_ne hk1_le_nextI hkLast
      have hk1_ne : k + 1 ≠ nextI := Nat.ne_of_lt hk1_lt_nextI
      by_cases hklt : k + 1 < i
      · have hklt0 : k < i := by omega
        have hkLeft : breaks[k]! = b[k]! := by
          simp [breaks_val k hk0, hk_ne, hklt0]
        have hkRight : breaks[k+1]! = b[k+1]! := by
          simp [breaks_val (k+1) hk1, hk1_ne, hklt]
        simpa [hkLeft, hkRight] using hbLt k hklt0
      · by_cases hklt0 : k < i
        · have hk1eq : k + 1 = i := by omega
          have hkLeft : breaks[k]! = b[k]! := by
            simp [breaks_val k hk0, hk_ne, hklt0]
          have hkRight : breaks[k+1]! = j := by
            have hki_ne : i ≠ nextI := Nat.ne_of_lt hi_lt_nextI
            have hi0' : i < nextI + 1 := Nat.lt_trans hi_lt_nextI (Nat.lt_succ_self _)
            have : breaks[i]! = j + (i - i) := by
              simp [breaks_val i hi0', hki_ne, Nat.lt_irrefl i]
            simpa [hk1eq, this]
          have hbkj : b[k]! < j := by
            have : b[k]! < b[k+1]! := hbLt k hklt0
            simpa [hk1eq, hbLast] using this
          simpa [hkLeft, hkRight] using hbkj
        · have hk_ge_i : i ≤ k := Nat.le_of_not_gt hklt0
          have hk_not_lt_i : ¬ k < i := Nat.not_lt.mpr hk_ge_i
          have hk1_not_lt_i : ¬ (k + 1 < i) := by omega
          have hkLeft : breaks[k]! = j + (k - i) := by
            simp [breaks_val k hk0, hk_ne, hk_not_lt_i]
          have hkRight : breaks[k+1]! = j + ((k+1) - i) := by
            simp [breaks_val (k+1) hk1, hk1_ne, hk1_not_lt_i]
          have : j + (k - i) < j + ((k + 1) - i) := by omega
          simpa [hkLeft, hkRight] using this

  refine ⟨breaks, hsize, h0, hLast, hStrict, ?_⟩
  intro k hk
  have hk0 : k < nextI + 1 := Nat.lt_trans hk (Nat.lt_succ_self _)
  have hk1 : k + 1 < nextI + 1 := Nat.succ_lt_succ hk
  have hk_ne : k ≠ nextI := Nat.ne_of_lt hk
  have hlt : breaks[k]! < breaks[k+1]! := hStrict k hk
  refine ⟨le_of_lt hlt, ?_, ?_⟩
  · by_cases hkLast : k + 1 = nextI
    · have : breaks[nextI]! = nextJ := hLast
      have : breaks[k+1]! = nextJ := by simpa [hkLast] using this
      exact le_trans (by simpa [this] using le_rfl) a_7
    · have hk1_le_nextI : k + 1 ≤ nextI := Nat.succ_le_of_lt hk
      have hk1_lt_nextI : k + 1 < nextI := lt_of_le_of_ne hk1_le_nextI hkLast
      have hk1_ne : k + 1 ≠ nextI := Nat.ne_of_lt hk1_lt_nextI
      by_cases hklt : k + 1 < i
      · have hklt0 : k < i := by omega
        have hbBound : b[k+1]! ≤ typed.size := (hbSeg k hklt0).2.1
        have hbEq : breaks[k+1]! = b[k+1]! := by
          simp [breaks_val (k+1) hk1, hk1_ne, hklt]
        simpa [hbEq] using hbBound
      · have hk1_not_lt_i : ¬ (k + 1 < i) := hklt
        have hbEq : breaks[k+1]! = j + ((k+1) - i) := by
          simp [breaks_val (k+1) hk1, hk1_ne, hk1_not_lt_i]
        have hleNextJ : j + ((k+1) - i) ≤ nextJ := by omega
        exact le_trans (by simpa [hbEq] using hleNextJ) a_7
  · intro t ht1 ht2
    by_cases hklt : k < i
    · have hk1_le_i : k + 1 ≤ i := Nat.succ_le_of_lt hklt
      have hk1_case : k + 1 < i ∨ k + 1 = i := lt_or_eq_of_le hk1_le_i
      have hk_ne' : k ≠ nextI := Nat.ne_of_lt (Nat.lt_trans hklt hi_lt_nextI)
      have hstart : breaks[k]! = b[k]! := by
        simp [breaks_val k hk0, hk_ne', hklt]
      have hend : breaks[k+1]! = b[k+1]! := by
        cases hk1_case with
        | inl hk1lt =>
            have hk1_ne : k + 1 ≠ nextI := Nat.ne_of_lt (Nat.lt_trans hk1lt hi_lt_nextI)
            simp [breaks_val (k+1) hk1, hk1_ne, hk1lt]
        | inr hk1eq =>
            have hki_ne : i ≠ nextI := Nat.ne_of_lt hi_lt_nextI
            have hi0' : i < nextI + 1 := Nat.lt_trans hi_lt_nextI (Nat.lt_succ_self _)
            have hbreaksi : breaks[i]! = j := by
              simp [breaks_val i hi0', hki_ne, Nat.lt_irrefl i]
            have : breaks[k+1]! = j := by simpa [hk1eq] using hbreaksi
            have : breaks[k+1]! = b[i]! := by simpa [hbLast] using this
            simpa [hk1eq] using this
      have hEq : ∀ t, b[k]! ≤ t → t < b[k+1]! → typed[t]! = name[k]! := (hbSeg k hklt).2.2
      apply hEq t
      · simpa [hstart] using ht1
      · simpa [hend] using ht2
    · have hk_ge_i : i ≤ k := Nat.le_of_not_gt hklt
      have hk_ne' : k ≠ nextI := Nat.ne_of_lt hk
      have hstart : breaks[k]! = j + (k - i) := by
        simp [breaks_val k hk0, hk_ne', hklt]
      have hjt : j ≤ t := by
        have : j ≤ j + (k - i) := Nat.le_add_right _ _
        exact le_trans (by simpa [hstart] using this) ht1
      by_cases hkLast : k + 1 = nextI
      · have hend : breaks[k+1]! = nextJ := by
          have : breaks[nextI]! = nextJ := hLast
          simpa [hkLast] using this
        have htN : t < nextJ := by simpa [hend] using ht2
        have htEq : typed[t]! = name[i]! := invariant_lp_typedRun_allEq t hjt htN
        have hnEq : name[k]! = name[i]! := invariant_lp_nameRun_allEq k hk_ge_i hk
        simpa [hnEq] using htEq
      · have hk1_le_nextI : k + 1 ≤ nextI := Nat.succ_le_of_lt hk
        have hk1_lt_nextI : k + 1 < nextI := lt_of_le_of_ne hk1_le_nextI hkLast
        have hk1_ne : k + 1 ≠ nextI := Nat.ne_of_lt hk1_lt_nextI
        have hend : breaks[k+1]! = j + ((k+1) - i) := by
          have hk1_not_lt_i : ¬ (k + 1 < i) := by omega
          simp [breaks_val (k+1) hk1, hk1_ne, hk1_not_lt_i]
        have hend_le : breaks[k+1]! ≤ nextJ := by omega
        have htN : t < nextJ := lt_of_lt_of_le ht2 hend_le
        have htEq : typed[t]! = name[i]! := invariant_lp_typedRun_allEq t hjt htN
        have hnEq : name[k]! = name[i]! := invariant_lp_nameRun_allEq k hk_ge_i hk
        simpa [hnEq] using htEq

theorem goal_3
    (name : Array Char)
    (typed : Array Char)
    (i : ℕ)
    (j : ℕ)
    (nextI : ℕ)
    (a_4 : i ≤ nextI)
    (a_5 : nextI ≤ name.size)
    (invariant_lp_nameRun_allEq : ∀ (k : ℕ), i ≤ k → k < nextI → name[k]! = name[i]!)
    (nextJ : ℕ)
    (a_6 : j ≤ nextJ)
    (a_7 : nextJ ≤ typed.size)
    (invariant_lp_typedRun_allEq : ∀ (k : ℕ), j ≤ k → k < nextJ → typed[k]! = name[i]!)
    (done_2 : nextI < name.size → ¬name[nextI]! = name[i]!)
    (done_3 : nextJ < typed.size → ¬typed[nextJ]! = name[i]!)
    (invariant_lp_outer_complete : ∀ (x : Array ℕ), x.size = name.size + OfNat.ofNat 1 → x[OfNat.ofNat 0]! = OfNat.ofNat 0 → x[name.size]! = typed.size → (∀ k < name.size, x[k]! < x[k + OfNat.ofNat 1]!) → (∀ k < name.size, x[k]! ≤ x[k + OfNat.ofNat 1]! ∧ x[k + OfNat.ofNat 1]! ≤ typed.size ∧ ∀ (i : ℕ), x[k]! ≤ i → i < x[k + OfNat.ofNat 1]! → typed[i]! = name[k]!) → ∃ (breaks : Array ℕ), (breaks.size = name.size + OfNat.ofNat 1 ∧ breaks[OfNat.ofNat 0]! = OfNat.ofNat 0 ∧ breaks[name.size]! = typed.size ∧ (∀ k < name.size, breaks[k]! < breaks[k + OfNat.ofNat 1]!) ∧ ∀ k < name.size, breaks[k]! ≤ breaks[k + OfNat.ofNat 1]! ∧ breaks[k + OfNat.ofNat 1]! ≤ typed.size ∧ ∀ (i : ℕ), breaks[k]! ≤ i → i < breaks[k + OfNat.ofNat 1]! → typed[i]! = name[k]!) ∧ breaks[i]! = j)
    : ∀ (x : Array ℕ), x.size = name.size + OfNat.ofNat 1 → x[OfNat.ofNat 0]! = OfNat.ofNat 0 → x[name.size]! = typed.size → (∀ k < name.size, x[k]! < x[k + OfNat.ofNat 1]!) → (∀ k < name.size, x[k]! ≤ x[k + OfNat.ofNat 1]! ∧ x[k + OfNat.ofNat 1]! ≤ typed.size ∧ ∀ (i : ℕ), x[k]! ≤ i → i < x[k + OfNat.ofNat 1]! → typed[i]! = name[k]!) → ∃ (breaks : Array ℕ), (breaks.size = name.size + OfNat.ofNat 1 ∧ breaks[OfNat.ofNat 0]! = OfNat.ofNat 0 ∧ breaks[name.size]! = typed.size ∧ (∀ k < name.size, breaks[k]! < breaks[k + OfNat.ofNat 1]!) ∧ ∀ k < name.size, breaks[k]! ≤ breaks[k + OfNat.ofNat 1]! ∧ breaks[k + OfNat.ofNat 1]! ≤ typed.size ∧ ∀ (i : ℕ), breaks[k]! ≤ i → i < breaks[k + OfNat.ofNat 1]! → typed[i]! = name[k]!) ∧ breaks[nextI]! = nextJ := by
  intro x hxSize hx0 hxLast hxLt hxSeg
  rcases invariant_lp_outer_complete x hxSize hx0 hxLast hxLt hxSeg with ⟨breaks, hbreaks⟩
  rcases hbreaks with ⟨hprops, hbi⟩
  rcases hprops with ⟨hsizeB, h0B, hlastB, hltB, hsegB⟩

  have h_i_le_nextJ : breaks[i]! ≤ nextJ := by
    simpa [hbi] using a_6

  -- For all n ≥ i, if n ≤ nextI then breaks[n]! ≤ nextJ.
  have hleP : ∀ n (hin : i ≤ n), n ≤ nextI → breaks[n]! ≤ nextJ := by
    -- P n hin := n ≤ nextI → breaks[n]! ≤ nextJ
    have hmain : ∀ n (hin : i ≤ n), (n ≤ nextI → breaks[n]! ≤ nextJ) :=
      Nat.le_induction (m := i) (P := fun n hin => n ≤ nextI → breaks[n]! ≤ nextJ)
        (base := by
          intro _
          exact h_i_le_nextJ)
        (succ := by
          intro n hin ih
          intro hn1_le_nextI
          have hn_le_nextI : n ≤ nextI :=
            Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self n)) hn1_le_nextI
          have hbn_le : breaks[n]! ≤ nextJ := ih hn_le_nextI

          have hn_lt_name : n < name.size := by
            have hn1_le_name : n + 1 ≤ name.size := Nat.le_trans hn1_le_nextI a_5
            exact Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn1_le_name

          rcases hsegB n hn_lt_name with ⟨_, hbnp1_le_size, hsegEq⟩

          by_cases hJ : nextJ < typed.size
          · have hnot : ¬ nextJ < breaks[n + 1]! := by
              intro hltJ
              have htyped : typed[nextJ]! = name[n]! := hsegEq nextJ hbn_le hltJ
              have hn_lt_nextI : n < nextI :=
                Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn1_le_nextI
              have hname : name[n]! = name[i]! := invariant_lp_nameRun_allEq n hin hn_lt_nextI
              have htyped' : typed[nextJ]! = name[i]! := by
                simpa [hname] using htyped
              exact (done_3 hJ) htyped'
            exact Nat.le_of_not_gt hnot
          · have hsize_le_nextJ : typed.size ≤ nextJ := Nat.le_of_not_gt hJ
            have hEq : typed.size = nextJ := Nat.le_antisymm hsize_le_nextJ a_7
            simpa [hEq] using hbnp1_le_size)
    intro n hin hnle
    exact (hmain n hin) hnle

  have hle_nextI : breaks[nextI]! ≤ nextJ := hleP nextI a_4 (le_rfl)

  -- Monotonicity from strict increase: breaks[i]! ≤ breaks[n]! for n between i and nextI.
  have hmono : ∀ n (hin : i ≤ n), n ≤ nextI → breaks[i]! ≤ breaks[n]! := by
    have hmain : ∀ n (hin : i ≤ n), (n ≤ nextI → breaks[i]! ≤ breaks[n]!) :=
      Nat.le_induction (m := i) (P := fun n hin => n ≤ nextI → breaks[i]! ≤ breaks[n]!)
        (base := by
          intro _
          exact le_rfl)
        (succ := by
          intro n hin ih
          intro hn1_le_nextI
          have hn_le_nextI : n ≤ nextI :=
            Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self n)) hn1_le_nextI
          have hi_le_bn : breaks[i]! ≤ breaks[n]! := ih hn_le_nextI
          have hn_lt_name : n < name.size := by
            have hn1_le_name : n + 1 ≤ name.size := Nat.le_trans hn1_le_nextI a_5
            exact Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn1_le_name
          have hb_le : breaks[n]! ≤ breaks[n + 1]! := Nat.le_of_lt (hltB n hn_lt_name)
          exact le_trans hi_le_bn hb_le)
    intro n hin hnle
    exact (hmain n hin) hnle

  have hj_le_breaks_nextI : j ≤ breaks[nextI]! := by
    have : breaks[i]! ≤ breaks[nextI]! := hmono nextI a_4 (le_rfl)
    simpa [hbi] using this

  have hnextJ_le : nextJ ≤ breaks[nextI]! := by
    by_cases hNI : nextI < name.size
    · by_contra hcontra
      have hlt : breaks[nextI]! < nextJ := Nat.lt_of_not_ge hcontra
      have hjle : j ≤ breaks[nextI]! := hj_le_breaks_nextI
      have htypedRun : typed[breaks[nextI]!]! = name[i]! :=
        invariant_lp_typedRun_allEq (breaks[nextI]!) hjle hlt
      rcases hsegB nextI hNI with ⟨_, _, hsegEq⟩
      have htypedSeg : typed[breaks[nextI]!]! = name[nextI]! := by
        have hltSeg : breaks[nextI]! < breaks[nextI + 1]! := hltB nextI hNI
        exact hsegEq (breaks[nextI]!) (le_rfl) hltSeg
      have hnameEq : name[nextI]! = name[i]! := by
        calc
          name[nextI]! = typed[breaks[nextI]!]! := by simpa using htypedSeg.symm
          _ = name[i]! := htypedRun
      exact (done_2 hNI) hnameEq
    · have hEqNI : nextI = name.size :=
        Nat.le_antisymm a_5 (Nat.le_of_not_gt hNI)
      simpa [hEqNI, hlastB] using a_7

  have hEqBreak : breaks[nextI]! = nextJ := Nat.le_antisymm hle_nextI hnextJ_le

  refine ⟨breaks, ?_, hEqBreak⟩
  exact ⟨hsizeB, h0B, hlastB, hltB, hsegB⟩

theorem goal_4 : ∃ (breaks : Array ℕ), breaks.size = OfNat.ofNat 1 ∧ breaks[OfNat.ofNat 0]! = OfNat.ofNat 0 := by
  refine ⟨#[0], ?_⟩
  simp

theorem goal_5
    (name : Array Char)
    (typed : Array Char)
    (invariant_lp_outer_sound_prefix : ∃ (breaks : Array ℕ), breaks.size = name.size + OfNat.ofNat 1 ∧ breaks[OfNat.ofNat 0]! = OfNat.ofNat 0 ∧ breaks[name.size]! = typed.size ∧ (∀ k < name.size, breaks[k]! < breaks[k + OfNat.ofNat 1]!) ∧ ∀ k < name.size, breaks[k]! ≤ breaks[k + OfNat.ofNat 1]! ∧ breaks[k + OfNat.ofNat 1]! ≤ typed.size ∧ ∀ (i : ℕ), breaks[k]! ≤ i → i < breaks[k + OfNat.ofNat 1]! → typed[i]! = name[k]!)
    : postcondition name typed true := by
    intros; expose_names; try simp_all; try grind


prove_correct LongPressedName by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at *); try (conv => congr <;> simp) ; try expose_names)
  exact (goal_0 name typed if_pos if_pos_1)
  exact (goal_1 name typed i j a nextI a_4 a_5 invariant_lp_nameRun_allEq nextJ a_6 if_pos done_3 invariant_lp_outer_complete)
  exact (goal_2 name typed i j a a_1 a_3 nextI a_4 invariant_lp_nameRun_allEq nextJ a_6 a_7 invariant_lp_typedRun_allEq if_neg_1 if_neg_2 done_2 done_3 if_neg_3 invariant_lp_outer_sound_prefix invariant_lp_outer_complete)
  exact (goal_3 name typed i j nextI a_4 a_5 invariant_lp_nameRun_allEq nextJ a_6 a_7 invariant_lp_typedRun_allEq done_2 done_3 invariant_lp_outer_complete)
  exact (goal_4)
  exact (goal_5 name typed invariant_lp_outer_sound_prefix)
end Proof
