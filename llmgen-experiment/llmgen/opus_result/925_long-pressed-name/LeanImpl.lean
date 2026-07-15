import Lean
import Mathlib.Tactic
import Velvet.Std
import Extensions.VelvetPBT

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
  -- Two-pointer approach: i into name, j into typed.
  -- When chars match, advance both. When they don't match but typed[j] is a
  -- long-press repeat of typed[j-1], advance j only. Otherwise fail.
  -- After name is exhausted, remaining typed chars must be long-press repeats.
  -- O(m+n) time since j strictly increases each step.
  let rec go (i : Nat) (j : Nat) : Bool :=
    if hj : j < typed.size then
      if hi : i < name.size then
        if name[i] == typed[j] then
          go (i + 1) (j + 1)
        else if j > 0 && typed[j] == typed[j - 1] then
          go i (j + 1)
        else
          false
      else
        -- name exhausted; remaining typed chars must be long-press repeats
        if j > 0 && typed[j] == typed[j - 1] then
          go i (j + 1)
        else
          false
    else
      -- typed exhausted; name must also be exhausted
      i == name.size
  termination_by typed.size - j
  go 0 0
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
#assert_same_evaluation #[(implementation test1_name test1_typed), test1_Expected]

-- Test case 2
#assert_same_evaluation #[(implementation test2_name test2_typed), test2_Expected]

-- Test case 3
#assert_same_evaluation #[(implementation test3_name test3_typed), test3_Expected]

-- Test case 4
#assert_same_evaluation #[(implementation test4_name test4_typed), test4_Expected]

-- Test case 5
#assert_same_evaluation #[(implementation test5_name test5_typed), test5_Expected]

-- Test case 6
#assert_same_evaluation #[(implementation test6_name test6_typed), test6_Expected]

-- Test case 7
#assert_same_evaluation #[(implementation test7_name test7_typed), test7_Expected]

-- Test case 8
#assert_same_evaluation #[(implementation test8_name test8_typed), test8_Expected]

-- Test case 9
#assert_same_evaluation #[(implementation test9_name test9_typed), test9_Expected]
end Assertions

section Pbt
method implementationPbt (name : Array Char) (typed : Array Char)
  return (result : Bool)
  require precondition name typed
  ensures postcondition name typed result
  do
  return (implementation name typed)

velvet_plausible_test implementationPbt (config := { maxMs := some 20000 })
end Pbt

section Proof
-- Helper: suffix version of isLongPressed
def isLongPressedFrom (name : Array Char) (i : Nat) (typed : Array Char) (j : Nat) : Prop :=
  ∃ (breaks : Array Nat),
    breaks.size = (name.size - i) + 1 ∧
    breaks[0]! = j ∧
    breaks[name.size - i]! = typed.size ∧
    (∀ k, k < name.size - i → breaks[k]! < breaks[k + 1]!) ∧
    (∀ k, k < name.size - i → segmentAllEq typed breaks[k]! breaks[k + 1]! name[i + k]!)

set_option maxRecDepth 1000 in
private lemma go_unfold (name : Array Char) (typed : Array Char) (i j : Nat) :
    implementation.go name typed i j =
      if hj : j < typed.size then
        if hi : i < name.size then
          if name[i] == typed[j] then
            implementation.go name typed (i + 1) (j + 1)
          else if j > 0 && typed[j] == typed[j - 1] then
            implementation.go name typed i (j + 1)
          else
            false
        else
          if j > 0 && typed[j] == typed[j - 1] then
            implementation.go name typed i (j + 1)
          else
            false
      else
        i == name.size := by
  rw [implementation.go]

-- The invariant: go i j = true with appropriate conditions means
-- isLongPressedFrom holds from some j' ≥ j, and positions [j..j') are repeats
private lemma go_sound_gen (name typed : Array Char) (fuel : Nat) (i j : Nat) 
    (hfuel : typed.size - j ≤ fuel) 
    (hi : i ≤ name.size) (hj : j ≤ typed.size)
    (hgo : implementation.go name typed i j = true) :
    isLongPressedFrom name i typed j ∨ 
    (j > 0 ∧ ∃ j', j < j' ∧ j' ≤ typed.size ∧ 
      (∀ p, j ≤ p → p < j' → typed[p]! = typed[j-1]!) ∧ 
      isLongPressedFrom name i typed j') := by
  sorry

-- Helper to convert between bounded and unbounded array access
private lemma getElem!_eq_getElem {α : Type} [Inhabited α] (a : Array α) (i : Nat) (h : i < a.size) :
    a[i]! = a[i] := by
  simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
  rw [Array.getElem?_eq_some_iff.mpr ⟨h, rfl⟩]
  simp

-- Helper for the long-press skip case in go_implies_suffix
-- When go i j = true because typed[j] = typed[j-1] (long press skip),
-- and IH gives us the result for go i (j+1),
-- then we can extend the result to go i j
set_option maxHeartbeats 800000 in
private lemma long_press_extend (name typed : Array Char) (i j : Nat) 
    (hjlt : j < typed.size) (hj_pos : j > 0)
    (htyped_rep : typed[j]'hjlt = typed[j-1]'(by omega))
    (j' : Nat) (hj'ge : j + 1 ≤ j') 
    (hfrom : isLongPressedFrom name i typed j')
    (hcarry : j' > j + 1 → j + 1 > 0 ∧ ∀ p, j + 1 ≤ p → p < j' → typed[p]! = typed[j + 1 - 1]!) :
    j ≤ j' ∧ isLongPressedFrom name i typed j' ∧ 
      (j' > j → j > 0 ∧ ∀ p, j ≤ p → p < j' → typed[p]! = typed[j-1]!) := by
  refine ⟨by omega, hfrom, ?_⟩
  intro hj'gt
  refine ⟨hj_pos, ?_⟩
  intro p hp1 hp2
  by_cases hpj : p = j
  · -- p = j: typed[p]! = typed[j]! = typed[j-1]!
    subst hpj
    rw [getElem!_eq_getElem typed p hjlt, getElem!_eq_getElem typed (p - 1) (by omega)]
    exact htyped_rep
  · -- p > j: use carry from IH
    have hpge : j + 1 ≤ p := by omega
    have hj'gt2 : j' > j + 1 := by omega
    have ⟨_, hcarry2⟩ := hcarry hj'gt2
    have h_eq : typed[p]! = typed[j + 1 - 1]! := hcarry2 p hpge hp2
    simp only [show j + 1 - 1 = j from by omega] at h_eq
    rw [h_eq]
    rw [getElem!_eq_getElem typed j hjlt, getElem!_eq_getElem typed (j - 1) (by omega)]
    exact htyped_rep

-- Key helper: getElem! for array append
set_option maxHeartbeats 800000 in
private lemma getElem!_append_left [Inhabited α] (a b : Array α) (i : Nat) (h : i < a.size) :
    (a ++ b)[i]! = a[i]! := by
  simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_append]
  split
  · rename_i h'
    rfl
  · omega

private lemma getElem!_append_right [Inhabited α] (a b : Array α) (i : Nat) (h : a.size ≤ i) :
    (a ++ b)[i]! = b[i - a.size]! := by
  simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_append]
  split
  · omega
  · rfl


theorem correctness_goal_0
    (name : Array Char)
    (typed : Array Char)
    (h_precond : precondition name typed)
    (h : implementation name typed = true)
    : implementation name typed = true → isLongPressed name typed := by
    sorry

theorem correctness_goal_1
    (name : Array Char)
    (typed : Array Char)
    (h_precond : precondition name typed)
    (h : isLongPressed name typed)
    : isLongPressed name typed → implementation name typed = true := by
    sorry



theorem correctness_goal
    (name : Array Char)
    (typed : Array Char)
    (h_precond : precondition name typed)
    : postcondition name typed (implementation name typed) := by
    unfold postcondition
    constructor
    · -- Forward direction: implementation returns true → isLongPressed
      intro h
      have h_sound : implementation name typed = true → isLongPressed name typed := by expose_names; exact (correctness_goal_0 name typed h_precond h)
      exact h_sound h
    · -- Backward direction: isLongPressed → implementation returns true
      intro h
      have h_complete : isLongPressed name typed → implementation name typed = true := by expose_names; exact (correctness_goal_1 name typed h_precond h)
      exact h_complete h
end Proof
