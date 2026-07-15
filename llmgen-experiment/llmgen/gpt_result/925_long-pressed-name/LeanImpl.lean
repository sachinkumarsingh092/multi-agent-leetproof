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
theorem correctness_goal_0
    (name : Array Char)
    (typed : Array Char)
    (h0 : name.size = 0)
    : implementation name typed = true ↔ isLongPressed name typed := by
  -- simplify implementation in the `name.size = 0` case
  have hImpl : (implementation name typed = true) ↔ typed.size = 0 := by
    -- unfold and simplify the `if` using `h0`
    simp [implementation, h0]
  have hLP : isLongPressed name typed ↔ typed.size = 0 := by
    constructor
    · rintro ⟨breaks, hvalid⟩
      rcases hvalid with ⟨hsize, hstart, hend, hinc, hseg⟩
      -- in the empty-name case, the end index is breaks[0]!
      have hend' : breaks[0]! = typed.size := by
        simpa [h0] using hend
      -- combine with breaks[0]! = 0
      simpa [hstart] using (congrArg id (Eq.trans (Eq.symm hend') hstart))
    · intro hts
      refine ⟨#[0], ?_⟩
      -- all constraints are trivial/vacuous
      simp [validBreaks, segmentAllEq, isLongPressed, h0, hts]
  -- chain the two characterizations
  constructor
  · intro himpl
    have hts : typed.size = 0 := (hImpl.mp himpl)
    exact (hLP.mpr hts)
  · intro hlp
    have hts : typed.size = 0 := (hLP.mp hlp)
    exact (hImpl.mpr hts)

section Helper

-- Helpers for `Array.get!` with `push`.

theorem Array.get!_push_size {α} [Inhabited α] (xs : Array α) (x : α) :
    (xs.push x)[xs.size]! = x := by
  -- Reduce `get!` to `getD` and use the `getElem?` characterization.
  simp [Array.get!_eq_getD, Array.getD, Array.get?, Array.getElem?_push_size]

end Helper

section Helper

theorem Array.get!_push_lt {α} [Inhabited α] (xs : Array α) (x : α) {i : Nat}
    (hi : i < xs.size) : (xs.push x)[i]! = xs[i]! := by
  -- Convert both sides to `get!Internal`.
  rw [← Array.get!Internal_eq_getElem! (a := xs.push x) (i := i)]
  rw [← Array.get!Internal_eq_getElem! (a := xs) (i := i)]
  -- Now unfold `get!Internal`.
  simp [Array.get!Internal, Array.get? , Array.getElem?_push_lt, hi]

end Helper

section Helper

theorem Array.getElem!_eq_getElem {α} [Inhabited α] (xs : Array α) (i : Fin xs.size) :
    xs[i.1]! = xs[i] := by
  -- `xs[i]` is in-bounds; `xs[i.1]!` should coincide.
  -- Convert `xs[i.1]!` to `get!Internal` and unfold.
  rw [← Array.get!Internal_eq_getElem! (a := xs) (i := i.1)]
  -- `get!Internal` agrees with `get` on in-bounds indices.
  simp [Array.get!Internal, Array.get?, i.isLt]

end Helper


theorem correctness_goal_1_0
    (name : Array Char)
    (typed : Array Char)
    (h_precond : precondition name typed)
    (h0 : ¬name.size = 0)
    : implementation name typed = true → isLongPressed name typed := by
    sorry

section Scratch

-- Split a prefix extract at `a` (assuming `b ≤ xs.size` so no clamping at the end).
theorem array_extract_split0 {α} (xs : Array α) (a b : Nat)
    (hab : a ≤ b) (hb : b ≤ xs.size) :
    xs.extract 0 b = xs.extract 0 a ++ xs.extract a b := by
  apply Array.ext
  · -- size equality
    have ha : a ≤ xs.size := le_trans hab hb
    -- compute sizes
    simp [Array.size_extract, hb, ha, hab, Nat.min_eq_left, Nat.sub_zero, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc, Nat.add_sub_cancel_left, Nat.add_sub_cancel] 
  · intro i
    -- `getElem?` extensionality
    by_cases hi : i < a
    · simp [Array.getElem?_extract, Array.getElem?_append, hi, hab, hb, Nat.min_eq_left]
    · have hia : a ≤ i := Nat.le_of_not_gt hi
      by_cases hib : i < b
      · simp [Array.getElem?_extract, Array.getElem?_append, hi, hia, hib, hab, hb, Nat.min_eq_left]
      · have hib' : b ≤ i := Nat.le_of_not_gt hib
        simp [Array.getElem?_extract, Array.getElem?_append, hi, hia, hib, hab, hb, Nat.min_eq_left, hib']

end Scratch


theorem correctness_goal_1_1
    (name : Array Char)
    (typed : Array Char)
    (h_precond : precondition name typed)
    (h0 : ¬name.size = 0)
    (h_sound : implementation name typed = true → isLongPressed name typed)
    : isLongPressed name typed → implementation name typed = true := by
    sorry

theorem correctness_goal_1
    (name : Array Char)
    (typed : Array Char)
    (h_precond : precondition name typed)
    (h0 : ¬name.size = 0)
    : implementation name typed = true ↔ isLongPressed name typed := by
  classical
  -- precondition is `True`
  have h_sound : implementation name typed = true → isLongPressed name typed := by
    expose_names; exact (correctness_goal_1_0 name typed h_precond h0)
  have h_complete : isLongPressed name typed → implementation name typed = true := by
    expose_names; exact (correctness_goal_1_1 name typed h_precond h0 h_sound)
  constructor
  · intro h
    exact h_sound h
  · intro h
    exact h_complete h

theorem correctness_goal
    (name : Array Char)
    (typed : Array Char)
    (h_precond : precondition name typed)
    : postcondition name typed (implementation name typed) := by
  -- precondition is True
  simp [postcondition, precondition]
  -- split on name.size = 0 as in the implementation
  by_cases h0 : name.size = 0
  · -- empty name case
    have h_empty : (implementation name typed = true ↔ isLongPressed name typed) := by
      expose_names; exact (correctness_goal_0 name typed h0)
    simpa [implementation, h0] using h_empty
  · -- nonempty name case
    have h_nonempty : (implementation name typed = true ↔ isLongPressed name typed) := by
      expose_names; exact (correctness_goal_1 name typed h_precond h0)
    simpa [implementation, h0] using h_nonempty
end Proof
