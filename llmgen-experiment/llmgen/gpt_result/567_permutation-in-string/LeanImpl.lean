import Lean
import Mathlib.Tactic
import Velvet.Std
import Extensions.VelvetPBT

set_option maxHeartbeats 10000000

section Specs
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false

/- Problem Description
    567. Permutation in String: determine whether s2 contains a contiguous substring that is a permutation of s1.
    Natural language breakdown:
    1. Inputs are two sequences of characters (modeled as List Char).
    2. A list w is a permutation of s1 exactly when both lists contain exactly the same characters with the same multiplicities.
    3. s2 contains a permutation of s1 when there exists a start index i such that the contiguous window of s2 of length |s1| starting at i is a permutation of s1.
    4. When |s1| = 0, the empty window exists in any s2, so the answer is true.
    5. When |s1| > |s2|, no window of the required length exists, so the answer is false.
    6. The returned Bool is true exactly when such a window exists.
    Your algorithm should run in **O(|s1| + |s2|)** time and **O(1)** extra space.
-/

-- A window of s (contiguous substring) starting at i of length n.
-- We use List.drop/List.take as a standard abstract model of substrings.
def window (s : List Char) (i : Nat) (n : Nat) : List Char :=
  (s.drop i).take n

-- "w is a permutation of s1" stated using only relevant characters.
-- We avoid quantifying over all Char by restricting to characters that appear in s1.
-- The two conditions are:
-- 1) For each character c occurring in s1, multiplicities match between s1 and w.
-- 2) w contains no characters outside s1.
-- Together, these imply w and s1 have the same multiset of characters.
def isPermutationOf (s1 : List Char) (w : List Char) : Prop :=
  (∀ c : Char, c ∈ s1 → s1.count c = w.count c) ∧
  (∀ c : Char, c ∈ w → c ∈ s1)

-- Preconditions: none.
def precondition (s1 : List Char) (s2 : List Char) : Prop :=
  True

-- Postcondition: result is true iff there exists an index i such that the length-|s1| window
-- of s2 starting at i is a permutation of s1.
-- Note: the guard i + |s1| ≤ |s2| ensures the window has exactly the required length.
def postcondition (s1 : List Char) (s2 : List Char) (result : Bool) : Prop :=
  result = true ↔
    (∃ i : Nat,
      i + s1.length ≤ s2.length ∧
      isPermutationOf s1 (window s2 i s1.length))
end Specs

section Impl
def implementation (s1 : List Char) (s2 : List Char) : Bool :=
  -- Sliding-window permutation check using frequency difference table.
  -- For full `Char` correctness, we index by the full `Char.toNat` range.
  -- `Char` is a Unicode scalar value, so `toNat < 0x110000`.
  let n := s1.length
  let m := s2.length
  if n = 0 then
    true
  else if n > m then
    false
  else
    let size : Nat := 0x110000
    let idx (c : Char) : Nat := c.toNat

    let base : Array Int := Array.replicate size 0

    let needAfterS1 : Array Int :=
      s1.foldl (fun a c =>
        let i := idx c
        a.set! i (a[i]! + 1)) base

    -- Subtract first window of length n from need.
    let rec initNeed (need : Array Int) (k : Nat) (xs : List Char) : Array Int :=
      match k, xs with
      | 0, _ => need
      | _ + 1, [] => need
      | k' + 1, c :: cs =>
          let i := idx c
          initNeed (need.set! i (need[i]! - 1)) k' cs

    let need0 := initNeed needAfterS1 n s2

    -- Count how many indices are nonzero (constant-sized scan).
    let mismatch0 : Nat :=
      (List.range size).foldl (fun acc i =>
        if need0[i]! = 0 then acc else acc + 1) 0

    -- Drop k elements from a list (structural recursion).
    let rec dropNat : Nat → List Char → List Char
      | 0, xs => xs
      | _ + 1, [] => []
      | k + 1, _ :: xs => dropNat k xs

    let outs0 : List Char := s2
    let ins0 : List Char := dropNat n s2

    let windows : Nat := m - n + 1

    -- Slide window, maintaining `need` and `mismatch`.
    let rec go (need : Array Int) (mismatch : Nat) (outs ins : List Char) (t : Nat) : Bool :=
      match t with
      | 0 => false
      | t' + 1 =>
          if mismatch = 0 then
            true
          else
            match outs with
            | [] => false
            | outc :: outs' =>
                let outi := idx outc
                let outOld := need[outi]!
                let outNew := outOld + 1
                let mismatch1 :=
                  if outOld = 0 then mismatch + 1
                  else if outNew = 0 then mismatch - 1
                  else mismatch
                let need1 := need.set! outi outNew
                match ins with
                | [] =>
                    go need1 mismatch1 outs' [] t'
                | inc :: ins' =>
                    let ini := idx inc
                    let inOld := need1[ini]!
                    let inNew := inOld - 1
                    let mismatch2 :=
                      if inOld = 0 then mismatch1 + 1
                      else if inNew = 0 then mismatch1 - 1
                      else mismatch1
                    let need2 := need1.set! ini inNew
                    go need2 mismatch2 outs' ins' t'

    go need0 mismatch0 outs0 ins0 windows
end Impl

section TestCases
-- Test case 1: Example 1 from statement: s1="ab", s2="eidbaooo" → true (contains "ba").
def test1_s1 : List Char := ['a', 'b']
def test1_s2 : List Char := ['e','i','d','b','a','o','o','o']
def test1_Expected : Bool := true

-- Test case 2: Example 2 from statement: s1="ab", s2="eidboaoo" → false.
def test2_s1 : List Char := ['a', 'b']
def test2_s2 : List Char := ['e','i','d','b','o','a','o','o']
def test2_Expected : Bool := false

-- Test case 3: Empty s1 should always return true.
def test3_s1 : List Char := []
def test3_s2 : List Char := ['x','y','z']
def test3_Expected : Bool := true

-- Test case 4: Both empty: true.
def test4_s1 : List Char := []
def test4_s2 : List Char := []
def test4_Expected : Bool := true

-- Test case 5: s1 longer than s2: false.
def test5_s1 : List Char := ['a','b','c']
def test5_s2 : List Char := ['a','b']
def test5_Expected : Bool := false

-- Test case 6: Exact match where s2 itself is a permutation of s1: true.
def test6_s1 : List Char := ['c','a','t']
def test6_s2 : List Char := ['t','a','c']
def test6_Expected : Bool := true

-- Test case 7: Repeated characters: s1="aabc", s2 contains a matching window "caba".
def test7_s1 : List Char := ['a','a','b','c']
def test7_s2 : List Char := ['z','c','a','b','a','y']
def test7_Expected : Bool := true

-- Test case 8: Repeated characters but not enough multiplicity: false.
def test8_s1 : List Char := ['a','a']
def test8_s2 : List Char := ['b','a','c','a','d']
def test8_Expected : Bool := false

-- Test case 9: Single-character s1 not present in s2: false.
def test9_s1 : List Char := ['q']
def test9_s2 : List Char := ['a','b','c']
def test9_Expected : Bool := false

-- Recommend to validate: test1_Expected, test2_Expected, test8_Expected
end TestCases

section Assertions
-- Test case 1
#assert_same_evaluation #[(implementation test1_s1 test1_s2), test1_Expected]

-- Test case 2
#assert_same_evaluation #[(implementation test2_s1 test2_s2), test2_Expected]

-- Test case 3
#assert_same_evaluation #[(implementation test3_s1 test3_s2), test3_Expected]

-- Test case 4
#assert_same_evaluation #[(implementation test4_s1 test4_s2), test4_Expected]

-- Test case 5
#assert_same_evaluation #[(implementation test5_s1 test5_s2), test5_Expected]

-- Test case 6
#assert_same_evaluation #[(implementation test6_s1 test6_s2), test6_Expected]

-- Test case 7
#assert_same_evaluation #[(implementation test7_s1 test7_s2), test7_Expected]

-- Test case 8
#assert_same_evaluation #[(implementation test8_s1 test8_s2), test8_Expected]

-- Test case 9
#assert_same_evaluation #[(implementation test9_s1 test9_s2), test9_Expected]
end Assertions

section Pbt
method implementationPbt (s1 : List Char) (s2 : List Char)
  return (result : Bool)
  require precondition s1 s2
  ensures postcondition s1 s2 result
  do
  return (implementation s1 s2)

velvet_plausible_test implementationPbt (config := { maxMs := some 20000 })
end Pbt

section Proof
theorem correctness_goal_0
    (s1 : List Char)
    (s2 : List Char)
    (hs1 : ¬s1 = [])
    (hgt : ¬s1.length > s2.length)
    (hle : s1.length ≤ s2.length)
    : implementation s1 s2 = true ↔ ∃ i, i + s1.length ≤ s2.length ∧ isPermutationOf s1 (window s2 i s1.length) := by
    sorry

theorem correctness_goal
    (s1 : List Char)
    (s2 : List Char)
    (h_precond : precondition s1 s2)
    : postcondition s1 s2 (implementation s1 s2) := by
  classical
  -- precondition is trivial
  have : True := h_precond
  clear h_precond this
  by_cases hs1 : s1 = []
  · subst hs1
    -- n = 0 branch: implementation returns true, and an empty window exists at i=0
    have : (implementation ([] : List Char) s2) = true := by
      simp [implementation]
    -- prove the postcondition directly
    unfold postcondition
    constructor
    · intro _
      refine ⟨0, ?_, ?_⟩
      · simpa
      · simp [isPermutationOf, window]
    · intro _
      simpa [implementation]
  · by_cases hgt : s1.length > s2.length
    · -- n > m branch
      have hno : ¬ (∃ i : Nat, i + s1.length ≤ s2.length ∧ isPermutationOf s1 (window s2 i s1.length)) := by
        intro hex
        rcases hex with ⟨i, hi, _⟩
        have : s1.length ≤ s2.length := le_trans (Nat.le_add_left _ _) hi
        exact (not_le_of_gt hgt) this
      -- implementation returns false
      simp [postcondition, implementation, hs1, hgt, hno]
    · -- main sliding-window branch
      have hle : s1.length ≤ s2.length := le_of_not_gt hgt
      have hmain : (implementation s1 s2 = true ↔
          (∃ i : Nat,
            i + s1.length ≤ s2.length ∧
            isPermutationOf s1 (window s2 i s1.length))) := by
        -- core correctness of go/initNeed/mismatch
        expose_names; exact (correctness_goal_0 s1 s2 hs1 hgt hle)
      simpa [postcondition] using hmain
end Proof
