import Velvet.Std
import Extensions.Tactics
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false
set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

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

section Specs
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
method CheckInclusion (s1 : List Char) (s2 : List Char)
  return (result : Bool)
  require precondition s1 s2
  ensures postcondition s1 s2 result
  do
  -- Sliding window using a fixed-size difference array over all Unicode scalar values.
  -- Char.toNat < 0x110000, so the alphabet size is a constant 1114112.
  let n1 : Nat := s1.length
  let n2 : Nat := s2.length

  if n1 = 0 then
    return true
  else
    if n1 > n2 then
      return false
    else
      let a1 : Array Char := s1.toArray
      let a2 : Array Char := s2.toArray

      let K : Nat := 1114112
      let kI : Int := (K : Int)

      -- diff[c] = count_s1(c) - count_window(c)
      let mut diff : Array Int := Array.replicate K 0

      -- initialize diff with s1 and the first window of s2
      let mut i : Nat := 0
      while i < n1
        -- i is a prefix length of both s1 and the initial window of s2.
        invariant "init_i_le" i ≤ n1
        -- diff stays a length-K array.
        invariant "init_diff_size" diff.size = K
        -- diff models the count difference between the first i chars of s1 and s2.
        invariant "init_diff_model"
          ∀ c : Char,
            diff[c.toNat]! = ((window s1 0 i).count c : Int) - ((window s2 0 i).count c : Int)
        decreasing (n1 - i)
      do
        let c1 : Char := a1[i]!
        let c2 : Char := a2[i]!
        let k1 : Nat := c1.toNat
        let k2 : Nat := c2.toNat

        -- These bounds should always hold for Char, but keep them explicit.
        if k1 < K then
          diff := diff.set! k1 (diff[k1]! + 1)
        if k2 < K then
          diff := diff.set! k2 (diff[k2]! - 1)

        i := i + 1

      -- count how many entries are zero (a constant-time scan in terms of |s1|+|s2|)
      let mut zeros : Int := 0
      let mut j : Nat := 0
      while j < K
        -- scan index bounds.
        invariant "zeros_j_le" j ≤ K
        invariant "zeros_diff_size" diff.size = K
        -- zeros is always between 0 and j (inclusive).
        invariant "zeros_bounds" (0 : Int) ≤ zeros ∧ zeros ≤ (j : Int)
        -- if zeros reaches the maximum possible value j, then all scanned entries are 0.
        invariant "zeros_all0_if_max"
          zeros = (j : Int) → (∀ t : Nat, t < j → diff[t]! = 0)
        decreasing (K - j)
      do
        if diff[j]! = 0 then
          zeros := zeros + 1
        j := j + 1

      if zeros = kI then
        return true
      else
        let mut left : Nat := 0
        let mut right : Nat := n1
        let mut found : Bool := false

        while (right < n2 ∧ found = false)
          invariant "slide_diff_size" diff.size = K
          -- window endpoints track a fixed length-n1 window.
          invariant "slide_window" right = left + n1
          -- bounds for the window indices.
          invariant "slide_bounds" left ≤ right ∧ right ≤ n2
          -- diff models count(s1) - count(current window of s2).
          invariant "slide_diff_model"
            ∀ c : Char,
              diff[c.toNat]! = (s1.count c : Int) - ((window s2 left n1).count c : Int)
          -- if zeros reports all K entries are 0, then diff is identically 0.
          invariant "slide_all0_if_full"
            zeros = kI → (∀ t : Nat, t < K → diff[t]! = 0)
          -- if we are still searching, all windows up to left are ruled out.
          invariant "slide_checked"
            found = false →
              (∀ i0 : Nat,
                i0 ≤ left →
                  ¬ isPermutationOf s1 (window s2 i0 n1))
          done_with (right ≥ n2 ∨ found = true)
          decreasing (n2 - right)
        do
          let outc : Char := a2[left]!
          let inc : Char := a2[right]!
          let kout : Nat := outc.toNat
          let kin : Nat := inc.toNat

          -- update for outgoing character: window count decreases by 1 => diff increases by 1
          if kout < K then
            let before : Int := diff[kout]!
            let after : Int := before + 1
            diff := diff.set! kout after
            if before = 0 then
              zeros := zeros - 1
            if after = 0 then
              zeros := zeros + 1

          -- update for incoming character: window count increases by 1 => diff decreases by 1
          if kin < K then
            let before2 : Int := diff[kin]!
            let after2 : Int := before2 - 1
            diff := diff.set! kin after2
            if before2 = 0 then
              zeros := zeros - 1
            if after2 = 0 then
              zeros := zeros + 1

          left := left + 1
          right := right + 1

          if zeros = kI then
            found := true

        return found
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

#assert_same_evaluation #[((CheckInclusion test1_s1 test1_s2).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((CheckInclusion test2_s1 test2_s2).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((CheckInclusion test3_s1 test3_s2).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((CheckInclusion test4_s1 test4_s2).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((CheckInclusion test5_s1 test5_s2).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((CheckInclusion test6_s1 test6_s2).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((CheckInclusion test7_s1 test7_s2).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((CheckInclusion test8_s1 test8_s2).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((CheckInclusion test9_s1 test9_s2).run), DivM.res test9_Expected ]
end Assertions

section Pbt
velvet_plausible_test CheckInclusion (config := { maxMs := some 20000 })
end Pbt
