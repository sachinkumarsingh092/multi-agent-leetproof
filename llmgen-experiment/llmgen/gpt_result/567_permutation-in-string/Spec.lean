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
  pure false

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
