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
    DedupPreserveFirst: Remove duplicate elements from a list of integers while preserving the order of first occurrence.
    Natural language breakdown:
    1. We are given a list of integers s; it may contain duplicate values.
    2. The output is a list result that contains each integer value at most once (no duplicates).
    3. Every value that appears in the input must appear in the output, and no new values may appear.
    4. Order is preserved by first occurrences: if x appears before y for the first time in s, then x must appear before y in result.
    5. Equivalently, each element in result is paired with its first-occurrence position in s, and these positions strictly increase along result.
    6. The method must handle all lists, including the empty list.
-/

section Specs
-- x has its first occurrence in s exactly at position p.
-- This characterizes first occurrence without using any library index-finding API.
def FirstOccurrenceAt (x : Int) (s : List Int) (p : Nat) : Prop :=
  p < s.length ∧
  s[p]! = x ∧
  ∀ q : Nat, q < p → s[q]! ≠ x

def precondition (s : List Int) : Prop :=
  True

def postcondition (s : List Int) (result : List Int) : Prop :=
  -- No duplicates in the output.
  result.Nodup ∧
  -- Output contains exactly the elements that appear in the input.
  (∀ x : Int, x ∈ result ↔ x ∈ s) ∧
  -- Every output element is taken at its first occurrence position in s.
  (∀ i : Nat, i < result.length → ∃ p : Nat, FirstOccurrenceAt (result[i]!) s p) ∧
  -- The first-occurrence positions of elements of result are strictly increasing in result order.
  (∀ i j : Nat, i < j → j < result.length →
    ∃ pi pj : Nat,
      FirstOccurrenceAt (result[i]!) s pi ∧
      FirstOccurrenceAt (result[j]!) s pj ∧
      pi < pj)
end Specs

section Impl
method DedupPreserveFirst (s : List Int)
  return (result : List Int)
  require precondition s
  ensures postcondition s result
  do
  pure ([] : List Int)  -- placeholder

prove_correct DedupPreserveFirst by sorry
end Impl

section TestCases
-- Test case 1: example from description
-- [1, 3, 2, 2, 3, 5] => [1, 3, 2, 5]
def test1_s : List Int := [1, 3, 2, 2, 3, 5]
def test1_Expected : List Int := [1, 3, 2, 5]

-- Test case 2: empty list
def test2_s : List Int := []
def test2_Expected : List Int := []

-- Test case 3: singleton list
def test3_s : List Int := [7]
def test3_Expected : List Int := [7]

-- Test case 4: already unique (order preserved)
def test4_s : List Int := [4, 3, 2, 1]
def test4_Expected : List Int := [4, 3, 2, 1]

-- Test case 5: all elements the same
def test5_s : List Int := [9, 9, 9, 9]
def test5_Expected : List Int := [9]

-- Test case 6: includes -1, 0, 1 with repetition (required edge values for Int)
def test6_s : List Int := [-1, 0, -1, 1, 0, 1]
def test6_Expected : List Int := [-1, 0, 1]

-- Test case 7: duplicates not adjacent
def test7_s : List Int := [2, 1, 2, 3, 1, 4, 3]
def test7_Expected : List Int := [2, 1, 3, 4]

-- Test case 8: boundary-like small values including 0 and 1 with duplicates
def test8_s : List Int := [0, 1, 0, 1, 2, 2]
def test8_Expected : List Int := [0, 1, 2]

-- Test case 9: mixed order with repeated first element later
def test9_s : List Int := [5, 4, 5, 3, 2, 3, 1, 2]
def test9_Expected : List Int := [5, 4, 3, 2, 1]

-- Recommend to validate: empty input, all-duplicates input, non-adjacent duplicates
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test3' (result : List Int) :
  result ≠ test3_Expected →
  ¬ postcondition test3_s result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test3_Expected]) (config := { numInst := 100000 })
