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
    TopKFrequentElements: return the k most frequent integers from a list of integers.
    Natural language breakdown:
    1. Input `nums` is a list of integers and may contain duplicates.
    2. For each integer value x, its frequency is the number of occurrences of x in `nums`.
    3. Input `k` is a natural number and satisfies k ≤ (number of distinct elements in nums).
    4. The output `result` is a list of integers of length exactly k.
    5. Every element of `result` must be a distinct element that occurs in `nums`.
    6. The elements of `result` must be ordered from higher frequency to lower frequency.
    7. When two values have the same frequency, any consistent ordering is acceptable.
    8. To make the specification deterministic (and thus uniquely characterizing), we fix a consistent tie-breaker:
       among equal frequencies, smaller first-occurrence index in `nums` comes first.
-/

section Specs
-- Frequency of an integer in a list (uses the Std/Init definition `List.count`)
def freq (nums : List Int) (x : Int) : Nat :=
  nums.count x

-- First index where x appears in nums; if x is absent, returns nums.length
-- (This total function is convenient for tie-breaking; in the postcondition we only
-- use it for values that are known to be in nums.)
def firstIndex (nums : List Int) (x : Int) : Nat :=
  match nums.findIdx? (fun y => y = x) with
  | some i => i
  | none => nums.length

-- Strict ordering used for a deterministic "top-k":
-- higher frequency first; for ties, earlier first occurrence first.
def precedesByFreqThenFirst (nums : List Int) (a : Int) (b : Int) : Prop :=
  let fa := freq nums a
  let fb := freq nums b
  let ia := firstIndex nums a
  let ib := firstIndex nums b
  (fa > fb) ∨ (fa = fb ∧ ia < ib)

-- List is strictly sorted by the above precedence.
def isSortedByFreqThenFirst (nums : List Int) (xs : List Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < xs.length →
    precedesByFreqThenFirst nums xs[i]! xs[j]!

-- k must not exceed the number of distinct values present.
-- We use `eraseDups` as the canonical distinct-elements list.
def precondition (nums : List Int) (k : Nat) : Prop :=
  k ≤ nums.eraseDups.length

-- Postcondition: result is the first k elements of the uniquely determined
-- ordering of all distinct elements by descending frequency and first occurrence.
def postcondition (nums : List Int) (k : Nat) (result : List Int) : Prop :=
  ∃ (sortedAll : List Int),
    sortedAll.Nodup ∧
    (∀ (x : Int), x ∈ sortedAll ↔ x ∈ nums) ∧
    isSortedByFreqThenFirst nums sortedAll ∧
    result = sortedAll.take k
end Specs

section Impl
method TopKFrequentElements (nums : List Int) (k : Nat)
  return (result : List Int)
  require precondition nums k
  ensures postcondition nums k result
  do
  pure []

prove_correct TopKFrequentElements by sorry
end Impl

section TestCases
-- Test case 1: typical case with a clear top-2
def test1_nums : List Int := [1, 1, 1, 2, 2, 3]
def test1_k : Nat := 2
def test1_Expected : List Int := [1, 2]

-- Test case 2: k = 0 should always return empty list (valid for any nums)
def test2_nums : List Int := [5, 5, 6]
def test2_k : Nat := 0
def test2_Expected : List Int := []

-- Test case 3: empty input with k = 0
def test3_nums : List Int := []
def test3_k : Nat := 0
def test3_Expected : List Int := []

-- Test case 4: all elements distinct; ordering determined by first occurrence (all freqs = 1)
def test4_nums : List Int := [10, 20, 30]
def test4_k : Nat := 2
def test4_Expected : List Int := [10, 20]

-- Test case 5: includes negative integers
def test5_nums : List Int := [-1, -1, 0, 1, 1, 1]
def test5_k : Nat := 2
def test5_Expected : List Int := [1, -1]

-- Test case 6: tie on top frequency; tie-break by first occurrence
-- Here 7 and 8 both have frequency 2; 7 appears first.
def test6_nums : List Int := [7, 8, 8, 7, 9]
def test6_k : Nat := 2
def test6_Expected : List Int := [7, 8]

-- Test case 7: k equals number of distinct elements
def test7_nums : List Int := [4, 4, 4, 3, 3, 2, 1]
def test7_k : Nat := 4
-- freqs: 4↦3, 3↦2, 2↦1, 1↦1; tie between 2 and 1 resolved by first occurrence (2 before 1)
def test7_Expected : List Int := [4, 3, 2, 1]

-- Test case 8: many ties in the middle; checks stable tie-breaking by first occurrence
def test8_nums : List Int := [2, 3, 2, 3, 4, 5]
def test8_k : Nat := 4
-- freqs: 2↦2, 3↦2, 4↦1, 5↦1; tie(2,3) by firstIndex: 2 before 3; tie(4,5) by firstIndex: 4 before 5
def test8_Expected : List Int := [2, 3, 4, 5]

-- Test case 9: singleton list with k = 1
def test9_nums : List Int := [42]
def test9_k : Nat := 1
def test9_Expected : List Int := [42]
end TestCases

set_option maxHeartbeats 500000

def testpostcondition_test7 :
  postcondition test7_nums test7_k test7_Expected := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  plausible' (config := { numInst := 100000 })
