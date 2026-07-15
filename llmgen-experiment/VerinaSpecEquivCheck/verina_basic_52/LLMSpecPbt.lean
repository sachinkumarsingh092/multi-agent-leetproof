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
    ArraySortNonDecreasing: Sort an array of integers in non-decreasing order.
    Natural language breakdown:
    1. The input is an array of integers; it may be empty or non-empty.
    2. The output is an array of integers.
    3. The output must have the same size as the input.
    4. The output must be sorted in non-decreasing order: earlier indices hold values ≤ later indices.
    5. The output must be a rearrangement of the input: for every integer value v,
       the number of occurrences of v in the output equals the number of occurrences of v in the input.
    6. No additional preconditions are required.
-/

section Specs
-- Helper predicate: non-decreasing sortedness via index comparison.
-- We use Nat indices with explicit bounds to avoid Fin-index proof overhead.
def isSortedNonDecreasing (arr : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < arr.size → arr[i]! ≤ arr[j]!

-- Helper predicate: multiset preservation stated as equality of occurrence counts.
-- `countP` counts elements satisfying a Bool predicate; we use Bool equality `==`.
def sameElementCounts (a : Array Int) (b : Array Int) : Prop :=
  ∀ (v : Int), a.countP (fun x => x == v) = b.countP (fun x => x == v)

def precondition (a : Array Int) : Prop :=
  True

def postcondition (a : Array Int) (result : Array Int) : Prop :=
  result.size = a.size ∧
  isSortedNonDecreasing result ∧
  sameElementCounts a result
end Specs

section Impl
method ArraySortNonDecreasing (a : Array Int)
  return (result : Array Int)
  require precondition a
  ensures postcondition a result
  do
    -- Placeholder implementation only.
    pure a

prove_correct ArraySortNonDecreasing by sorry
end Impl

section TestCases
-- Test case 1: typical unsorted distinct elements
def test1_a : Array Int := #[3, 1, 2]
def test1_Expected : Array Int := #[1, 2, 3]

-- Test case 2: empty array
def test2_a : Array Int := #[]
def test2_Expected : Array Int := #[]

-- Test case 3: singleton
def test3_a : Array Int := #[42]
def test3_Expected : Array Int := #[42]

-- Test case 4: already sorted with negatives (includes -1, 0, 1)
def test4_a : Array Int := #[-1, 0, 1, 2]
def test4_Expected : Array Int := #[-1, 0, 1, 2]

-- Test case 5: reverse-sorted
def test5_a : Array Int := #[5, 4, 3, 2, 1]
def test5_Expected : Array Int := #[1, 2, 3, 4, 5]

-- Test case 6: duplicates
def test6_a : Array Int := #[2, 1, 2, 1, 2]
def test6_Expected : Array Int := #[1, 1, 2, 2, 2]

-- Test case 7: all equal
def test7_a : Array Int := #[7, 7, 7, 7]
def test7_Expected : Array Int := #[7, 7, 7, 7]

-- Test case 8: mixed negatives/positives with duplicates
def test8_a : Array Int := #[0, -3, 2, -3, 1]
def test8_Expected : Array Int := #[-3, -3, 0, 1, 2]

-- Test case 9: larger mixture
def test9_a : Array Int := #[10, -1, 3, 3, 0, 8, -5]
def test9_Expected : Array Int := #[-5, -1, 0, 3, 3, 8, 10]
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test3' (result : Array Int) :
  result ≠ test3_Expected →
  ¬ postcondition test3_a result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test3_Expected]) (config := { numInst := 100000 })
