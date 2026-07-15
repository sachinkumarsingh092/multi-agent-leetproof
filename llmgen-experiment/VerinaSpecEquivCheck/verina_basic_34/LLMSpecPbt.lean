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
    ExtractEvenFromArray: extract even integers from an array while preserving order.
    Natural language breakdown:
    1. The input is an array `arr` of integers.
    2. An integer is even exactly when it is divisible by 2 (i.e., `x % 2 = 0`).
    3. The output is an array `result` containing only even integers.
    4. Every element of `result` is an element of `arr`.
    5. No odd integer value appears in `result`.
    6. For every even integer value, its number of occurrences (multiplicity) in `result` equals its number of occurrences in `arr`.
    7. The relative order of the retained (even) integers in `result` matches their order in `arr`.
    8. The method has no preconditions; it must handle empty arrays.
-/

section Specs
-- Helper predicate: evenness for Int.
-- We keep it as a Prop; we avoid needing decidability by never branching (`if`) on it in specs.
def EvenInt (x : Int) : Prop := x % 2 = 0

-- Order preservation: `result` is obtained by selecting elements from `arr` at strictly increasing indices.
-- This expresses that `result` is a subsequence of `arr` (with multiplicity), and preserves order.
def isOrderPreservingSelection (arr : Array Int) (result : Array Int) : Prop :=
  ∃ f : Nat → Nat,
    (∀ i : Nat, i < result.size → f i < arr.size ∧ result[i]! = arr[f i]!) ∧
    (∀ i : Nat, ∀ j : Nat, i < j → j < result.size → f i < f j)

-- No preconditions.
def precondition (arr : Array Int) : Prop :=
  True

-- Postcondition:
-- 1) Every element in `result` is even.
-- 2) For each integer value x:
--    - if x is even, its multiplicity is preserved (same count as in `arr`)
--    - if x is odd, it does not appear in `result` (count = 0)
-- 3) The relative order of the kept elements matches their order in `arr`.
def postcondition (arr : Array Int) (result : Array Int) : Prop :=
  (∀ i : Nat, i < result.size → EvenInt (result[i]!)) ∧
  (∀ x : Int, EvenInt x → result.count x = arr.count x) ∧
  (∀ x : Int, ¬ EvenInt x → result.count x = 0) ∧
  isOrderPreservingSelection arr result
end Specs

section Impl
method ExtractEvenFromArray (arr : Array Int)
  return (result : Array Int)
  require precondition arr
  ensures postcondition arr result
  do
  pure #[]

prove_correct ExtractEvenFromArray by sorry
end Impl

section TestCases
-- Test case 1: mixed positive integers
-- Input: [1,2,3,4,5,6] => Output: [2,4,6]
def test1_arr : Array Int := #[1, 2, 3, 4, 5, 6]
def test1_Expected : Array Int := #[2, 4, 6]

-- Test case 2: empty array
-- Input: [] => Output: []
def test2_arr : Array Int := #[]
def test2_Expected : Array Int := #[]

-- Test case 3: all odd
-- Input: [1,3,5,7] => Output: []
def test3_arr : Array Int := #[1, 3, 5, 7]
def test3_Expected : Array Int := #[]

-- Test case 4: all even
-- Input: [2,4,6] => Output: [2,4,6]
def test4_arr : Array Int := #[2, 4, 6]
def test4_Expected : Array Int := #[2, 4, 6]

-- Test case 5: includes 0 and negative values
-- Input: [0,-1,-2,-3,-4] => Output: [0,-2,-4]
def test5_arr : Array Int := #[0, -1, -2, -3, -4]
def test5_Expected : Array Int := #[0, -2, -4]

-- Test case 6: duplicates, preserve multiplicity and order
-- Input: [2,2,3,2,4,4,5] => Output: [2,2,2,4,4]
def test6_arr : Array Int := #[2, 2, 3, 2, 4, 4, 5]
def test6_Expected : Array Int := #[2, 2, 2, 4, 4]

-- Test case 7: singleton even (boundary)
-- Input: [0] => Output: [0]
def test7_arr : Array Int := #[0]
def test7_Expected : Array Int := #[0]

-- Test case 8: singleton odd (boundary)
-- Input: [1] => Output: []
def test8_arr : Array Int := #[1]
def test8_Expected : Array Int := #[]

-- Test case 9: alternating signs and parity
-- Input: [-5,-4,-3,-2,-1] => Output: [-4,-2]
def test9_arr : Array Int := #[-5, -4, -3, -2, -1]
def test9_Expected : Array Int := #[-4, -2]

-- Recommend to validate: empty input, all-odd input, all-even input
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test9' (result : Array Int) :
  result ≠ test9_Expected →
  ¬ postcondition test9_arr result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test9_Expected]) (config := { numInst := 100000 })
