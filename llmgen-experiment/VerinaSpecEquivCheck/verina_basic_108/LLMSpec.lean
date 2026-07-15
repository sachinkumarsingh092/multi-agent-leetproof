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
    PartialSumsWithNegativeFlag: compute cumulative results of sequential integer operations.
    Natural language breakdown:
    1. Input is a list of integer operations performed sequentially.
    2. We construct an array of partial sums with size one more than the number of operations.
    3. The first partial sum is 0 (no operations performed yet).
    4. For each index i with 0 ≤ i < operations.length, the (i+1)-th partial sum equals the i-th partial sum plus operations[i].
    5. Equivalently, for any i within the bounds of the partial-sum array, the i-th partial sum equals the sum of the first i operations.
    6. We also output a boolean flag that is true exactly when at least one partial sum after the initial 0 is negative.
    7. The empty list is valid: then the partial-sum array is [0] and the flag is false.
-/

section Specs
-- Helper: interpret a partial sum at index i as the sum of the first i operations.
-- We rely on Mathlib/Init definitions: List.take and List.sum.

def precondition (operations : List Int) : Prop :=
  True

def postcondition (operations : List Int) (result : (Array Int × Bool)) : Prop :=
  let ps : Array Int := result.1
  let neg : Bool := result.2
  -- Shape of the partial-sum array
  ps.size = operations.length + 1 ∧
  -- Each position i contains the sum of the first i operations
  (∀ (i : Nat), i < ps.size → ps[i]! = (operations.take i).sum) ∧
  -- Negativity flag: some partial sum after index 0 is negative
  (neg = true ↔ ∃ (i : Nat), i < ps.size ∧ i ≠ 0 ∧ ps[i]! < 0)
end Specs

section Impl
method PartialSumsWithNegativeFlag (operations : List Int)
  return (result : (Array Int × Bool))
  require precondition operations
  ensures postcondition operations result
  do
  pure (#[0], false)

end Impl

section TestCases
-- Test case 1: empty operations
def test1_operations : List Int := []
def test1_Expected : (Array Int × Bool) := (#[0], false)

-- Test case 2: single positive operation
def test2_operations : List Int := [5]
def test2_Expected : (Array Int × Bool) := (#[0, 5], false)

-- Test case 3: single negative operation (negative partial sum exists)
def test3_operations : List Int := [-1]
def test3_Expected : (Array Int × Bool) := (#[0, -1], true)

-- Test case 4: mix with negative reached later
def test4_operations : List Int := [3, -10, 4]
def test4_Expected : (Array Int × Bool) := (#[0, 3, -7, -3], true)

-- Test case 5: negatives in operations but never negative partial sum
def test5_operations : List Int := [10, -3, -2]
def test5_Expected : (Array Int × Bool) := (#[0, 10, 7, 5], false)

-- Test case 6: includes zeros only
def test6_operations : List Int := [0, 0, 0]
def test6_Expected : (Array Int × Bool) := (#[0, 0, 0, 0], false)

-- Test case 7: negative immediately then recovers
def test7_operations : List Int := [-2, 5]
def test7_Expected : (Array Int × Bool) := (#[0, -2, 3], true)

-- Test case 8: longer list with alternating changes, never negative
def test8_operations : List Int := [1, -1, 2, -2, 3]
def test8_Expected : (Array Int × Bool) := (#[0, 1, 0, 2, 0, 3], false)

-- Test case 9: large magnitude negative at end
def test9_operations : List Int := [100, 20, -150]
def test9_Expected : (Array Int × Bool) := (#[0, 100, 120, -30], true)
end TestCases
