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
    ArraySetIndexTo60: Update an array of integers by setting the element at a given index to 60.
    Natural language breakdown:
    1. Input is an array of integers `a` and a natural number index `j`.
    2. The index `j` is 0-based and is assumed to be a valid index into `a`.
    3. The output is an array `result` of the same size as `a`.
    4. At index `j`, the output array contains the integer value 60.
    5. For every index `i` different from `j`, the output array agrees with `a` at `i`.
-/

section Specs
-- Precondition: the update index must be in bounds.
-- Note: The constraint 0 ≤ j is automatic since j : Nat.
def precondition (a : Array Int) (j : Nat) : Prop :=
  j < a.size

-- Postcondition: same size; pointwise update semantics.
def postcondition (a : Array Int) (j : Nat) (result : Array Int) : Prop :=
  result.size = a.size ∧
  (∀ (i : Nat), i < a.size → result[i]! = (if i = j then (60 : Int) else a[i]!))
end Specs

section Impl
method ArraySetIndexTo60 (a : Array Int) (j : Nat)
  return (result : Array Int)
  require precondition a j
  ensures postcondition a j result
  do
  pure a  -- placeholder body

prove_correct ArraySetIndexTo60 by sorry
end Impl

section TestCases
-- Test case 1: typical array, middle index updated
def test1_a : Array Int := #[10, 20, 30, 40]
def test1_j : Nat := 2
def test1_Expected : Array Int := #[10, 20, 60, 40]

-- Test case 2: update at index 0 (boundary index)
def test2_a : Array Int := #[5, 6, 7]
def test2_j : Nat := 0
def test2_Expected : Array Int := #[60, 6, 7]

-- Test case 3: update at last index (boundary index)
def test3_a : Array Int := #[1, 2, 3, 4, 5]
def test3_j : Nat := 4
def test3_Expected : Array Int := #[1, 2, 3, 4, 60]

-- Test case 4: singleton array (size = 1)
def test4_a : Array Int := #[99]
def test4_j : Nat := 0
def test4_Expected : Array Int := #[60]

-- Test case 5: array containing negative values
def test5_a : Array Int := #[-1, -2, -3]
def test5_j : Nat := 1
def test5_Expected : Array Int := #[-1, 60, -3]

-- Test case 6: index points to an element already equal to 60
def test6_a : Array Int := #[60, 1, 60]
def test6_j : Nat := 2
def test6_Expected : Array Int := #[60, 1, 60]

-- Test case 7: array with repeated values; update one occurrence
def test7_a : Array Int := #[7, 7, 7, 7]
def test7_j : Nat := 1
def test7_Expected : Array Int := #[7, 60, 7, 7]

-- Test case 8: larger array; update near the front
def test8_a : Array Int := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
def test8_j : Nat := 3
def test8_Expected : Array Int := #[0, 1, 2, 60, 4, 5, 6, 7, 8, 9]
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test8' (result : Array Int) :
  result ≠ test8_Expected →
  ¬ postcondition test8_a test8_j result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test8_Expected]) (config := { numInst := 100000 })
