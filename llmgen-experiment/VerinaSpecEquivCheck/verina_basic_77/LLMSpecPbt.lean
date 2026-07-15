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
    Update2D: Update one element in a 2-dimensional array of natural numbers
    Natural language breakdown:
    1. The input is an outer array `arr` whose elements are inner arrays of natural numbers.
    2. `index1` selects which inner array to modify (0-indexed in the outer array).
    3. `index2` selects which element to modify within that chosen inner array (0-indexed).
    4. `val` is the new natural number that should replace the old value at coordinates `(index1, index2)`.
    5. The output must have the same outer size as the input.
    6. For every outer index `i ≠ index1`, the inner array at `i` is unchanged.
    7. For the modified inner array at `index1`, the inner size is unchanged.
    8. In the modified inner array, the element at `index2` is exactly `val`.
    9. In the modified inner array, every element at position `j ≠ index2` is unchanged.
    10. It is assumed `index1` is a valid index of the outer array and `index2` is a valid index of the selected inner array; this is captured as a precondition.
-/

section Specs
-- Preconditions: indices are in bounds.
-- This captures the problem statement assumption that both indices are valid.
-- The bounds also ensure all array indexing used in the postcondition is safe.
def precondition (arr : Array (Array Nat)) (index1 : Nat) (index2 : Nat) (val : Nat) : Prop :=
  index1 < arr.size ∧
  index2 < (arr[index1]!).size

-- Postcondition: outer size preserved; only the selected cell (index1,index2) is updated.
-- All other inner arrays are identical; in the modified inner array, all other positions are identical.
def postcondition (arr : Array (Array Nat)) (index1 : Nat) (index2 : Nat) (val : Nat)
    (result : Array (Array Nat)) : Prop :=
  result.size = arr.size ∧
  (∀ (i : Nat), i < arr.size →
    (if _h1 : i = index1 then
        let a : Array Nat := arr[i]!
        let r : Array Nat := result[i]!
        r.size = a.size ∧
        (∀ (j : Nat), j < a.size →
          (if _h2 : j = index2 then
              r[j]! = val
            else
              r[j]! = a[j]!))
      else
        result[i]! = arr[i]!))
end Specs

section Impl
method Update2D (arr : Array (Array Nat)) (index1 : Nat) (index2 : Nat) (val : Nat)
  return (result : Array (Array Nat))
  require precondition arr index1 index2 val
  ensures postcondition arr index1 index2 val result
  do
  pure arr  -- placeholder body only

prove_correct Update2D by sorry
end Impl

section TestCases
-- Test case 1: update a middle element in a 2-inner-array structure
-- (Example from previous attempts)
def test1_arr : Array (Array Nat) := #[#[1, 2, 3], #[4, 5]]
def test1_index1 : Nat := 0
def test1_index2 : Nat := 1
def test1_val : Nat := 9
def test1_Expected : Array (Array Nat) := #[#[1, 9, 3], #[4, 5]]

-- Test case 2: update element (0,0) in a singleton inner array (includes Nat 0)
def test2_arr : Array (Array Nat) := #[#[7]]
def test2_index1 : Nat := 0
def test2_index2 : Nat := 0
def test2_val : Nat := 0
def test2_Expected : Array (Array Nat) := #[#[0]]

-- Test case 3: update last inner array, last element
def test3_arr : Array (Array Nat) := #[#[10, 11], #[12, 13, 14]]
def test3_index1 : Nat := 1
def test3_index2 : Nat := 2
def test3_val : Nat := 99
def test3_Expected : Array (Array Nat) := #[#[10, 11], #[12, 13, 99]]

-- Test case 4: outer array has three inner arrays, update middle inner array at first element
def test4_arr : Array (Array Nat) := #[#[0, 1], #[2, 3], #[4, 5]]
def test4_index1 : Nat := 1
def test4_index2 : Nat := 0
def test4_val : Nat := 8
def test4_Expected : Array (Array Nat) := #[#[0, 1], #[8, 3], #[4, 5]]

-- Test case 5: update an element to the same value (no observable change)
def test5_arr : Array (Array Nat) := #[#[1, 1, 1]]
def test5_index1 : Nat := 0
def test5_index2 : Nat := 2
def test5_val : Nat := 1
def test5_Expected : Array (Array Nat) := #[#[1, 1, 1]]

-- Test case 6: outer array includes empty inner arrays; update the only element in the non-empty one
def test6_arr : Array (Array Nat) := #[#[], #[5], #[]]
def test6_index1 : Nat := 1
def test6_index2 : Nat := 0
def test6_val : Nat := 6
def test6_Expected : Array (Array Nat) := #[#[], #[6], #[]]

-- Test case 7: larger inner array; update a non-boundary index
def test7_arr : Array (Array Nat) := #[#[2, 4, 6, 8, 10], #[1, 3]]
def test7_index1 : Nat := 0
def test7_index2 : Nat := 3
def test7_val : Nat := 7
def test7_Expected : Array (Array Nat) := #[#[2, 4, 6, 7, 10], #[1, 3]]

-- Test case 8: update last outer index when outer size is 2
def test8_arr : Array (Array Nat) := #[#[0], #[9, 9]]
def test8_index1 : Nat := 1
def test8_index2 : Nat := 1
def test8_val : Nat := 1
def test8_Expected : Array (Array Nat) := #[#[0], #[9, 1]]

-- Test case 9: update at (last outer index, first inner index)
def test9_arr : Array (Array Nat) := #[#[3, 3, 3], #[4, 4]]
def test9_index1 : Nat := 1
def test9_index2 : Nat := 0
def test9_val : Nat := 1
def test9_Expected : Array (Array Nat) := #[#[3, 3, 3], #[1, 4]]

-- Recommend to validate: postcondition framing, index bounds coverage, behavior with empty inner arrays
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test9' (result : Array (Array Nat)) :
  result ≠ test9_Expected →
  ¬ postcondition test9_arr test9_index1 test9_index2 test9_val result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test9_Expected]) (config := { numInst := 100000 })
