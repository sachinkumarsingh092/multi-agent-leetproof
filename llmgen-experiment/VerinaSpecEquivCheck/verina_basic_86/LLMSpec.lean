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
    RotateLeftArray: rotate an array of integers to the left by a non-negative offset.
    Natural language breakdown:
    1. Input is an array a of integers; a may be empty or non-empty.
    2. Input offset is an integer representing the number of positions to rotate left.
    3. The offset is assumed to be non-negative.
    4. The output is an array result.
    5. If a is empty, result is empty.
    6. If a has size n > 0, result has the same size n.
    7. For every valid index i with i < n, the element at result[i] equals the element of a
       at index ((i + offset) mod n).
    8. Rotation is by offset positions; offsets larger than n wrap around by modulo n.
-/

section Specs
-- Helper: the effective (wrapped) rotation amount in Nat, when n = a.size.
-- For n = 0, this value is defined but not used by the postcondition.
def effectiveOffset (a : Array Int) (offset : Int) : Nat :=
  offset.toNat % a.size

def precondition (a : Array Int) (offset : Int) : Prop :=
  0 ≤ offset

def postcondition (a : Array Int) (offset : Int) (result : Array Int) : Prop :=
  (a.size = 0 → result.size = 0) ∧
  (a.size > 0 →
    result.size = a.size ∧
    (∀ (i : Nat), i < a.size →
      result[i]! = a[(i + effectiveOffset a offset) % a.size]!))
end Specs

section Impl
method RotateLeftArray (a : Array Int) (offset : Int)
  return (result : Array Int)
  require precondition a offset
  ensures postcondition a offset result
  do
  pure a  -- placeholder

end Impl

section TestCases
-- Test case 1: typical non-empty array, offset 2
-- Left rotation by 2: [10,20,30,40,50] -> [30,40,50,10,20]
def test1_a : Array Int := #[10, 20, 30, 40, 50]
def test1_offset : Int := 2
def test1_Expected : Array Int := #[30, 40, 50, 10, 20]

-- Test case 2: empty array, any offset -> empty

def test2_a : Array Int := #[]
def test2_offset : Int := 0
def test2_Expected : Array Int := #[]

-- Test case 3: singleton array, offset 0 -> unchanged

def test3_a : Array Int := #[7]
def test3_offset : Int := 0
def test3_Expected : Array Int := #[7]

-- Test case 4: singleton array, offset 1 -> unchanged (wraps)

def test4_a : Array Int := #[7]
def test4_offset : Int := 1
def test4_Expected : Array Int := #[7]

-- Test case 5: offset 0 on non-empty array -> unchanged

def test5_a : Array Int := #[1, 2, 3, 4]
def test5_offset : Int := 0
def test5_Expected : Array Int := #[1, 2, 3, 4]

-- Test case 6: offset equal to size -> unchanged

def test6_a : Array Int := #[1, 2, 3, 4]
def test6_offset : Int := 4
def test6_Expected : Array Int := #[1, 2, 3, 4]

-- Test case 7: offset larger than size -> wraps (offset 5 on size 4 equals offset 1)
-- [1,2,3,4] -> [2,3,4,1]

def test7_a : Array Int := #[1, 2, 3, 4]
def test7_offset : Int := 5
def test7_Expected : Array Int := #[2, 3, 4, 1]

-- Test case 8: contains negative and repeated elements, offset 3
-- [0,-1,-1,2] -> [2,0,-1,-1]

def test8_a : Array Int := #[0, -1, -1, 2]
def test8_offset : Int := 3
def test8_Expected : Array Int := #[2, 0, -1, -1]
end TestCases
