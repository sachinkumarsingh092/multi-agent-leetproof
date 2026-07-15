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
    GreaterThanAll: Determine if an integer is strictly greater than every element in an array.
    Natural language breakdown:
    1. Inputs are an integer n and an array a of integers.
    2. The output is a Boolean.
    3. The output is true exactly when n is strictly greater than every element of a.
    4. Equivalently, for every valid index i in the array, we have a[i] < n.
    5. If the array is empty, the condition holds vacuously and the result is true.
    6. The array is assumed non-null; in Lean/Velvet, Array values are always well-defined.
-/

section Specs
-- Helper predicate: n is strictly greater than all elements of a.
def GreaterThanAllProp (n : Int) (a : Array Int) : Prop :=
  ∀ (i : Nat), i < a.size → a[i]! < n

def precondition (n : Int) (a : Array Int) : Prop :=
  True

def postcondition (n : Int) (a : Array Int) (result : Bool) : Prop :=
  (result = true ↔ GreaterThanAllProp n a)
end Specs

section Impl
method GreaterThanAll (n : Int) (a : Array Int)
  return (result : Bool)
  require precondition n a
  ensures postcondition n a result
  do
  pure true  -- placeholder

prove_correct GreaterThanAll by sorry
end Impl

section TestCases
-- Test case 1: typical case where n is greater than all elements
-- a = [1,2,3], n = 4 => true

def test1_n : Int := 4

def test1_a : Array Int := #[1, 2, 3]

def test1_Expected : Bool := true

-- Test case 2: n equals an element => false (needs strictly greater)

def test2_n : Int := 3

def test2_a : Array Int := #[1, 2, 3]

def test2_Expected : Bool := false

-- Test case 3: n is less than some element => false

def test3_n : Int := 2

def test3_a : Array Int := #[1, 5, 2]

def test3_Expected : Bool := false

-- Test case 4: empty array => true (vacuous)

def test4_n : Int := 0

def test4_a : Array Int := #[]

def test4_Expected : Bool := true

-- Test case 5: singleton array, n greater => true

def test5_n : Int := 1

def test5_a : Array Int := #[0]

def test5_Expected : Bool := true

-- Test case 6: singleton array, n not greater (equal) => false

def test6_n : Int := 1

def test6_a : Array Int := #[1]

def test6_Expected : Bool := false

-- Test case 7: negative numbers, n greater than all negatives => true

def test7_n : Int := -1

def test7_a : Array Int := #[-5, -3, -2]

def test7_Expected : Bool := true

-- Test case 8: negative n, array contains equal/greater element => false

def test8_n : Int := -3

def test8_a : Array Int := #[-4, -3, -10]

def test8_Expected : Bool := false

-- Test case 9: larger array with mixed values, n greater than max => true

def test9_n : Int := 100

def test9_a : Array Int := #[0, 1, 2, 50, -7, 99]

def test9_Expected : Bool := true
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test9' (result : Bool) :
  result ≠ test9_Expected →
  ¬ postcondition test9_n test9_a result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test9_Expected]) (config := { numInst := 100000 })
