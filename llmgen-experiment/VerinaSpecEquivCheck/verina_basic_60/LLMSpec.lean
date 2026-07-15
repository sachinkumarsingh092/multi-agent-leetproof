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
    FilterEvenArray: produce a new array containing exactly the even integers from an input array, preserving order.

    Natural language breakdown:
    1. Input is an array of integers `arr`.
    2. An integer is even iff it is divisible by 2.
    3. The output `result` must contain only even integers.
    4. Every even element occurring in `arr` must occur in `result` the same number of times (preserve multiplicity).
    5. No odd element from `arr` may appear in `result`.
    6. The relative order of the selected elements must be the same as in `arr` (stable filtering).
    7. There are no additional preconditions; all input arrays are valid.
-/

section Specs
-- Helper predicate: evenness as a Prop (Mathlib's `Even`).
def isEven (x : Int) : Prop := Even x

-- Helper predicate: evenness as a Bool (useful for `countP`).
def isEvenB (x : Int) : Bool := (x % 2) == 0

-- Order preservation expressed via an increasing index mapping from `result` indices to `arr` indices.
def orderPreserved (arr : Array Int) (result : Array Int) : Prop :=
  ∃ f : Nat → Nat,
    (∀ (i : Nat), i < result.size →
      f i < arr.size ∧ arr[f i]! = result[i]!) ∧
    (∀ (i : Nat) (j : Nat), i < j → j < result.size → f i < f j)

-- No additional preconditions.
def precondition (arr : Array Int) : Prop :=
  True

def postcondition (arr : Array Int) (result : Array Int) : Prop :=
  -- All outputs are even
  (∀ (i : Nat), i < result.size → isEven (result[i]!)) ∧
  -- Exact multiplicity of each value: even values are kept, odd values are removed
  (∀ (x : Int), (isEven x → result.count x = arr.count x) ∧ (¬ isEven x → result.count x = 0)) ∧
  -- Order is preserved relative to the input
  orderPreserved arr result ∧
  -- Size matches the number of even elements in the input
  (result.size = arr.countP isEvenB)
end Specs

section Impl
method FilterEvenArray (arr : Array Int)
  return (result : Array Int)
  require precondition arr
  ensures postcondition arr result
  do
  pure (#[])

end Impl

section TestCases
-- Test case 1: empty input
-- Expected: empty output

def test1_arr : Array Int := #[]
def test1_Expected : Array Int := #[]

-- Test case 2: all odd

def test2_arr : Array Int := #[1, 3, 5, 7]
def test2_Expected : Array Int := #[]

-- Test case 3: all even

def test3_arr : Array Int := #[2, 4, 6, 8]
def test3_Expected : Array Int := #[2, 4, 6, 8]

-- Test case 4: mixed with 0 and 1 (boundary naturals embedded as Int)

def test4_arr : Array Int := #[0, 1, 2, 3, 4, 5]
def test4_Expected : Array Int := #[0, 2, 4]

-- Test case 5: negatives and positives

def test5_arr : Array Int := #[-3, -2, -1, 0, 1, 2]
def test5_Expected : Array Int := #[-2, 0, 2]

-- Test case 6: duplicates of even and odd values

def test6_arr : Array Int := #[2, 2, 3, 2, 3, 4, 4, 5]
def test6_Expected : Array Int := #[2, 2, 2, 4, 4]

-- Test case 7: single element (odd)

def test7_arr : Array Int := #[1]
def test7_Expected : Array Int := #[]

-- Test case 8: single element (even)

def test8_arr : Array Int := #[2]
def test8_Expected : Array Int := #[2]

-- Test case 9: alternating pattern, ensuring stability of order

def test9_arr : Array Int := #[1, 2, 1, 4, 3, 6, 5, 8]
def test9_Expected : Array Int := #[2, 4, 6, 8]
end TestCases
