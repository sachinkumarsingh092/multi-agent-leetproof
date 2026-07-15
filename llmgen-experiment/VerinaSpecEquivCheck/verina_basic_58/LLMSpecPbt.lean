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
    DoubleArrayElements: transform an array of integers by doubling each element.
    Natural language breakdown:
    1. The input is an array `s` of integers.
    2. The output is an array `result` of integers.
    3. The output array has the same size as the input array.
    4. For every valid index `i` (i < s.size), `result[i]` equals `2 * s[i]`.
    5. The input array is assumed valid, and doubling does not overflow.
-/

section Specs
-- No additional helper definitions are required.

def precondition (s : Array Int) : Prop :=
  True

def postcondition (s : Array Int) (result : Array Int) : Prop :=
  result.size = s.size ∧
  ∀ (i : Nat), i < s.size → result[i]! = (2 : Int) * s[i]!
end Specs

section Impl
method DoubleArrayElements (s : Array Int)
  return (result : Array Int)
  require precondition s
  ensures postcondition s result
  do
    pure #[]  -- placeholder body

prove_correct DoubleArrayElements by sorry
end Impl

section TestCases
-- Test case 1: empty array
def test1_s : Array Int := #[]
def test1_Expected : Array Int := #[]

-- Test case 2: singleton zero
def test2_s : Array Int := #[0]
def test2_Expected : Array Int := #[0]

-- Test case 3: singleton positive
def test3_s : Array Int := #[7]
def test3_Expected : Array Int := #[14]

-- Test case 4: singleton negative
def test4_s : Array Int := #[-3]
def test4_Expected : Array Int := #[-6]

-- Test case 5: mixed small values
def test5_s : Array Int := #[1, -2, 3, 0]
def test5_Expected : Array Int := #[2, -4, 6, 0]

-- Test case 6: includes Int boundaries near typical 32-bit range (still safe in Lean Int)
def test6_s : Array Int := #[2147483647, -2147483648]
def test6_Expected : Array Int := #[4294967294, -4294967296]

-- Test case 7: repeated values
def test7_s : Array Int := #[5, 5, 5]
def test7_Expected : Array Int := #[10, 10, 10]

-- Test case 8: longer array
def test8_s : Array Int := #[10, 20, 30, 40, 50]
def test8_Expected : Array Int := #[20, 40, 60, 80, 100]
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test8' (result : Array Int) :
  result ≠ test8_Expected →
  ¬ postcondition test8_s result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test8_Expected]) (config := { numInst := 100000 })
