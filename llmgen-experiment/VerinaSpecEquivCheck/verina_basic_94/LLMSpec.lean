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
    CopyArray: Produce a new array that has the same size and identical elements in the same order as the input.
    Natural language breakdown:
    1. The input is an array of integers `s`.
    2. The output is an array of integers `result`.
    3. The output array must have the same size as the input array.
    4. For every valid index `i` in the input array, the output element at `i` equals the input element at `i`.
    5. The input may be empty or non-empty; there are no restrictions.
-/

section Specs
def precondition (s : Array Int) : Prop :=
  True

def postcondition (s : Array Int) (result : Array Int) : Prop :=
  result.size = s.size ∧
  (∀ (i : Nat), i < s.size → result[i]! = s[i]!)
end Specs

section Impl
method CopyArray (s : Array Int)
  return (result : Array Int)
  require precondition s
  ensures postcondition s result
  do
  pure s  -- placeholder body

end Impl

section TestCases
-- Test case 1: empty array
def test1_s : Array Int := #[]
def test1_Expected : Array Int := #[]

-- Test case 2: singleton array (edge case)
def test2_s : Array Int := #[42]
def test2_Expected : Array Int := #[42]

-- Test case 3: contains zero (edge case)
def test3_s : Array Int := #[0]
def test3_Expected : Array Int := #[0]

-- Test case 4: mixed positive/negative values
def test4_s : Array Int := #[-3, 1, -2, 5]
def test4_Expected : Array Int := #[-3, 1, -2, 5]

-- Test case 5: repeated values
def test5_s : Array Int := #[7, 7, 7]
def test5_Expected : Array Int := #[7, 7, 7]

-- Test case 6: longer typical array
def test6_s : Array Int := #[10, 20, 30, 40, 50]
def test6_Expected : Array Int := #[10, 20, 30, 40, 50]

-- Test case 7: includes both Int.min-like magnitude and Int.max-like magnitude within Int range
-- (Lean Int literals are unbounded in syntax, but represent mathematical integers)
def test7_s : Array Int := #[-2147483648, 2147483647]
def test7_Expected : Array Int := #[-2147483648, 2147483647]

-- Test case 8: alternating signs and zeros
def test8_s : Array Int := #[0, -1, 0, 1, 0, -1]
def test8_Expected : Array Int := #[0, -1, 0, 1, 0, -1]
end TestCases
