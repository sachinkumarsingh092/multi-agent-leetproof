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
    ProductOfArrayExceptSelf: for each index i, return the product of all input elements except the one at i.
    **Important: complexity should be O(n) time and O(n) space**
    Natural language breakdown:
    1. Input is an array of integers `nums`.
    2. Output is an array `answer` of the same length as `nums`.
    3. For every valid index i, `answer[i]` equals the product of all `nums[j]` with j ≠ i.
    4. The relative order of indices is preserved: output position i corresponds to input position i.
    5. Multiplication uses the integer multiplicative identity 1 for the excluded element.
    6. Edge cases:
       - If the array is empty, the output is empty.
       - If the array has one element, the only output value is 1 (product over an empty set).
       - Zeros and negative values must be handled correctly.
    7. The problem statement guarantees that any prefix or suffix product fits in a 32-bit signed integer; we capture this as an input precondition.
    8. The algorithmic requirement “no division” is an implementation constraint; the mathematical result is uniquely determined by the product definition.
-/

section Specs
-- Signed 32-bit integer bounds expressed as Int.
def int32Min : Int := (-2147483648)
def int32Max : Int := (2147483647)

def InInt32 (z : Int) : Prop := int32Min ≤ z ∧ z ≤ int32Max

-- Product of the first k elements (a prefix), where k is intended to satisfy k ≤ nums.size.
def prefixProd (nums : Array Int) (k : Nat) : Int :=
  (Finset.range k).prod (fun (j : Nat) => nums[j]!)

-- Product of the suffix starting at index k, where k is intended to satisfy k ≤ nums.size.
def suffixProd (nums : Array Int) (k : Nat) : Int :=
  (Finset.range (nums.size - k)).prod (fun (t : Nat) => nums[k + t]!)

-- Product of all elements except the element at index i.
def prodExcept (nums : Array Int) (i : Nat) : Int :=
  (Finset.range nums.size).prod (fun (j : Nat) => if j = i then (1 : Int) else nums[j]!)

-- Preconditions
-- We encode the stated 32-bit safety guarantee for any prefix and suffix product.
def precondition (nums : Array Int) : Prop :=
  (∀ (k : Nat), k ≤ nums.size → InInt32 (prefixProd nums k)) ∧
  (∀ (k : Nat), k ≤ nums.size → InInt32 (suffixProd nums k))

-- Postconditions
-- 1) Output length matches input length.
-- 2) For each valid index i, result[i] is the product of all input elements except nums[i].
def postcondition (nums : Array Int) (answer : Array Int) : Prop :=
  answer.size = nums.size ∧
  (∀ (i : Nat), i < nums.size → answer[i]! = prodExcept nums i)
end Specs

section Impl
method ProductOfArrayExceptSelf (nums : Array Int)
  return (answer : Array Int)
  require precondition nums
  ensures postcondition nums answer
  do
  pure (#[] : Array Int)  -- placeholder body only

end Impl

section TestCases
-- Test case 1: Example 1
def test1_nums : Array Int := #[1, 2, 3, 4]
def test1_Expected : Array Int := #[24, 12, 8, 6]

-- Test case 2: Example 2
def test2_nums : Array Int := #[-1, 1, 0, -3, 3]
def test2_Expected : Array Int := #[0, 0, 9, 0, 0]

-- Test case 3: Empty array
def test3_nums : Array Int := (#[] : Array Int)
def test3_Expected : Array Int := (#[] : Array Int)

-- Test case 4: Singleton array
def test4_nums : Array Int := #[7]
def test4_Expected : Array Int := #[1]

-- Test case 5: Two elements
def test5_nums : Array Int := #[5, 6]
def test5_Expected : Array Int := #[6, 5]

-- Test case 6: Contains exactly one zero
def test6_nums : Array Int := #[0, 2, 3, 4]
def test6_Expected : Array Int := #[24, 0, 0, 0]

-- Test case 7: Contains two zeros
def test7_nums : Array Int := #[0, 2, 0, 4]
def test7_Expected : Array Int := #[0, 0, 0, 0]

-- Test case 8: All negative values
def test8_nums : Array Int := #[-1, -2, -3]
def test8_Expected : Array Int := #[6, 3, 2]

-- Test case 9: Mixed signs, no zeros
def test9_nums : Array Int := #[-2, 3, -4, 5]
def test9_Expected : Array Int := #[-60, 40, -30, 24]
end TestCases
