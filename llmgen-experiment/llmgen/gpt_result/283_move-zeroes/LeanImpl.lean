import Lean
import Mathlib.Tactic
import Velvet.Std

set_option maxHeartbeats 10000000

section Specs
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false

/- Problem Description
    MoveZeroes: Move all 0 values to the end of an integer array while preserving the relative order of non-zero elements.
    Natural language breakdown:
    1. Input is an array of integers.
    2. The output is an array of integers with the same length as the input.
    3. The output contains exactly the same multiset of values as the input (no values are lost or created).
    4. All non-zero elements appear before all zero elements in the output (zeros form a suffix).
    5. The relative order of the non-zero elements is preserved: scanning left-to-right, the sequence of non-zero values
       in the output is exactly the sequence of non-zero values in the input.
    Your algorithm should run in **O(n)** time and **O(1)** extra space (in-place).
-/

-- Helper: count occurrences of a value in an array.
-- (Computable; used to express multiset preservation without defining a concrete implementation of MoveZeroes.)
def countVal (arr : Array Int) (v : Int) : Nat :=
  arr.foldl (fun (acc : Nat) (x : Int) => if x = v then acc + 1 else acc) 0

-- Helper: output has all zeros grouped at the end.
-- If a position is zero, everything to its right is also zero.
def zerosFormSuffix (output : Array Int) : Prop :=
  ∀ (k : Nat),
    k < output.size →
    output[k]! = 0 →
    ∀ (j : Nat), k < j → j < output.size → output[j]! = 0

-- Helper: a nonzero index predicate (kept small and decidable-looking).
def isNonZeroIndex (a : Array Int) (i : Nat) : Prop :=
  i < a.size ∧ a[i]! ≠ 0

-- Helper: the output nonzero prefix corresponds exactly to the input nonzero elements in order.
-- We use a strictly-increasing mapping f from input indices (where input[i] != 0) to output indices.
-- This expresses stability without giving an algorithm.
def preservesNonZeroOrder (input : Array Int) (output : Array Int) : Prop :=
  ∃ (f : Nat → Nat),
    (∀ (i : Nat), isNonZeroIndex input i → f i < output.size ∧ output[(f i)]! = input[i]!) ∧
    (∀ (i : Nat) (j : Nat), i < j → isNonZeroIndex input i → isNonZeroIndex input j → f i < f j) ∧
    (∀ (p : Nat), p < output.size → output[p]! ≠ 0 → ∃ (i : Nat), isNonZeroIndex input i ∧ f i = p)

-- Preconditions: none (any array is valid).
def precondition (nums : Array Int) : Prop :=
  True

-- Postcondition:
-- 1) same size
-- 2) same multiset of values (via per-value counts)
-- 3) zeros form a suffix
-- 4) stable preservation of the entire nonzero subsequence (via an order-isomorphism style mapping)
def postcondition (nums : Array Int) (result : Array Int) : Prop :=
  result.size = nums.size ∧
  (∀ (v : Int), countVal nums v = countVal result v) ∧
  zerosFormSuffix result ∧
  preservesNonZeroOrder nums result
end Specs

section Impl
def implementation (nums : Array Int) : Array Int :=
  -- In-place style (O(1) extra space in an imperative setting):
  -- scan left-to-right, writing nonzeros to the next write position;
  -- then fill the remaining suffix with zeros.
  let n := nums.size
  let step (st : Nat × Array Int) (x : Int) : Nat × Array Int :=
    let (w, a) := st
    if x = 0 then
      (w, a)
    else
      -- write x at position w (which is always < n)
      (w + 1, a.set! w x)
  let (w, a1) := nums.foldl step (0, nums)
  let rec fillZeros (a : Array Int) (i : Nat) : Array Int :=
    if h : i < n then
      fillZeros (a.set! i 0) (i + 1)
    else
      a
  termination_by n - i
  fillZeros a1 w
end Impl

section TestCases
-- Test case 1: Example 1
-- Input: [0,1,0,3,12]
-- Output: [1,3,12,0,0]
def test1_nums : Array Int := #[0, 1, 0, 3, 12]
def test1_Expected : Array Int := #[1, 3, 12, 0, 0]

-- Test case 2: Example 2
-- Input: [0]
-- Output: [0]
def test2_nums : Array Int := #[0]
def test2_Expected : Array Int := #[0]

-- Test case 3: Empty array
-- Input: []
-- Output: []
def test3_nums : Array Int := #[]
def test3_Expected : Array Int := #[]

-- Test case 4: No zeros
-- Input: [1,2,3]
-- Output: [1,2,3]
def test4_nums : Array Int := #[1, 2, 3]
def test4_Expected : Array Int := #[1, 2, 3]

-- Test case 5: All zeros
-- Input: [0,0,0]
-- Output: [0,0,0]
def test5_nums : Array Int := #[0, 0, 0]
def test5_Expected : Array Int := #[0, 0, 0]

-- Test case 6: Zeros already at end
-- Input: [5,0,0]
-- Output: [5,0,0]
def test6_nums : Array Int := #[5, 0, 0]
def test6_Expected : Array Int := #[5, 0, 0]

-- Test case 7: Alternating including negatives
-- Input: [0,-1,0,-2,3]
-- Output: [-1,-2,3,0,0]
def test7_nums : Array Int := #[0, -1, 0, -2, 3]
def test7_Expected : Array Int := #[-1, -2, 3, 0, 0]

-- Test case 8: Duplicates of non-zero values and multiple zeros
-- Input: [1,0,1,0,1]
-- Output: [1,1,1,0,0]
def test8_nums : Array Int := #[1, 0, 1, 0, 1]
def test8_Expected : Array Int := #[1, 1, 1, 0, 0]

-- Test case 9: Mix with repeated negatives and zeros
-- Input: [-1,0,-1,2,0]
-- Output: [-1,-1,2,0,0]
def test9_nums : Array Int := #[-1, 0, -1, 2, 0]
def test9_Expected : Array Int := #[-1, -1, 2, 0, 0]

-- Recommend to validate: MoveZeroes, precondition, postcondition
end TestCases

section Assertions
-- Test case 1
#assert_same_evaluation #[(implementation test1_nums), test1_Expected]

-- Test case 2
#assert_same_evaluation #[(implementation test2_nums), test2_Expected]

-- Test case 3
#assert_same_evaluation #[(implementation test3_nums), test3_Expected]

-- Test case 4
#assert_same_evaluation #[(implementation test4_nums), test4_Expected]

-- Test case 5
#assert_same_evaluation #[(implementation test5_nums), test5_Expected]

-- Test case 6
#assert_same_evaluation #[(implementation test6_nums), test6_Expected]

-- Test case 7
#assert_same_evaluation #[(implementation test7_nums), test7_Expected]

-- Test case 8
#assert_same_evaluation #[(implementation test8_nums), test8_Expected]

-- Test case 9
#assert_same_evaluation #[(implementation test9_nums), test9_Expected]
end Assertions

section Proof
theorem correctness_goal
    (nums : Array Int)
    (h_precond : precondition nums)
    : postcondition nums (implementation (nums)) := by
    sorry
end Proof
