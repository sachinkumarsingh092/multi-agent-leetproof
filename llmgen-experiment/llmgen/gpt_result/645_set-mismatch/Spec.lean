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
    645. Set Mismatch: identify the duplicated number and the missing number in an array that should represent {1..n}.
    **Important: complexity should be O(n ^ 2) time and O(n) space**
    Natural language breakdown:
    1. The input is an array `nums` of length `n`.
    2. The intended correct set of values is exactly the integers from 1 to n (each appearing once).
    3. Due to an error, exactly one value in 1..n appears twice in `nums` (the duplicated value).
    4. As a consequence, exactly one value in 1..n appears zero times in `nums` (the missing value).
    5. Every element of `nums` is in the range 1..n.
    6. The output is an array of length 2: [duplicated, missing].
    7. The duplicated value must occur exactly twice in `nums`.
    8. The missing value must occur exactly zero times in `nums`.
    9. Every other value in 1..n must occur exactly once in `nums`.
-/

section Specs
-- Helper: membership in the intended domain {1,2,...,n}
def inOneToN (n : Nat) (x : Nat) : Prop :=
  1 ≤ x ∧ x ≤ n

-- Helper: the core characterization of a valid set-mismatch instance
-- (there exists exactly one duplicated value and one missing value).
def hasSetMismatch (nums : Array Nat) : Prop :=
  let n : Nat := nums.size
  (n > 0) ∧
  (∀ (i : Nat), i < n → inOneToN n nums[i]!) ∧
  (∃ (dup : Nat) (miss : Nat),
      dup ≠ miss ∧
      inOneToN n dup ∧
      inOneToN n miss ∧
      nums.count dup = 2 ∧
      nums.count miss = 0 ∧
      (∀ (x : Nat), inOneToN n x → x ≠ dup → x ≠ miss → nums.count x = 1))

-- Preconditions
-- We require exactly the set-mismatch structure described above.
def precondition (nums : Array Nat) : Prop :=
  hasSetMismatch nums

-- Postconditions
-- The result is an array [dup, miss] that matches the unique count-pattern.
def postcondition (nums : Array Nat) (result : Array Nat) : Prop :=
  let n : Nat := nums.size
  result.size = 2 ∧
  let dup : Nat := result[0]!
  let miss : Nat := result[1]!
  dup ≠ miss ∧
  inOneToN n dup ∧
  inOneToN n miss ∧
  nums.count dup = 2 ∧
  nums.count miss = 0 ∧
  (∀ (x : Nat), inOneToN n x → x ≠ dup → x ≠ miss → nums.count x = 1)
end Specs

section Impl
method SetMismatch (nums : Array Nat)
  return (result : Array Nat)
  require precondition nums
  ensures postcondition nums result
  do
  pure (#[] : Array Nat)  -- placeholder body

end Impl

section TestCases
-- Test case 1: Example 1
def test1_nums : Array Nat := #[1, 2, 2, 4]
def test1_Expected : Array Nat := #[2, 3]

-- Test case 2: Example 2
def test2_nums : Array Nat := #[1, 1]
def test2_Expected : Array Nat := #[1, 2]

-- Test case 3: duplicate is the maximum, missing is the minimum
def test3_nums : Array Nat := #[2, 2]
def test3_Expected : Array Nat := #[2, 1]

-- Test case 4: n = 3, missing is the maximum
def test4_nums : Array Nat := #[1, 2, 2]
def test4_Expected : Array Nat := #[2, 3]

-- Test case 5: n = 3, duplicate appears at both ends
def test5_nums : Array Nat := #[3, 1, 3]
def test5_Expected : Array Nat := #[3, 2]

-- Test case 6: n = 4, duplicate in the middle, missing at the end
def test6_nums : Array Nat := #[1, 2, 3, 3]
def test6_Expected : Array Nat := #[3, 4]

-- Test case 7: n = 5, unsorted, duplicate is small, missing is maximum
def test7_nums : Array Nat := #[2, 1, 1, 4, 3]
def test7_Expected : Array Nat := #[1, 5]

-- Test case 8: n = 6, duplicate is interior, missing is interior
def test8_nums : Array Nat := #[1, 5, 3, 4, 2, 2]
def test8_Expected : Array Nat := #[2, 6]

-- Test case 9: n = 7, larger case, duplicate is maximum, missing is interior
def test9_nums : Array Nat := #[1, 2, 3, 4, 5, 7, 7]
def test9_Expected : Array Nat := #[7, 6]
end TestCases
