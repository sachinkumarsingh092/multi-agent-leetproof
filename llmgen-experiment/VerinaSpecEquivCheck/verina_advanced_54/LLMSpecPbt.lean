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
    MissingNumber: Find the unique missing natural number from the range 0..n given a list of length n.
    Natural language breakdown:
    1. The input is a list `nums : List Nat`.
    2. Let n = nums.length. The intended full set of values is all natural numbers in the inclusive range [0, n].
    3. The list contains exactly n distinct numbers, each within [0, n].
    4. Exactly one number from [0, n] is missing from the list.
    5. The function returns that missing number.
    6. The returned number must be within [0, n].
    7. The returned number must not appear in the list.
    8. Any number within [0, n] that does not appear in the list must equal the returned number (uniqueness).
-/

section Specs
-- Helper: predicate stating a Nat is within the expected inclusive range [0, nums.length].
-- Note: lower bound 0 is automatic for Nat.
def inRange0n (nums : List Nat) (x : Nat) : Prop :=
  x ≤ nums.length

-- Preconditions:
-- - no duplicates
-- - all elements are within [0, n]
-- - there exists a missing number in [0, n]
-- - the missing number is unique

def precondition (nums : List Nat) : Prop :=
  nums.Nodup ∧
  (∀ (x : Nat), x ∈ nums → inRange0n nums x) ∧
  (∃ (m : Nat), inRange0n nums m ∧ m ∉ nums) ∧
  (∀ (m1 : Nat) (m2 : Nat),
    inRange0n nums m1 → inRange0n nums m2 → m1 ∉ nums → m2 ∉ nums → m1 = m2)

-- Postconditions:
-- - result is within [0, n]
-- - result is not present in the list
-- - result is the unique missing number in [0, n]

def postcondition (nums : List Nat) (result : Nat) : Prop :=
  inRange0n nums result ∧
  result ∉ nums ∧
  (∀ (x : Nat), inRange0n nums x → x ∉ nums → x = result)
end Specs

section Impl
method MissingNumber (nums : List Nat)
  return (result : Nat)
  require precondition nums
  ensures postcondition nums result
  do
  pure 0

prove_correct MissingNumber by sorry
end Impl

section TestCases
-- Test case 1: example-style case (common in missing number problems)
-- nums = [3,0,1] has n = 3 and missing number 2.
def test1_nums : List Nat := [3, 0, 1]
def test1_Expected : Nat := 2

-- Test case 2: empty list (n = 0), range is [0,0], missing is 0.
def test2_nums : List Nat := []
def test2_Expected : Nat := 0

-- Test case 3: singleton list containing 0 (n = 1), missing is 1.
def test3_nums : List Nat := [0]
def test3_Expected : Nat := 1

-- Test case 4: singleton list containing 1 (n = 1), missing is 0.
def test4_nums : List Nat := [1]
def test4_Expected : Nat := 0

-- Test case 5: missing at the end of the range
-- n = 3, nums has {0,1,2}, missing is 3.
def test5_nums : List Nat := [0, 1, 2]
def test5_Expected : Nat := 3

-- Test case 6: missing at the beginning of the range
-- n = 3, nums has {1,2,3}, missing is 0.
def test6_nums : List Nat := [1, 2, 3]
def test6_Expected : Nat := 0

-- Test case 7: typical mid-range missing
-- n = 5, missing is 4.
def test7_nums : List Nat := [0, 1, 2, 3, 5]
def test7_Expected : Nat := 4

-- Test case 8: unsorted input, missing in the middle
-- n = 4, missing is 2.
def test8_nums : List Nat := [4, 1, 3, 0]
def test8_Expected : Nat := 2

-- Test case 9: larger n with a missing interior value
-- n = 8, missing is 6.
def test9_nums : List Nat := [0, 1, 2, 3, 4, 5, 7, 8]
def test9_Expected : Nat := 6
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test9' (result : Nat) :
  result ≠ test9_Expected →
  ¬ postcondition test9_nums result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test9_Expected]) (config := { numInst := 100000 })
