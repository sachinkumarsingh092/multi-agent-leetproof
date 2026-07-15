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
    LongestConsecutiveSequenceLength: find the length of the longest streak of consecutive integers present in a list.

    Natural language breakdown:
    1. Input is a list of integers `nums`.
    2. The integers are unique (no duplicates).
    3. A consecutive sequence is a set of integers that can be arranged as a contiguous interval with step 1 and no gaps.
    4. Order in the input list does not matter; only membership matters.
    5. The output is a natural number equal to the maximum length among all consecutive integer intervals fully contained in `nums`.
    6. If the input list is empty, the longest consecutive sequence length is 0.
    7. If the input list is nonempty, the result is at least 1 and at most `nums.length`.
-/

section Specs
-- An interval [a,b] is fully contained in nums if every integer k with a ≤ k ≤ b appears in nums.
-- We include the side condition a ≤ b to avoid degenerate "backwards" intervals.
def intervalContained (nums : List Int) (a : Int) (b : Int) : Prop :=
  a ≤ b ∧ ∀ (k : Int), a ≤ k ∧ k ≤ b → k ∈ nums

-- The length of an integer interval [a,b] as a natural number.
-- This is only meaningful when a ≤ b; the definition uses Int.toNat, so we pair it with a ≤ b in specs.
def intervalLength (a : Int) (b : Int) : Nat :=
  Int.toNat (b - a + 1)

def precondition (nums : List Int) : Prop :=
  nums.Nodup

def postcondition (nums : List Int) (result : Nat) : Prop :=
  (nums = [] → result = 0) ∧
  (nums ≠ [] →
    (∃ (a : Int) (b : Int),
      intervalContained nums a b ∧
      result = intervalLength a b) ∧
    (∀ (a : Int) (b : Int),
      intervalContained nums a b → intervalLength a b ≤ result) ∧
    (1 ≤ result) ∧
    (result ≤ nums.length))
end Specs

section Impl
method LongestConsecutiveSequenceLength (nums : List Int)
  return (result : Nat)
  require precondition nums
  ensures postcondition nums result
  do
  pure 0

prove_correct LongestConsecutiveSequenceLength by sorry
end Impl

section TestCases
-- Test case 1: typical unordered input with a longest streak of length 4
-- Longest consecutive sequence is {1,2,3,4}
def test1_nums : List Int := [100, 4, 200, 1, 3, 2]
def test1_Expected : Nat := 4

-- Test case 2: empty list

def test2_nums : List Int := []
def test2_Expected : Nat := 0

-- Test case 3: singleton list

def test3_nums : List Int := [5]
def test3_Expected : Nat := 1

-- Test case 4: two elements not consecutive

def test4_nums : List Int := [1, 3]
def test4_Expected : Nat := 1

-- Test case 5: already consecutive but in reverse order

def test5_nums : List Int := [2, 1, 0]
def test5_Expected : Nat := 3

-- Test case 6: includes negative numbers; longest is [-1,0,1,2]

def test6_nums : List Int := [-1, 2, 0, 1]
def test6_Expected : Nat := 4

-- Test case 7: multiple streaks; longest is [5,6,7]

def test7_nums : List Int := [10, 5, 6, 7, 30]
def test7_Expected : Nat := 3

-- Test case 8: sparse input; longest streak length 2 ([0,1] or [10,11])

def test8_nums : List Int := [0, 1, 10, 11, 20]
def test8_Expected : Nat := 2

-- Test case 9: large consecutive run with additional outlier

def test9_nums : List Int := [50, 47, 48, 49, 46, 100]
def test9_Expected : Nat := 5
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test3' (result : Nat) :
  result ≠ test3_Expected →
  ¬ postcondition test3_nums result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test3_Expected]) (config := { numInst := 100000 })
