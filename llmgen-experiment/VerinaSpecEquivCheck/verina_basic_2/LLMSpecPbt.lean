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
    ArrayMinOption: find the smallest number in an array of (nonnegative) integers.

    The problem statement mentions integers, but the required specification type is:
    (s : Array Nat) (result : Option Nat).

    Natural language breakdown:
    1. The input is an array s of natural numbers.
    2. If s is empty, the function returns none.
    3. If s is nonempty, the function returns some m where m is an element of s.
    4. For a nonempty s, the returned m is less than or equal to every element of s.
    5. Because Nat has a total order, this uniquely characterizes the minimum value of s.
-/

section Specs
def precondition (s : Array Nat) : Prop :=
  True

def postcondition (s : Array Nat) (result : Option Nat) : Prop :=
  match result with
  | none => s.size = 0
  | some m =>
      s.size > 0 ∧ m ∈ s ∧ ∀ x : Nat, x ∈ s → m ≤ x
end Specs

section Impl
method ArrayMinOption (s : Array Nat)
  return (result : Option Nat)
  require precondition s
  ensures postcondition s result
  do
  pure none  -- placeholder body

prove_correct ArrayMinOption by sorry
end Impl

section TestCases
-- Test case 1: empty array
def test1_s : Array Nat := #[]
def test1_Expected : Option Nat := none

-- Test case 2: singleton array containing 0 (edge case)
def test2_s : Array Nat := #[0]
def test2_Expected : Option Nat := some 0

-- Test case 3: singleton array containing a nonzero value
def test3_s : Array Nat := #[5]
def test3_Expected : Option Nat := some 5

-- Test case 4: strictly increasing
def test4_s : Array Nat := #[1, 2, 3, 4]
def test4_Expected : Option Nat := some 1

-- Test case 5: strictly decreasing
def test5_s : Array Nat := #[9, 7, 5, 3]
def test5_Expected : Option Nat := some 3

-- Test case 6: includes duplicates of the minimum
def test6_s : Array Nat := #[2, 1, 3, 1, 4]
def test6_Expected : Option Nat := some 1

-- Test case 7: all elements equal
def test7_s : Array Nat := #[6, 6, 6]
def test7_Expected : Option Nat := some 6

-- Test case 8: minimum appears at the end and is 0
def test8_s : Array Nat := #[10, 8, 7, 0]
def test8_Expected : Option Nat := some 0

-- Test case 9: larger values
def test9_s : Array Nat := #[100000, 99999, 100001]
def test9_Expected : Option Nat := some 99999
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test9' (result : Option Nat) :
  result ≠ test9_Expected →
  ¬ postcondition test9_s result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test9_Expected]) (config := { numInst := 100000 })
