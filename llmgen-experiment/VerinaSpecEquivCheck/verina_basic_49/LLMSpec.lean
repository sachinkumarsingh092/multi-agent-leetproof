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
    FindFirstOddIndex: Search an array of integers for the first odd number.
    Natural language breakdown:
    1. Input is an array `a` of integers.
    2. An element `x` is considered odd exactly when `x % 2 ≠ 0`.
    3. If there is no index `i` with `i < a.size` such that `a[i]` is odd, the result is `none`.
    4. If there exists at least one odd element, the result is `some k` where:
       a) `k < a.size`.
       b) `a[k]` is odd.
       c) `k` is the smallest index with an odd element, i.e. all earlier indices are not odd.
    5. Edge cases:
       a) Empty array: result is `none`.
       b) Arrays with all even numbers: result is `none`.
       c) Arrays with multiple odd numbers: return the smallest odd index.
-/

section Specs
-- Helper: oddness predicate for Int (avoids relying on `Int.Odd`, which may not be available)
def isOddInt (x : Int) : Prop := x % 2 ≠ 0

def precondition (a : Array Int) : Prop :=
  True

def postcondition (a : Array Int) (result : Option Nat) : Prop :=
  match result with
  | none =>
      ∀ (i : Nat), i < a.size → ¬ isOddInt (a[i]!)
  | some k =>
      k < a.size ∧
      isOddInt (a[k]!) ∧
      ∀ (j : Nat), j < k → ¬ isOddInt (a[j]!)
end Specs

section Impl
method FindFirstOddIndex (a : Array Int)
  return (result : Option Nat)
  require precondition a
  ensures postcondition a result
  do
  pure none  -- placeholder

end Impl

section TestCases
-- Test case 1: empty array (edge case)
def test1_a : Array Int := #[]
def test1_Expected : Option Nat := none

-- Test case 2: singleton even
def test2_a : Array Int := #[2]
def test2_Expected : Option Nat := none

-- Test case 3: singleton odd
def test3_a : Array Int := #[3]
def test3_Expected : Option Nat := some 0

-- Test case 4: first element odd
def test4_a : Array Int := #[5, 2, 4]
def test4_Expected : Option Nat := some 0

-- Test case 5: odd appears in the middle
def test5_a : Array Int := #[2, 4, 7, 8]
def test5_Expected : Option Nat := some 2

-- Test case 6: multiple odds, should pick the first occurrence
def test6_a : Array Int := #[2, 9, 11, 14]
def test6_Expected : Option Nat := some 1

-- Test case 7: all even, includes zero
def test7_a : Array Int := #[0, 6, 10, 12]
def test7_Expected : Option Nat := none

-- Test case 8: negative odd present
def test8_a : Array Int := #[-4, -3, 2]
def test8_Expected : Option Nat := some 1

-- Test case 9: singleton -1 (required Int boundary case)
def test9_a : Array Int := #[-1]
def test9_Expected : Option Nat := some 0

-- Recommend to validate: empty, all-even, negative-odd
end TestCases
