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
    IsContiguousSublist: Determine whether one list of integers occurs as a contiguous sublist of another.
    Natural language breakdown:
    1. Inputs are two lists of integers: `sub` (the candidate sublist) and `xs` (the list to search within).
    2. `sub` occurs contiguously in `xs` exactly when there exist lists `pre` and `suf` such that
       `xs = pre ++ sub ++ suf`.
    3. The method returns `true` iff `sub` occurs contiguously in `xs`.
    4. The method returns `false` iff `sub` does not occur contiguously in `xs`.
    5. Edge cases:
       - The empty list occurs contiguously in every list.
       - A non-empty list cannot occur contiguously in an empty list.
       - If `sub.length > xs.length`, then `sub` cannot occur contiguously in `xs`.
-/

section Specs
-- Helper predicate: propositional definition of contiguous sublist occurrence.
-- `sub` is a contiguous sublist of `xs` iff `xs` can be split into a prefix, then `sub`, then a suffix.
def IsContigSublist (sub : List Int) (xs : List Int) : Prop :=
  ∃ (pre : List Int) (suf : List Int), xs = pre ++ sub ++ suf

def precondition (sub : List Int) (xs : List Int) : Prop :=
  True

def postcondition (sub : List Int) (xs : List Int) (result : Bool) : Prop :=
  (result = true ↔ IsContigSublist sub xs)
end Specs

section Impl
method IsContiguousSublist (sub : List Int) (xs : List Int)
  return (result : Bool)
  require precondition sub xs
  ensures postcondition sub xs result
  do
  pure false

end Impl

section TestCases
-- Test case 1: sub occurs in the middle
def test1_sub : List Int := [2, 3]
def test1_xs : List Int := [1, 2, 3, 4]
def test1_Expected : Bool := true

-- Test case 2: sub does not occur
def test2_sub : List Int := [2, 4]
def test2_xs : List Int := [1, 2, 3, 4]
def test2_Expected : Bool := false

-- Test case 3: sub equals xs
def test3_sub : List Int := [1, 2, 3]
def test3_xs : List Int := [1, 2, 3]
def test3_Expected : Bool := true

-- Test case 4: sub occurs at the start (prefix)
def test4_sub : List Int := [1, 2]
def test4_xs : List Int := [1, 2, 3, 4]
def test4_Expected : Bool := true

-- Test case 5: sub occurs at the end (suffix)
def test5_sub : List Int := [3, 4]
def test5_xs : List Int := [1, 2, 3, 4]
def test5_Expected : Bool := true

-- Test case 6: empty sublist is always a contiguous sublist
def test6_sub : List Int := []
def test6_xs : List Int := [5, 6]
def test6_Expected : Bool := true

-- Test case 7: non-empty sublist cannot occur in empty xs
-- Includes -1, 0, 1 as elements to cover common Int boundary-like values.
def test7_sub : List Int := [-1, 0, 1]
def test7_xs : List Int := []
def test7_Expected : Bool := false

-- Test case 8: both lists empty
def test8_sub : List Int := []
def test8_xs : List Int := []
def test8_Expected : Bool := true

-- Test case 9: repeated elements; match must be contiguous
def test9_sub : List Int := [1, 1]
def test9_xs : List Int := [0, 1, 1, 1]
def test9_Expected : Bool := true

-- Test case 10: sub longer than xs
def test10_sub : List Int := [1, 2, 3]
def test10_xs : List Int := [1, 2]
def test10_Expected : Bool := false

-- Recommend to validate: empty-sub behavior, both-empty behavior, repeated-element matches
end TestCases
