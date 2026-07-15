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
    UniqueKeyOccurrence: Determine whether a specified key appears exactly once in an array of integers.
    Natural language breakdown:
    1. The input is an array `a` of integers and an integer `key`.
    2. An occurrence of `key` is an index `i` with `i < a.size` and `a[i]! = key`.
    3. The output is a Boolean.
    4. The output must be true exactly when the number of occurrences of `key` in `a` is 1.
    5. If `key` occurs zero times, the output is false.
    6. If `key` occurs two or more times, the output is false.
    7. The specification does not prescribe an implementation strategy; it only constrains the observable result.
-/

section Specs
-- Helper definition: the key occurs exactly once iff its Array.count is 1.
def occursExactlyOnce (a : Array Int) (key : Int) : Prop :=
  a.count key = 1

def precondition (a : Array Int) (key : Int) : Prop :=
  True

def postcondition (a : Array Int) (key : Int) (result : Bool) : Prop :=
  (result = true ↔ occursExactlyOnce a key)
end Specs

section Impl
method UniqueKeyOccurrence (a : Array Int) (key : Int)
  return (result : Bool)
  require precondition a key
  ensures postcondition a key result
  do
  pure false

end Impl

section TestCases
-- Test case 1: empty array, key absent
def test1_a : Array Int := #[]
def test1_key : Int := 5
def test1_Expected : Bool := false

-- Test case 2: singleton array equals key
def test2_a : Array Int := #[7]
def test2_key : Int := 7
def test2_Expected : Bool := true

-- Test case 3: singleton array not equal to key
def test3_a : Array Int := #[7]
def test3_key : Int := 8
def test3_Expected : Bool := false

-- Test case 4: key occurs exactly once in a longer array
def test4_a : Array Int := #[1, 2, 3, 4]
def test4_key : Int := 3
def test4_Expected : Bool := true

-- Test case 5: key occurs multiple times
def test5_a : Array Int := #[2, 2, 2]
def test5_key : Int := 2
def test5_Expected : Bool := false

-- Test case 6: key occurs zero times but array non-empty
def test6_a : Array Int := #[1, 2, 3]
def test6_key : Int := 0
def test6_Expected : Bool := false

-- Test case 7: include negative key; occurs exactly once
def test7_a : Array Int := #[-1, 0, 1]
def test7_key : Int := -1
def test7_Expected : Bool := true

-- Test case 8: include negative key; occurs twice
def test8_a : Array Int := #[-1, -1, 2]
def test8_key : Int := -1
def test8_Expected : Bool := false

-- Test case 9: boundary-style key 0 occurs exactly once among other zeros? (here: once)
def test9_a : Array Int := #[0, 1, 2, 3]
def test9_key : Int := 0
def test9_Expected : Bool := true
end TestCases
