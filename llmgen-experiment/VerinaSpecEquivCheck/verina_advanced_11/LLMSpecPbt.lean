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
    MajorityElement: Find the majority element in a list of integers.
    Natural language breakdown:
    1. The input is a list of integers; it may be empty and may contain duplicates and negative values.
    2. For an integer x, its occurrence count in the list is `lst.count x`.
    3. An integer x is a majority element of the list iff it occurs strictly more than half of the list length.
    4. Equivalently (avoiding division): x is a majority element iff 2 * count(x) > length.
    5. If a majority element exists, it is unique.
    6. If a majority element exists, the method must return that (unique) element.
    7. If no majority element exists, the method must return -1.
    8. Note: Because the return type is Int and -1 is also a valid list element, it is possible that
       the correct majority element equals -1; in that case the required output is still -1.
-/

section Specs
-- Helper predicate: x is a majority element of lst iff it appears strictly more than half the time.
-- We avoid division by using the equivalent inequality 2 * count(x) > length.
-- Note: `lst.count x : Nat` and `lst.length : Nat`.
def isMajority (lst : List Int) (x : Int) : Prop :=
  (2 * lst.count x) > lst.length

def precondition (lst : List Int) : Prop :=
  True

-- Postcondition:
-- 1. If a majority element exists, `result` is that unique majority element.
-- 2. If no majority element exists, `result = -1`.
-- This matches the prompt's requirement "return the majority element if one exists, otherwise -1".
def postcondition (lst : List Int) (result : Int) : Prop :=
  ((∃ x : Int, isMajority lst x) →
      (isMajority lst result ∧ ∀ x : Int, isMajority lst x → x = result)) ∧
  ((¬ (∃ x : Int, isMajority lst x)) → result = (-1))
end Specs

section Impl
method MajorityElement (lst : List Int)
  return (result : Int)
  require precondition lst
  ensures postcondition lst result
  do
  -- Placeholder body only
  pure (-1)

prove_correct MajorityElement by sorry
end Impl

section TestCases
-- Test case 1: empty list (no majority)
-- (No explicit example was provided in the prompt; we use this as the first representative case.)
def test1_lst : List Int := []
def test1_Expected : Int := (-1)

-- Test case 2: singleton list (the only element is majority)
def test2_lst : List Int := [5]
def test2_Expected : Int := 5

-- Test case 3: all distinct (no majority)
def test3_lst : List Int := [1, 2, 3]
def test3_Expected : Int := (-1)

-- Test case 4: simple majority in odd-length list

def test4_lst : List Int := [2, 2, 1]
def test4_Expected : Int := 2

-- Test case 5: exactly half occurrences is not a majority (even length)
def test5_lst : List Int := [1, 1, 2, 2]
def test5_Expected : Int := (-1)

-- Test case 6: majority element is 0 in an even-length list
-- length = 6, count(0) = 4, so 4 > 3.
def test6_lst : List Int := [0, 0, 0, 1, 2, 0]
def test6_Expected : Int := 0

-- Test case 7: majority element is a negative number (not -1)
def test7_lst : List Int := [(-2), (-2), 3, (-2), 4]
def test7_Expected : Int := (-2)

-- Test case 8: majority element is -1 (sentinel value can also be the true majority)
-- length = 3, count(-1) = 2, so 2 > 1.
def test8_lst : List Int := [(-1), (-1), 2]
def test8_Expected : Int := (-1)

-- Test case 9: list contains -1 but there is no majority
-- length = 4, all counts are ≤ 2, so no strict majority.
def test9_lst : List Int := [(-1), 0, 1, 2]
def test9_Expected : Int := (-1)

-- Recommend to validate: test1_lst, test6_lst, test8_lst
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test8' (result : Int) :
  result ≠ test8_Expected →
  ¬ postcondition test8_lst result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test8_Expected]) (config := { numInst := 100000 })
