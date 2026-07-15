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
    PrefixMaxAndFirstGreaterIndex: compute the maximum of the first x elements and choose an index p based on the first element greater than that maximum.
    Natural language breakdown:
    1. Input is a nonempty array a of integers and a natural number x.
    2. The index x is valid for splitting the array: 1 ≤ x < a.size.
    3. Let m be the maximum value among the first x elements, i.e. indices 0..x-1.
    4. Consider the suffix segment starting at index x and ending at a.size-1.
    5. If there exists an index i with x ≤ i < a.size and a[i] is strictly greater than m,
       then p is the smallest such index (the first occurrence in the suffix of a value > m).
    6. Otherwise (no element in the suffix is > m), p is set to the last index of the array, a.size - 1.
    7. The output is the pair (m, p).
-/

section Specs
-- Helper predicate: m is the maximum value among indices [0, x).
def isMaxOfPrefix (a : Array Int) (x : Nat) (m : Int) : Prop :=
  (∀ (i : Nat), i < x → a[i]! ≤ m) ∧
  (∃ (i : Nat), i < x ∧ a[i]! = m)

-- Helper predicate: p is the correct index in [x, a.size) according to the problem statement.
def isChosenIndex (a : Array Int) (x : Nat) (m : Int) (p : Nat) : Prop :=
  x ≤ p ∧ p < a.size ∧
  ((∃ (i : Nat), x ≤ i ∧ i < a.size ∧ a[i]! > m) →
      (a[p]! > m ∧ (∀ (j : Nat), x ≤ j ∧ j < p → a[j]! ≤ m))) ∧
  ((¬ ∃ (i : Nat), x ≤ i ∧ i < a.size ∧ a[i]! > m) →
      (p = a.size - 1 ∧ (∀ (i : Nat), x ≤ i ∧ i < a.size → a[i]! ≤ m)))

-- Preconditions from the problem statement.
def precondition (a : Array Int) (x : Nat) : Prop :=
  a.size > 0 ∧ 1 ≤ x ∧ x < a.size

-- Postcondition: result = (m, p) where m is max of prefix and p is chosen as specified.
def postcondition (a : Array Int) (x : Nat) (result : Int × Nat) : Prop :=
  isMaxOfPrefix a x result.1 ∧
  isChosenIndex a x result.1 result.2
end Specs

section Impl
method PrefixMaxAndFirstGreaterIndex (a : Array Int) (x : Nat)
  return (result : Int × Nat)
  require precondition a x
  ensures postcondition a x result
  do
  pure (0, 0)  -- placeholder

prove_correct PrefixMaxAndFirstGreaterIndex by sorry
end Impl

section TestCases
-- Test case 1: typical array with a later element greater than the prefix maximum
-- a = [1, 3, 2, 5, 4], x = 3 => prefix max m = 3, first > 3 from index 3 is at p = 3
-- expected (3, 3)
def test1_a : Array Int := #[1, 3, 2, 5, 4]
def test1_x : Nat := 3
def test1_Expected : Int × Nat := (3, 3)

-- Test case 2: no element in suffix exceeds prefix max; p should be last index
-- a = [5, 1, 4, 3], x = 2 => m = 5, no > 5 in suffix => p = 3
-- expected (5, 3)
def test2_a : Array Int := #[5, 1, 4, 3]
def test2_x : Nat := 2
def test2_Expected : Int × Nat := (5, 3)

-- Test case 3: minimal valid x = 1 (required edge)
-- a = [2, 3], x = 1 => m = 2, suffix has 3 > 2 at p = 1
-- expected (2, 1)
def test3_a : Array Int := #[2, 3]
def test3_x : Nat := 1
def test3_Expected : Int × Nat := (2, 1)

-- Test case 4: x = a.size - 1 (suffix has exactly one element)
-- a = [1, 9, 2, 8], x = 3 => m = 9, suffix is [8], no > 9 => p = 3
-- expected (9, 3)
def test4_a : Array Int := #[1, 9, 2, 8]
def test4_x : Nat := 3
def test4_Expected : Int × Nat := (9, 3)

-- Test case 5: negative numbers; suffix contains first element greater than m immediately at x
-- a = [-5, -2, -3, -1], x = 2 => m = -2, a[2] = -3 not >, a[3] = -1 > => p = 3
-- expected (-2, 3)
def test5_a : Array Int := #[-5, -2, -3, -1]
def test5_x : Nat := 2
def test5_Expected : Int × Nat := (-2, 3)

-- Test case 6: repeated values in prefix; maximum occurs multiple times
-- a = [4, 4, 1, 4, 5], x = 4 => m = 4, suffix has 5 > 4 at p = 4
-- expected (4, 4)
def test6_a : Array Int := #[4, 4, 1, 4, 5]
def test6_x : Nat := 4
def test6_Expected : Int × Nat := (4, 4)

-- Test case 7: suffix has an element equal to m but not greater; must still select last when none greater
-- a = [3, 1, 2, 3], x = 3 => m = 3, suffix is [3] (not >) => p = 3
-- expected (3, 3)
def test7_a : Array Int := #[3, 1, 2, 3]
def test7_x : Nat := 3
def test7_Expected : Int × Nat := (3, 3)

-- Test case 8: first greater occurs later in suffix (not at x)
-- a = [0, 2, 1, 2, 3], x = 4 => m = 2, suffix is [3], 3 > 2 at p = 4
-- expected (2, 4)
def test8_a : Array Int := #[0, 2, 1, 2, 3]
def test8_x : Nat := 4
def test8_Expected : Int × Nat := (2, 4)

-- Test case 9: larger array, first greater at x exactly
-- a = [1, 2, 3, 10, 0, 0], x = 3 => m = 3, a[3] = 10 > 3 so p = 3
-- expected (3, 3)
def test9_a : Array Int := #[1, 2, 3, 10, 0, 0]
def test9_x : Nat := 3
def test9_Expected : Int × Nat := (3, 3)
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test9' (result : Int × Nat) :
  result ≠ test9_Expected →
  ¬ postcondition test9_a test9_x result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test9_Expected]) (config := { numInst := 100000 })
