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
    FirstEvenOddProduct: compute the product of the first even and the first odd integer encountered in a list.

    Natural language breakdown:
    1. The input is a list of integers.
    2. We scan the list from left to right.
    3. The “first even number” is the earliest element whose remainder modulo 2 is 0.
    4. The “first odd number” is the earliest element whose remainder modulo 2 is 1.
    5. The input is assumed to contain at least one even number and at least one odd number.
    6. The output is the product of these two first-found numbers.
-/

section Specs
-- Helper predicates as Bool so they can be used with List.find?
def isEvenB (n : Int) : Bool := (n % 2) == 0

def isOddB (n : Int) : Bool := (n % 2) == 1

-- The precondition requires existence of at least one even and one odd element.
-- We express this via List.find? returning some value.
def precondition (lst : List Int) : Prop :=
  (lst.find? isEvenB).isSome = true ∧
  (lst.find? isOddB).isSome = true

-- Postcondition: result equals the product of the first even and first odd elements.
-- We pin down “first” using List.find? itself (which is defined as left-to-right search).
def postcondition (lst : List Int) (result : Int) : Prop :=
  ∃ (e : Int) (o : Int),
    lst.find? isEvenB = some e ∧
    lst.find? isOddB = some o ∧
    result = e * o
end Specs

section Impl
method FirstEvenOddProduct (lst : List Int)
  return (result : Int)
  require precondition lst
  ensures postcondition lst result
  do
  pure 0

prove_correct FirstEvenOddProduct by sorry
end Impl

section TestCases
-- Test case 1: typical list with even then odd
def test1_lst : List Int := [2, 3, 4]
def test1_Expected : Int := 6

-- Test case 2: odd appears before the first even
def test2_lst : List Int := [3, 2, 5, 6]
def test2_Expected : Int := 6

-- Test case 3: includes boundary values 0 and 1
def test3_lst : List Int := [0, 1]
def test3_Expected : Int := 0

-- Test case 4: includes -1 as the first odd and a later even
def test4_lst : List Int := [-1, 4, 7]
def test4_Expected : Int := -4

-- Test case 5: all negative values
def test5_lst : List Int := [-2, -3, -4]
def test5_Expected : Int := 6

-- Test case 6: first even occurs later in the list
def test6_lst : List Int := [5, 7, 8, 2]
def test6_Expected : Int := 40

-- Test case 7: first odd occurs later in the list
def test7_lst : List Int := [2, 4, 6, 9, 10]
def test7_Expected : Int := 18

-- Test case 8: single even at the end, multiple odds before it
def test8_lst : List Int := [1, 3, 5, 2]
def test8_Expected : Int := 2
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
