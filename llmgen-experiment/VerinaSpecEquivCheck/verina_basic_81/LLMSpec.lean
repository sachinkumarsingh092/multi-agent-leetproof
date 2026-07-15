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
    NatDivRemInt: Integer division with remainder on natural numbers, returning results as integers.
    Natural language breakdown:
    1. Inputs are natural numbers x (dividend) and y (divisor).
    2. The function returns a pair (r, q) of integers, where r is the remainder and q is the quotient.
    3. If y ≠ 0, then the output must satisfy the Euclidean division properties over integers:
       a) (q * Int.ofNat y) + r = Int.ofNat x.
       b) 0 ≤ r and r < Int.ofNat y.
       c) 0 ≤ q.
    4. If y = 0, no division is performed and the output is (Int.ofNat x, 0).
    5. The Euclidean-division constraints apply only in the case y ≠ 0.
-/

section Specs
-- Helper: view a Nat as an Int (explicitly).
def natToInt (n : Nat) : Int :=
  Int.ofNat n

-- Preconditions: all natural-number inputs are allowed.
def precondition (x : Nat) (y : Nat) : Prop :=
  True

-- Postcondition: (r, q) follows Euclidean division when y ≠ 0; otherwise returns (x, 0) in Int.
def postcondition (x : Nat) (y : Nat) (result : Int × Int) : Prop :=
  if y = 0 then
    result = (natToInt x, (0 : Int))
  else
    let r : Int := result.1
    let q : Int := result.2
    (q * natToInt y + r = natToInt x) ∧
    (0 ≤ r) ∧ (r < natToInt y) ∧
    (0 ≤ q)
end Specs

section Impl
method NatDivRemInt (x : Nat) (y : Nat)
  return (result : Int × Int)
  require precondition x y
  ensures postcondition x y result
  do
    pure (natToInt x, (0 : Int))

end Impl

section TestCases
-- Test case 1: boundary (x=0, y=0) -> no division, return (0,0)
def test1_x : Nat := 0
def test1_y : Nat := 0
def test1_Expected : Int × Int := (Int.ofNat 0, (0 : Int))

-- Test case 2: y=0 with nonzero x -> (x,0)
def test2_x : Nat := 5
def test2_y : Nat := 0
def test2_Expected : Int × Int := (Int.ofNat 5, (0 : Int))

-- Test case 3: x=0 with y>0 -> quotient 0, remainder 0
def test3_x : Nat := 0
def test3_y : Nat := 3
def test3_Expected : Int × Int := ((0 : Int), (0 : Int))

-- Test case 4: y=1 -> remainder 0, quotient x
def test4_x : Nat := 7
def test4_y : Nat := 1
def test4_Expected : Int × Int := ((0 : Int), (Int.ofNat 7))

-- Test case 5: typical nontrivial division 7 / 2 -> q=3, r=1
def test5_x : Nat := 7
def test5_y : Nat := 2
def test5_Expected : Int × Int := ((1 : Int), (3 : Int))

-- Test case 6: exact division 8 / 2 -> q=4, r=0
def test6_x : Nat := 8
def test6_y : Nat := 2
def test6_Expected : Int × Int := ((0 : Int), (4 : Int))

-- Test case 7: x < y (1 / 2) -> q=0, r=x
def test7_x : Nat := 1
def test7_y : Nat := 2
def test7_Expected : Int × Int := ((1 : Int), (0 : Int))

-- Test case 8: exact division 9 / 3 -> q=3, r=0
def test8_x : Nat := 9
def test8_y : Nat := 3
def test8_Expected : Int × Int := ((0 : Int), (3 : Int))

-- Test case 9: typical division 10 / 6 -> q=1, r=4
def test9_x : Nat := 10
def test9_y : Nat := 6
def test9_Expected : Int × Int := ((4 : Int), (1 : Int))
end TestCases
