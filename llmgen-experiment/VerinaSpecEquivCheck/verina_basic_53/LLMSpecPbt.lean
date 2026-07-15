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
    verina_basic_53: Sum of the first N natural numbers
    Natural language breakdown:
    1. The input N is a natural number indicating how many initial natural numbers to sum.
    2. The required output is the sum 1 + 2 + ... + N.
    3. By convention, when N = 0 the sum is 0.
    4. For all N, the sum is the N-th triangular number and equals N * (N + 1) / 2.
    5. The method returns a natural number result representing this sum.
    6. There are no additional input constraints beyond N being a Nat.
    7. Although an implementation may be recursive, the specification constrains only the input-output relation.
-/

section Specs
def precondition (N : Nat) : Prop :=
  True

def postcondition (N : Nat) (result : Nat) : Prop :=
  result = (N * (N + 1)) / 2
end Specs

section Impl
method SumFirstN (N : Nat)
  return (result : Nat)
  require precondition N
  ensures postcondition N result
  do
  -- Placeholder body only
  pure 0

prove_correct SumFirstN by sorry
end Impl

section TestCases
-- Test case 1: N = 0 (boundary; explicitly mentioned in statement)
def test1_N : Nat := 0
def test1_Expected : Nat := 0

-- Test case 2: N = 1 (smallest positive)
def test2_N : Nat := 1
def test2_Expected : Nat := 1

-- Test case 3: N = 2
def test3_N : Nat := 2
def test3_Expected : Nat := 3

-- Test case 4: N = 3
def test4_N : Nat := 3
def test4_Expected : Nat := 6

-- Test case 5: N = 4
def test5_N : Nat := 4
def test5_Expected : Nat := 10

-- Test case 6: N = 5
def test6_N : Nat := 5
def test6_Expected : Nat := 15

-- Test case 7: N = 10 (typical)
def test7_N : Nat := 10
def test7_Expected : Nat := 55

-- Test case 8: N = 100 (larger)
def test8_N : Nat := 100
def test8_Expected : Nat := 5050

-- Test case 9: N = 1000 (stress)
def test9_N : Nat := 1000
def test9_Expected : Nat := 500500

-- Recommend to validate: test1_N, test7_N, test9_N
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test9' (result : Nat) :
  result ≠ test9_Expected →
  ¬ postcondition test9_N result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test9_Expected]) (config := { numInst := 100000 })
