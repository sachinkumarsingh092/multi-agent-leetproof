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
    SumAndAverageFirstN: compute the sum and average of the first n natural numbers.
    **Important: complexity should be O(1)**
    Natural language breakdown:
    1. The input is a natural number n.
    2. The input is assumed to be positive (n > 0).
    3. Let S be the sum of the first n natural numbers 1, 2, ..., n.
    4. S satisfies the closed form S = n * (n + 1) / 2.
    5. The output is a pair (sumInt, avgFloat).
    6. sumInt is an Int representation of S.
    7. avgFloat is the average of the n numbers 1, 2, ..., n, computed as S / n.
    8. To keep Float conversions precise, both n and S are bounded by 2^53.
-/

section Specs
-- 2^53, the largest integer such that all naturals below it are exactly representable in IEEE-754 Float.
def twoPow53 : Nat := 9007199254740992

-- Closed-form sum S = 1 + 2 + ... + n.
-- Note: This is a mathematical characterization; it is not an algorithmic summation.
def sumOneTo (n : Nat) : Nat := n * (n + 1) / 2

def precondition (n : Nat) : Prop :=
  n > 0 ∧
  n < twoPow53 ∧
  sumOneTo n < twoPow53

def postcondition (n : Nat) (result : Int × Float) : Prop :=
  result.1 = Int.ofNat (sumOneTo n) ∧
  result.2 == (Float.ofInt result.1 / Float.ofNat n)
end Specs

section Impl
method SumAndAverageFirstN (n : Nat)
  return (result : Int × Float)
  require precondition n
  ensures postcondition n result
  do
  pure (0, 0.0)  -- placeholder body

prove_correct SumAndAverageFirstN by sorry
end Impl

section TestCases
-- Test case 1: n = 1 (smallest valid input)
def test1_n : Nat := 1
def test1_Expected : Int × Float :=
  (Int.ofNat (sumOneTo test1_n), Float.ofNat (sumOneTo test1_n) / Float.ofNat test1_n)

-- Test case 2: n = 2
def test2_n : Nat := 2
def test2_Expected : Int × Float :=
  (Int.ofNat (sumOneTo test2_n), Float.ofNat (sumOneTo test2_n) / Float.ofNat test2_n)

-- Test case 3: n = 3
def test3_n : Nat := 3
def test3_Expected : Int × Float :=
  (Int.ofNat (sumOneTo test3_n), Float.ofNat (sumOneTo test3_n) / Float.ofNat test3_n)

-- Test case 4: n = 4
def test4_n : Nat := 4
def test4_Expected : Int × Float :=
  (Int.ofNat (sumOneTo test4_n), Float.ofNat (sumOneTo test4_n) / Float.ofNat test4_n)

-- Test case 5: n = 10
def test5_n : Nat := 10
def test5_Expected : Int × Float :=
  (Int.ofNat (sumOneTo test5_n), Float.ofNat (sumOneTo test5_n) / Float.ofNat test5_n)

-- Test case 6: n = 100
def test6_n : Nat := 100
def test6_Expected : Int × Float :=
  (Int.ofNat (sumOneTo test6_n), Float.ofNat (sumOneTo test6_n) / Float.ofNat test6_n)

-- Test case 7: n = 10000
def test7_n : Nat := 10000
def test7_Expected : Int × Float :=
  (Int.ofNat (sumOneTo test7_n), Float.ofNat (sumOneTo test7_n) / Float.ofNat test7_n)

-- Test case 8: larger n still satisfying the Float-precision bound on the sum
-- sumOneTo 10_000_000 = 50_000_005_000_000 < 2^53

def test8_n : Nat := 10000000
def test8_Expected : Int × Float :=
  (Int.ofNat (sumOneTo test8_n), Float.ofNat (sumOneTo test8_n) / Float.ofNat test8_n)

-- Test case 9: near the largest n for which sumOneTo n < 2^53 holds

def test9_n : Nat := 134000000
def test9_Expected : Int × Float :=
  (Int.ofNat (sumOneTo test9_n), Float.ofNat (sumOneTo test9_n) / Float.ofNat test9_n)

-- Recommend to validate: n = 1, n = 10000, n = 134000000
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test1' (result : Int × Float) :
  result ≠ test1_Expected →
  ¬ postcondition test1_n result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test1_Expected]) (config := { numInst := 100000 })
