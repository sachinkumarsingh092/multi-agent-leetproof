import SpecPBTResult.Clever.CleverAllImports
import Velvet.Std
import Extensions.Testing
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem: problem_24

section Specs

register_specdef_allow_recursion

variable (n : Nat)

def problem_spec
-- function signature
(implementation: Nat → Nat)
-- inputs
(n: Nat) :=
-- spec
let spec (result: Nat) :=
0 < n → 0 < result → result ∣ n → ∀ x, x ∣ n → x ≠ n → x ≤ result;
-- program termination
∃ result, implementation n = result ∧
spec result

def precondition (n : Nat) : Prop :=
  0 < n

instance instDecidablePrecond (n : Nat) : Decidable (precondition n) := by
  unfold precondition
  infer_instance

def postcondition (n : Nat) (result : Nat) :=
  0 < result →
    result ∣ n →
    ∀ x, x ∣ n →
    x ≠ n →
    x ≤ result

end Specs

section Impl

def implementation (n: Nat) : Nat :=
let possible_divisors := (List.range (n / 2 + 1)).drop 1
let reversed_possible_divisors := List.reverse possible_divisors;
Id.run do
  for i in reversed_possible_divisors do
    if n % i = 0 then
      return i
  return 1

end Impl

section TestCases

def test1_n : Nat := 15
def test1_Expected : Nat := 5

def test2_n : Nat := 9
def test2_Expected : Nat := 3

def test3_n : Nat := 19
def test3_Expected : Nat := 1

def test4_n : Nat := 9
def test4_Expected : Nat := 3

def test5_n : Nat := 16
def test5_Expected : Nat := 8

def test6_n : Nat := 20
def test6_Expected : Nat := 10

def test7_n : Nat := 13
def test7_Expected : Nat := 1

def test8_n : Nat := 5
def test8_Expected : Nat := 1

def test9_n : Nat := 13
def test9_Expected : Nat := 1

def test10_n : Nat := 16
def test10_Expected : Nat := 8

def test11_n : Nat := 2
def test11_Expected : Nat := 1

def test12_n : Nat := 10
def test12_Expected : Nat := 5

def test13_n : Nat := 10
def test13_Expected : Nat := 5

def test14_n : Nat := 8
def test14_Expected : Nat := 4

def test15_n : Nat := 18
def test15_Expected : Nat := 9

def test16_n : Nat := 4
def test16_Expected : Nat := 2
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test1' (result : Nat) :
  result ≠ test1_Expected →
  ¬ postcondition test1_n result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test1_Expected]) (config := { numInst := 100000 })
