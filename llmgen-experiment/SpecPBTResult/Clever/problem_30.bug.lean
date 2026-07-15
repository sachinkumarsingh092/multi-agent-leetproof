import SpecPBTResult.Clever.CleverAllImports
import Velvet.Std
import Extensions.Testing
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem: problem_30

section Specs

register_specdef_allow_recursion

def problem_spec
-- function signature
(implementation: List Int → List Int)
-- inputs
(numbers: List Int) :=
-- spec
let spec (result: List Int) :=
  result.all (λ x => x > 0 ∧ x ∈ numbers) ∧
  numbers.all (λ x => x > 0 → x ∈ result) ∧
  result.all (λ x => result.count x = numbers.count x);
-- program termination
∃ result,
  implementation numbers = result ∧
  spec result

def precondition (numbers : List Int) : Prop :=
  True

instance instDecidablePrecond (numbers : List Int) : Decidable (precondition numbers) := by
  unfold precondition
  infer_instance

def postcondition (numbers : List Int) (result : List Int) :=
  result.all (λ x => x > 0 ∧ x ∈ numbers) ∧
    numbers.all (λ x => x > 0 → x ∈ result) ∧
    result.all (λ x => result.count x = numbers.count x)

end Specs

section Impl

def implementation (numbers: List Int): List Int :=
numbers.filter (λ x => x > 0)

end Impl

section TestCases

def test1_numbers : List Int := [-1, 2, -4, 5, 6]
def test1_Expected : List Int := [2, 5, 6]

def test2_numbers : List Int := [5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10]
def test2_Expected : List Int := [5, 3, 2, 3, 9, 123, 1]

def test3_numbers : List Int := []
def test3_Expected : List Int := []

def test4_numbers : List Int := [17, -19, -16, -2, -8, -3, -2, -16, 13, 10, 19, -8, -14, -9, -14, 0, -4]
def test4_Expected : List Int := [17, 13, 10, 19]

def test5_numbers : List Int := [-19, 10, 11, -19, 18, 19, -12, -17, -20, 15, -4, 12, 12, -13, 1, -10, 20]
def test5_Expected : List Int := [10, 11, 18, 19, 15, 12, 12, 1, 20]

def test6_numbers : List Int := [6, 1, 1, -18, -8]
def test6_Expected : List Int := [6, 1, 1]

def test7_numbers : List Int := [-4, -16, 9, 11, 1, 9, -16, 5, -16, 0, -14, -20, 1, -11, 20, -18, 9, 14, -19]
def test7_Expected : List Int := [9, 11, 1, 9, 5, 1, 20, 9, 14]

def test8_numbers : List Int := [5, 10, 9, 12, 16, 10, 13, 0, -14, 2]
def test8_Expected : List Int := [5, 10, 9, 12, 16, 10, 13, 2]

def test9_numbers : List Int := [-3, 0]
def test9_Expected : List Int := []

def test10_numbers : List Int := [-17, -19, 3, 17, -19, -20, 17]
def test10_Expected : List Int := [3, 17, 17]

def test11_numbers : List Int := [20, -17, -5, -10, 11, 5, 15, -15, 10, 9, -19, 1, 18, -13, -13, -3]
def test11_Expected : List Int := [20, 11, 5, 15, 10, 9, 1, 18]

def test12_numbers : List Int := [12, 5, 14, -7, -12, 1, 11, 19, -1, 11, 7, 12, -1, -11, 15, -2, 11, 7]
def test12_Expected : List Int := [12, 5, 14, 1, 11, 19, 11, 7, 12, 15, 11, 7]

def test13_numbers : List Int := [18, 19, -5, -14, 5, -9, 10, -18, 12, 6, 6, 15]
def test13_Expected : List Int := [18, 19, 5, 10, 12, 6, 6, 15]

def test14_numbers : List Int := [-4, 1, -17, -18]
def test14_Expected : List Int := [1]

def test15_numbers : List Int := [-15, 15, -11, 20, -3, -16, -9, 17, -1, 19, -15]
def test15_Expected : List Int := [15, 20, 17, 19]

def test16_numbers : List Int := [-4, 20]
def test16_Expected : List Int := [20]

def test17_numbers : List Int := [-2, 20, -20, -2, 6, -12, -19, -14, 12]
def test17_Expected : List Int := [20, 6, 12]
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test1 (result : List Int) :
  result ≠ test1_Expected →
  ¬ postcondition test1_numbers result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  plausible'_mut (seeds := #[test1_Expected]) (config := { numInst := 100000 })
