import SpecPBTResult.Clever.CleverAllImports
import Velvet.Std
import Extensions.Testing
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem: problem_9

section Specs

register_specdef_allow_recursion

def problem_spec
-- function signature
(implementation: List Int → List Int)
-- inputs
(numbers: List Int) :=
-- spec
let spec (result: List Int) :=
result.length = numbers.length ∧
∀ i, i < numbers.length →
(result[i]! ∈ numbers.take (i + 1) ∧
∀ j, j ≤ i → numbers[j]! ≤ result[i]!);
-- program termination
∃ result, implementation numbers = result ∧
spec result

def precondition (numbers : List Int) : Prop :=
  True

instance instDecidablePrecond (numbers : List Int) : Decidable (precondition numbers) := by
  unfold precondition
  infer_instance

def postcondition (numbers : List Int) (result : List Int) :=
  result.length = numbers.length ∧
  ∀ i, i < numbers.length →
    (result[i]! ∈ numbers.take (i + 1) ∧
  ∀ j, j ≤ i → numbers[j]! ≤ result[i]!)

end Specs

section Impl

def implementation (numbers: List Int) : List Int :=
let rec rolling_max (numbers: List Int) (results: List Int) (acc: Int) : List Int :=
  match numbers with
  | [] => results
  | n :: ns =>
    let new_acc := max acc n
    let new_results := results ++ [new_acc]
    rolling_max ns new_results new_acc
rolling_max numbers [] 0

end Impl

section TestCases

def test1_numbers : List Int := [1, 2, 3, 2, 3, 4, 2]
def test1_Expected : List Int := [1, 2, 3, 3, 3, 4, 4]

def test2_numbers : List Int := [-6, 20, -5, 17, -6, 3, -14, -8, 7, -20, 2, -15, 20, -13, -11, 18, 7]
def test2_Expected : List Int := [0, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20]

def test3_numbers : List Int := [-13]
def test3_Expected : List Int := [0]

def test4_numbers : List Int := [-8, 5, -19, 18, 20, -3, -15, -1, -4, -11, -11, -2, -8, 16, -18, -9, -18, 18, 7, -14]
def test4_Expected : List Int := [0, 5, 5, 18, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20]

def test5_numbers : List Int := [-13, -6, -8, 12, 19, 19, 13, -18, 16, 8, -13, 2, -5, 13, 17, -6, -8, 4, -16, 0]
def test5_Expected : List Int := [0, 0, 0, 12, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19]

def test6_numbers : List Int := [10, -2, -7, 0, 2, -13, -9, 6, 0, 9, -1, 17, -2, -16]
def test6_Expected : List Int := [10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 17, 17, 17]

def test7_numbers : List Int := [-15, -3, 9, -16, -3, -14, 16, -13, 0, -17, 13, -4, -3, -4, 3, -3, 10, 5, -17]
def test7_Expected : List Int := [0, 0, 9, 9, 9, 9, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16]

def test8_numbers : List Int := []
def test8_Expected : List Int := []

def test9_numbers : List Int := [-10, 7, 18, 10, -7, 6]
def test9_Expected : List Int := [0, 7, 18, 18, 18, 18]

def test10_numbers : List Int := [8]
def test10_Expected : List Int := [8]

def test11_numbers : List Int := [10, -5, 3, -3, -15, -4, 13, 5, 20, 20, -5]
def test11_Expected : List Int := [10, 10, 10, 10, 10, 10, 13, 13, 20, 20, 20]

def test12_numbers : List Int := [20, -3, 9, -2, -12, 4, -10, 16, 7, -18, -16, -6, -2, -5, -14, -14]
def test12_Expected : List Int := [20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20]

def test13_numbers : List Int := [-11, -1, -13, 2, 9, 15, -7, -19]
def test13_Expected : List Int := [0, 0, 0, 2, 9, 15, 15, 15]

def test14_numbers : List Int := [19, -4, -4, -17]
def test14_Expected : List Int := [19, 19, 19, 19]

def test15_numbers : List Int := [-18, -12, -13, -7, 19, 6, -5, 9, -7, 17, -20, -12, -18, 19, -18, 9, -20, -15]
def test15_Expected : List Int := [0, 0, 0, 0, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19]

def test16_numbers : List Int := [9, -20, -13, 5, 11, 10, -15, 5, -12, -19, -16, 14, 10, 20, 15]
def test16_Expected : List Int := [9, 9, 9, 9, 11, 11, 11, 11, 11, 11, 11, 14, 14, 20, 20]
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test2 (result : List Int) :
  result ≠ test2_Expected →
  ¬ postcondition test2_numbers result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  plausible'_mut (seeds := #[test2_Expected]) (config := { numInst := 100000 })
