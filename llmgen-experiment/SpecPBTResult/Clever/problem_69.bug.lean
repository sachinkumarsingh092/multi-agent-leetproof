import SpecPBTResult.Clever.CleverAllImports
import Velvet.Std
import Extensions.Testing
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem: problem_69

section Specs

register_specdef_allow_recursion

def problem_spec
-- function signature
(implementation: List Int → Int)
-- inputs
(numbers: List Int) :=
-- spec
let spec (result: Int) :=
0 < numbers.length ∧ numbers.all (fun n => 0 < n) →
(result ≠ -1 ↔ ∃ i : Nat, i < numbers.length ∧
  numbers[i]! = result ∧ numbers[i]! > 0 ∧
  numbers[i]! ≤ (numbers.filter (fun x => x = numbers[i]!)).length ∧
  (¬∃ j : Nat, j < numbers.length ∧
  numbers[i]! < numbers[j]! ∧ numbers[j]! ≤ numbers.count numbers[j]!));
-- program termination
∃ result, implementation numbers = result ∧
spec result

def precondition (numbers : List Int) : Prop :=
  0 < numbers.length ∧ numbers.all (fun n => 0 < n)

instance instDecidablePrecond (numbers : List Int) : Decidable (precondition numbers) := by
  unfold precondition
  infer_instance

def postcondition (numbers : List Int) (result : (Int)) :=
  (result ≠ -1 ↔ ∃ i : Nat, i < numbers.length ∧
    numbers[i]! = result ∧ numbers[i]! > 0 ∧
    numbers[i]! ≤ (numbers.filter (fun x => x = numbers[i]!)).length ∧
    (¬∃ j : Nat, j < numbers.length ∧
    numbers[i]! < numbers[j]! ∧ numbers[j]! ≤ numbers.count numbers[j]!))

end Specs

section Impl

def implementation (numbers: List Int) : (Int) :=
sorry

end Impl

section TestCases

def test1_numbers : List Int := [4, 1, 2, 2, 3, 1]
def test1_Expected : (Int) := 2

def test2_numbers : List Int := [1, 2, 2, 3, 3, 3, 4, 4, 4]
def test2_Expected : (Int) := 3

def test3_numbers : List Int := [5, 5, 4, 4, 4]
def test3_Expected : (Int) := -1

end TestCases

set_option maxHeartbeats 500000

def uniqueness_test1 (result : (Int)) :
  result ≠ test1_Expected →
  ¬ postcondition test1_numbers result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  plausible'_mut (seeds := #[test1_Expected]) (config := { numInst := 100000 })
