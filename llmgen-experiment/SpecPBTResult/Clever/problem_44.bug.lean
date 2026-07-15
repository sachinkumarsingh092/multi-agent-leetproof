import SpecPBTResult.Clever.CleverAllImports
import Velvet.Std
import Extensions.Testing
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem: problem_44

section Specs

register_specdef_allow_recursion

def problem_spec
-- function signature
(implementation: Nat → Nat -> String)
-- inputs
(x base: Nat) :=
-- spec
let spec (result: String) :=
let result_array := result.toList.map (fun c => c.toNat - '0'.toNat);
let pow_array := (List.range result_array.length).map (fun i => base^(result_array.length - i - 1) * result_array[i]!);
let pow_sum := pow_array.sum;
(0 < base ∧ base ≤ 10) ∧
(∀ i, i < result_array.length →
result_array[i]! < base ∧ 0 ≤ result_array[i]! →
pow_sum = x);
-- program termination
∃ result, implementation x base = result ∧
spec result

def precondition (x : Nat) (base : Nat) : Prop :=
  True

instance instDecidablePrecond (x : Nat) (base : Nat) : Decidable (precondition x base) := by
  unfold precondition
  infer_instance

def postcondition (x : Nat) (base : Nat) (result : String) :=
  let result_array := result.toList.map (fun c => c.toNat - '0'.toNat);
  let pow_array := (List.range result_array.length).map (fun i => base^(result_array.length - i - 1) * result_array[i]!);
  let pow_sum := pow_array.sum;
  (0 < base ∧ base ≤ 10) ∧
  (∀ i, i < result_array.length →
  result_array[i]! < base ∧ 0 ≤ result_array[i]! →
  pow_sum = x)

end Specs

section Impl

def implementation (x base: Nat) : String :=
sorry

end Impl

section TestCases

def test1_x : Nat := 8
def test1_base : Nat := 3
def test1_Expected : String := "22"

def test2_x : Nat := 8
def test2_base : Nat := 2
def test2_Expected : String := "1000"

def test3_x : Nat := 7
def test3_base : Nat := 2
def test3_Expected : String := "111"

end TestCases

set_option maxHeartbeats 500000

def uniqueness_test1 (result : String) :
  result ≠ test1_Expected →
  ¬ postcondition test1_x test1_base result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  plausible'_mut (seeds := #[test1_Expected]) (config := { numInst := 100000 })
