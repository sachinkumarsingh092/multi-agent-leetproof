import SpecPBTResult.Clever.CleverAllImports
import Velvet.Std
import Extensions.Testing
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem: problem_84

section Specs

register_specdef_allow_recursion

def problem_spec
-- function signature
(implementation: Nat → String)
-- inputs
(n: Nat) :=
-- spec
let spec (result : String) :=
  0 < n →
  result.all (fun c => c = '0' ∨ c = '1') →
  Nat.ofDigits 2 (result.data.map (fun c => if c = '0' then 0 else 1)).reverse = (Nat.digits 10 n).sum
-- program termination
∃ result,
  implementation n = result ∧
  spec result

def precondition (n : Nat) : Prop :=
  0 < n

instance instDecidablePrecond (n : Nat) : Decidable (precondition n) := by
  unfold precondition
  infer_instance

def postcondition (n : Nat) (result : String) :=
  result.all (fun c => c = '0' ∨ c = '1') →
    Nat.ofDigits 2 (result.data.map (fun c => if c = '0' then 0 else 1)).reverse = (Nat.digits 10 n).sum

end Specs

section Impl

def implementation (n: Nat) : String :=
sorry

end Impl

section TestCases

def test1_n : Nat := 1000
def test1_Expected : String := "1"

def test2_n : Nat := 150
def test2_Expected : String := "110"

def test3_n : Nat := 147
def test3_Expected : String := "1100"

end TestCases

set_option maxHeartbeats 500000

def uniqueness_test1 (result : String) :
  result ≠ test1_Expected →
  ¬ postcondition test1_n result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  plausible'_mut (seeds := #[test1_Expected]) (config := { numInst := 100000 })
