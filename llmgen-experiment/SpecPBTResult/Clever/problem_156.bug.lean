import SpecPBTResult.Clever.CleverAllImports
import Velvet.Std
import Extensions.Testing
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem: problem_156

section Specs

register_specdef_allow_recursion

def problem_spec
-- function signature
(impl: Nat → String)
-- inputs
(num: Nat) :=
-- spec
let spec (result: String) :=
1 ≤ num ∧ num ≤ 1000 ∧ (result.data.all (fun c => c.isLower)) →
isValidRoman result ∧ romanToDecimal result = num
-- program terminates
∃ result, impl num = result ∧
-- return value satisfies spec
spec result

def precondition (num : Nat) : Prop :=
  True

instance instDecidablePrecond (num : Nat) : Decidable (precondition num) := by
  unfold precondition
  infer_instance

def postcondition (num : Nat) (result : String) :=
  1 ≤ num ∧ num ≤ 1000 ∧ (result.data.all (fun c => c.isLower)) →
    isValidRoman result ∧ romanToDecimal result = num

end Specs

section Impl

def implementation (num: Nat) : String :=
sorry

end Impl

section TestCases

def test1_num : Nat := 19
def test1_Expected : String := "xix"

def test2_num : Nat := 152
def test2_Expected : String := "clii"

def test3_num : Nat := 426
def test3_Expected : String := "cdxxvi"

end TestCases

set_option maxHeartbeats 500000

def uniqueness_test1 (result : String) :
  result ≠ test1_Expected →
  ¬ postcondition test1_num result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  plausible'_mut (seeds := #[test1_Expected]) (config := { numInst := 100000 })
