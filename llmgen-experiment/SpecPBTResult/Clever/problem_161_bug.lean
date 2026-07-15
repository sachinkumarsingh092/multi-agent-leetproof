import SpecPBTResult.Clever.CleverAllImports
import Velvet.Std
import Extensions.Testing
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem: problem_161

section Specs

register_specdef_allow_recursion

def problem_spec
-- function signature
(impl: String → String)
-- inputs
(string : String) :=
-- spec
let spec (result: String) :=
result.length = string.length ∧
let hasNoAlphabet := string.all (λ c => not (c.isAlpha));
(hasNoAlphabet →
  result.toList = string.toList.reverse) ∧
(hasNoAlphabet = false →
  ∀ i, i < string.length →
  let c := string.get! ⟨i⟩;
  (c.isAlpha → ((c.isLower → c.toUpper = result.get! ⟨i⟩) ∨
              (c.isUpper → c.toLower = result.get! ⟨i⟩))) ∧
  (¬ c.isAlpha → c = result.get! ⟨i⟩))
-- program terminates
∃ result, impl string = result ∧
-- return value satisfies spec
spec result

def precondition (string : String) : Prop :=
  True

instance instDecidablePrecond (string : String) : Decidable (precondition string) := by
  unfold precondition
  infer_instance

def postcondition (string : String) (result : String) :=
  result.length = string.length ∧
  let hasNoAlphabet := string.all (λ c => not (c.isAlpha));
  (hasNoAlphabet →
    result.toList = string.toList.reverse) ∧
  (hasNoAlphabet = false →
    ∀ i, i < string.length →
    let c := string.get! ⟨i⟩;
    (c.isAlpha → ((c.isLower → c.toUpper = result.get! ⟨i⟩) ∨
                (c.isUpper → c.toLower = result.get! ⟨i⟩))) ∧
    (¬ c.isAlpha → c = result.get! ⟨i⟩))

end Specs

section Impl

def implementation (s: String) : String :=
sorry

end Impl

section TestCases

def test1_s : String := "1234"
def test1_Expected : String := "4321"

def test2_s : String := "ab"
def test2_Expected : String := "AB"

def test3_s : String := "#a@C"
def test3_Expected : String := "#A@c"

end TestCases

set_option maxHeartbeats 500000

def uniqueness_test2' (result : String) :
  result ≠ test2_Expected →
  ¬ postcondition test2_s result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test2_Expected]) (config := { numInst := 100000 })
