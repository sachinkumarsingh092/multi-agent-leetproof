import SpecPBTResult.Clever.CleverAllImports
import Velvet.Std
import Extensions.Testing
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem: problem_89

section Specs

register_specdef_allow_recursion

def problem_spec
-- function signature
(implementation: String → String)
-- inputs
(str: String) :=
-- spec
let spec (result : String) :=
  result.data.all (fun c => c.isLower) →
  result.length = str.length ∧
  (∀ i, i < str.length →
    let c := str.data[i]!
    let c' := result.data[i]!
    ((c'.toNat - 97) + 2 * 2) % 26 = (c.toNat - 97))
-- program termination
∃ result,
  implementation str = result ∧
  spec result

def precondition (str : String) : Prop :=
  True

instance instDecidablePrecond (str : String) : Decidable (precondition str) := by
  unfold precondition
  infer_instance

def postcondition (str : String) (result : String) :=
  result.data.all (fun c => c.isLower) →
    result.length = str.length ∧
    (∀ i, i < str.length →
      let c := str.data[i]!
      let c' := result.data[i]!
      ((c'.toNat - 97) + 2 * 2) % 26 = (c.toNat - 97))

end Specs

section Impl

def implementation (str: String) : String :=
sorry

end Impl

section TestCases

def test1_str : String := "hi"
def test1_Expected : String := "lm"

def test2_str : String := "asdfghjkl"
def test2_Expected : String := "ewhjklnop"

def test3_str : String := "gf"
def test3_Expected : String := "kj"

def test4_str : String := "et"
def test4_Expected : String := "ix"

end TestCases

set_option maxHeartbeats 500000

def uniqueness_test1 (result : String) :
  result ≠ test1_Expected →
  ¬ postcondition test1_str result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  plausible'_mut (seeds := #[test1_Expected]) (config := { numInst := 100000 })
