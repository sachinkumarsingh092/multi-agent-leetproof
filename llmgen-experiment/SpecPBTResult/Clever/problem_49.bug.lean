import SpecPBTResult.Clever.CleverAllImports
import Velvet.Std
import Extensions.Testing
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem: problem_49

section Specs

register_specdef_allow_recursion

def problem_spec
-- function signature
(implementation: Nat → Nat → Nat)
-- inputs
(n p: Nat) :=
-- spec
let spec (result: Nat) :=
0 < p ∧
result < p ∧
(∃ k : Nat, p * k + result = Nat.pow 2 n)
-- program termination
∃ result, implementation n p = result ∧
spec result

def precondition (n : Nat) (p : Nat) : Prop :=
  True

instance instDecidablePrecond (n : Nat) (p : Nat) : Decidable (precondition n p) := by
  unfold precondition
  infer_instance

def postcondition (n : Nat) (p : Nat) (result : Nat) :=
  0 < p ∧
  result < p ∧
  (∃ k : Nat, p * k + result = Nat.pow 2 n)

end Specs

section Impl

def implementation (n p: Nat) : Nat :=
sorry

end Impl

section TestCases

def test1_n : Nat := 3
def test1_p : Nat := 5
def test1_Expected : Nat := 3

def test2_n : Nat := 1101
def test2_p : Nat := 101
def test2_Expected : Nat := 2

def test3_n : Nat := 0
def test3_p : Nat := 101
def test3_Expected : Nat := 0

def test4_n : Nat := 100
def test4_p : Nat := 101
def test4_Expected : Nat := 1

end TestCases

set_option maxHeartbeats 500000

def uniqueness_test3 (result : Nat) :
  result ≠ test3_Expected →
  ¬ postcondition test3_n test3_p result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  plausible'_mut (seeds := #[test3_Expected]) (config := { numInst := 100000 })
