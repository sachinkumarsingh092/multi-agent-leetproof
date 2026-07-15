import Mathlib.Tactic

namespace VerinaSpec


def binaryToDecimal_precond (digits : List Nat) : Prop :=
  digits.all (fun d => d = 0 ∨ d = 1)

def binaryToDecimal_postcond (digits : List Nat) (result: Nat) : Prop :=
  result - List.foldl (λ acc bit => acc * 2 + bit) 0 digits = 0 ∧
  List.foldl (λ acc bit => acc * 2 + bit) 0 digits - result = 0

end VerinaSpec

namespace LLMSpec

-- Helper: digit validity predicate
def isBitDigit (d : Nat) : Prop := d = 0 ∨ d = 1

-- Helper: interpret a digit as a Bool bit (true iff digit is 1)
def digitToBit (d : Nat) : Bool := (d == 1)

-- Helper: kth digit from the right (least significant side), using total indexing.
-- This is intended to be used only under the guard k < digits.length.
def digitFromRight (digits : List Nat) (k : Nat) : Nat :=
  digits.get! (digits.length - 1 - k)

def precondition (digits : List Nat) : Prop :=
  ∀ (d : Nat), d ∈ digits → isBitDigit d

def postcondition (digits : List Nat) (result : Nat) : Prop :=
  (∀ (k : Nat), k < digits.length → result.testBit k = digitToBit (digitFromRight digits k)) ∧
  (∀ (k : Nat), digits.length ≤ k → result.testBit k = false)

end LLMSpec

section Proof

theorem precondition_equiv (digits : List Nat) :
  VerinaSpec.binaryToDecimal_precond digits ↔ LLMSpec.precondition digits := by
  sorry

theorem postcondition_equiv (digits : List Nat) (result: Nat) :
  LLMSpec.precondition digits →
  (VerinaSpec.binaryToDecimal_postcond digits result ↔ LLMSpec.postcondition digits result) := by
  sorry

end Proof
