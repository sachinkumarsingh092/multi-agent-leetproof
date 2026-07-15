import Mathlib.Tactic

namespace VerinaSpec


def listToNat : List Nat → Nat
| []       => 0
| d :: ds  => d + 10 * listToNat ds

def addTwoNumbers_precond (l1 : List Nat) (l2 : List Nat) : Prop :=
  l1.length > 0 ∧ l2.length > 0 ∧
  (∀ d ∈ l1, d < 10) ∧ (∀ d ∈ l2, d < 10) ∧
  (l1.getLast! ≠ 0 ∨ l1 = [0]) ∧
  (l2.getLast! ≠ 0 ∨ l2 = [0])

def addTwoNumbers_postcond (l1 : List Nat) (l2 : List Nat) (result: List Nat) : Prop :=
  listToNat result = listToNat l1 + listToNat l2 ∧
  (∀ d ∈ result, d < 10) ∧
  (result.getLast! ≠ 0 ∨ (l1 = [0] ∧ l2 = [0] ∧ result = [0]))

end VerinaSpec

namespace LLMSpec

-- A digit list is valid (base 10) iff all elements are < 10.
-- We use strict inequality (< 10) because digits are naturals.
def allDigitsBase10 (l : List Nat) : Prop :=
  ∀ (d : Nat), d ∈ l → d < 10

-- The base-10 value of a little-endian (reversed) digit list.
-- Mathlib's Nat.ofDigits uses the little-endian convention.
def valueBase10LE (l : List Nat) : Nat :=
  Nat.ofDigits 10 l

-- Canonicality for a base-10 little-endian digit list:
-- it is non-empty, all digits are valid, and it has no unnecessary most-significant zeros.
-- We treat 0 specially: the unique canonical representation is [0].
def canonicalBase10LE (l : List Nat) : Prop :=
  l ≠ [] ∧
  allDigitsBase10 l ∧
  ((valueBase10LE l = 0) ↔ (l = [0])) ∧
  (valueBase10LE l ≠ 0 → l.getLast? ≠ some 0)

-- Inputs are required to be non-empty and contain only decimal digits.
-- (We do not require canonical inputs; leading zeros are allowed in the most-significant positions.)
def precondition (l1 : List Nat) (l2 : List Nat) : Prop :=
  l1 ≠ [] ∧
  l2 ≠ [] ∧
  allDigitsBase10 l1 ∧
  allDigitsBase10 l2

-- The output must be a canonical base-10 little-endian digit list representing the sum.
def postcondition (l1 : List Nat) (l2 : List Nat) (result : List Nat) : Prop :=
  canonicalBase10LE result ∧
  valueBase10LE result = valueBase10LE l1 + valueBase10LE l2

end LLMSpec

section Proof

theorem precondition_equiv (l1 : List Nat) (l2 : List Nat) :
  VerinaSpec.addTwoNumbers_precond l1 l2 ↔ LLMSpec.precondition l1 l2 := by
  sorry

theorem postcondition_equiv (l1 : List Nat) (l2 : List Nat) (result: List Nat) :
  LLMSpec.precondition l1 l2 →
  (VerinaSpec.addTwoNumbers_postcond l1 l2 result ↔ LLMSpec.postcondition l1 l2 result) := by
  sorry

end Proof
