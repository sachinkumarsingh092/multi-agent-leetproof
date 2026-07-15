/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 00a8877f-4102-41ac-abe7-1189f29ef871

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (x : Nat) (y : Nat) : VerinaSpec.DivisionFunction_precond x y ↔ LLMSpec.precondition x y

- theorem postcondition_equiv (x : Nat) (y : Nat) (result : Int × Int) : LLMSpec.precondition x y →
  (VerinaSpec.DivisionFunction_postcond x y result ↔ LLMSpec.postcondition x y result)
-/

import Mathlib.Tactic

import Mathlib


namespace VerinaSpec

def DivisionFunction_precond (x : Nat) (y : Nat) : Prop :=
  True

def divMod (x y : Nat) : Int × Int :=
  let q : Int := Int.ofNat (x / y)
  let r : Int := Int.ofNat (x % y)
  (r, q)

def DivisionFunction_postcond (x : Nat) (y : Nat) (result: Int × Int) :=
  let (r, q) := result;
  (y = 0 → r = Int.ofNat x ∧ q = 0) ∧
  (y ≠ 0 → (q * Int.ofNat y + r = Int.ofNat x) ∧ (0 ≤ r ∧ r < Int.ofNat y) ∧ (0 ≤ q))

end VerinaSpec

namespace LLMSpec

-- Helper: view a Nat as an Int (explicitly).
def natToInt (n : Nat) : Int :=
  Int.ofNat n

-- Preconditions: all natural-number inputs are allowed.
def precondition (x : Nat) (y : Nat) : Prop :=
  True

-- Postcondition: (r, q) follows Euclidean division when y ≠ 0; otherwise returns (x, 0) in Int.
def postcondition (x : Nat) (y : Nat) (result : Int × Int) : Prop :=
  if y = 0 then
    result = (natToInt x, (0 : Int))
  else
    let r : Int := result.1
    let q : Int := result.2
    (q * natToInt y + r = natToInt x) ∧
    (0 ≤ r) ∧ (r < natToInt y) ∧
    (0 ≤ q)

end LLMSpec

section Proof

theorem precondition_equiv (x : Nat) (y : Nat) : VerinaSpec.DivisionFunction_precond x y ↔ LLMSpec.precondition x y := by
  -- Since both preconditions are True, their equivalence is trivial.
  simp [VerinaSpec.DivisionFunction_precond, LLMSpec.precondition]

theorem postcondition_equiv (x : Nat) (y : Nat) (result : Int × Int) : LLMSpec.precondition x y →
  (VerinaSpec.DivisionFunction_postcond x y result ↔ LLMSpec.postcondition x y result) := by
  -- By definition of postcondition, we need to consider two cases: when y is zero and when y is not zero.
  by_cases hy : y = 0 <;> simp [hy, VerinaSpec.DivisionFunction_postcond, LLMSpec.postcondition];
  · -- By definition of pairs, if result.1 = x and result.2 = 0, then result must be (x, 0). Conversely, if result is (x, 0), then obviously result.1 is x and result.2 is 0.
    simp [Prod.ext_iff];
    exact?;
  · tauto

end Proof