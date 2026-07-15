/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: b49ec552-51cf-40c8-a06b-47af3ff3e355

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int) (offset : Int) : VerinaSpec.rotate_precond a offset ↔ LLMSpec.precondition a offset

- theorem postcondition_equiv (a : Array Int) (offset : Int) (result : Array Int) : LLMSpec.precondition a offset →
  (VerinaSpec.rotate_postcond a offset result ↔ LLMSpec.postcondition a offset result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def rotate_precond (a : Array Int) (offset : Int) : Prop :=
  offset ≥ 0

def rotateAux (a : Array Int) (offset : Int) (i : Nat) (len : Nat) (b : Array Int) : Array Int :=
  if i < len then
    let idx_int : Int := (Int.ofNat i + offset) % (Int.ofNat len)
    let idx_int_adjusted := if idx_int < 0 then idx_int + Int.ofNat len else idx_int
    let idx_nat : Nat := Int.toNat idx_int_adjusted
    let new_b := b.set! i (a[idx_nat]!)
    rotateAux a offset (i + 1) len new_b
  else b

def rotate_postcond (a : Array Int) (offset : Int) (result: Array Int) :=
  result.size = a.size ∧
  (∀ i : Nat, i < a.size →
    result[i]! = a[Int.toNat ((Int.ofNat i + offset) % (Int.ofNat a.size))]!)

end VerinaSpec

namespace LLMSpec

-- Helper: the effective (wrapped) rotation amount in Nat, when n = a.size.
-- For n = 0, this value is defined but not used by the postcondition.
def effectiveOffset (a : Array Int) (offset : Int) : Nat :=
  offset.toNat % a.size

def precondition (a : Array Int) (offset : Int) : Prop :=
  0 ≤ offset

def postcondition (a : Array Int) (offset : Int) (result : Array Int) : Prop :=
  (a.size = 0 → result.size = 0) ∧
  (a.size > 0 →
    result.size = a.size ∧
    (∀ (i : Nat), i < a.size →
      result[i]! = a[(i + effectiveOffset a offset) % a.size]!))

end LLMSpec

section Proof

theorem precondition_equiv (a : Array Int) (offset : Int) : VerinaSpec.rotate_precond a offset ↔ LLMSpec.precondition a offset := by
  -- The preconditions are equivalent because they both state that the offset is non-negative.
  simp [VerinaSpec.rotate_precond, LLMSpec.precondition]

theorem postcondition_equiv (a : Array Int) (offset : Int) (result : Array Int) : LLMSpec.precondition a offset →
  (VerinaSpec.rotate_postcond a offset result ↔ LLMSpec.postcondition a offset result) := by
  -- If the size of the array is zero, both postconditions are trivially true.
  by_cases h_size_zero : a.size = 0;
  · -- Since the size of the array is zero, both postconditions are trivially true.
    simp [h_size_zero, VerinaSpec.rotate_postcond, LLMSpec.postcondition];
  · -- Since the size of the array is not zero, both postconditions require the length to be equal to the original size and the elements to be shifted by the offset.
    simp [VerinaSpec.rotate_postcond, LLMSpec.postcondition, h_size_zero];
    -- Since the size of the array is not zero, the first part of the postcondition is already satisfied.
    intro h_precond
    simp [h_size_zero, LLMSpec.effectiveOffset];
    -- Since the size of the array is positive, the modulo operation will always give a valid index. Therefore, the two postconditions are equivalent because they both require the result array's size to be equal to the original size and each element to be shifted by the offset.
    simp [Nat.pos_iff_ne_zero, h_size_zero];
    cases offset <;> norm_cast at * ; aesop

end Proof