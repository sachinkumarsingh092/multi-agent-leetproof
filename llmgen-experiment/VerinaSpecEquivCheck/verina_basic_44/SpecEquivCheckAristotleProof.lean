/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 57faad66-bbd7-421f-be0d-3db463a4d118

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int) : VerinaSpec.isOddAtIndexOdd_precond a ↔ LLMSpec.precondition a

- theorem postcondition_equiv (a : Array Int) (result : Bool) : LLMSpec.precondition a →
  (VerinaSpec.isOddAtIndexOdd_postcond a result ↔ LLMSpec.postcondition a result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def isOdd (n : Int) : Bool :=
  n % 2 == 1

def isOddAtIndexOdd_precond (a : Array Int) : Prop :=
  True

def isOddAtIndexOdd_postcond (a : Array Int) (result: Bool) :=
  result ↔ (∀ i, (hi : i < a.size) → isOdd i → isOdd (a[i]))

end VerinaSpec

namespace LLMSpec

-- Helper predicate: all elements at odd indices are odd.
-- We express index oddness using a simple modular condition on Nat to avoid relying on `Nat.Odd`.
-- For values, we use `Odd` on `Int`.

def oddIndex (i : Nat) : Prop :=
  i % 2 = 1

def oddIndicesHoldOdd (a : Array Int) : Prop :=
  ∀ (i : Nat), i < a.size → oddIndex i → Odd (a[i]!)

def precondition (a : Array Int) : Prop :=
  True

def postcondition (a : Array Int) (result : Bool) : Prop :=
  (result = true ↔ oddIndicesHoldOdd a)

end LLMSpec

section Proof

theorem precondition_equiv (a : Array Int) : VerinaSpec.isOddAtIndexOdd_precond a ↔ LLMSpec.precondition a := by
  -- Since both preconditions are True, they are trivially equivalent.
  simp [VerinaSpec.isOddAtIndexOdd_precond, LLMSpec.precondition]

theorem postcondition_equiv (a : Array Int) (result : Bool) : LLMSpec.precondition a →
  (VerinaSpec.isOddAtIndexOdd_postcond a result ↔ LLMSpec.postcondition a result) := by
  unfold VerinaSpec.isOddAtIndexOdd_postcond LLMSpec.postcondition;
  -- Since `VerinaSpec.isOdd` and `Odd` are equivalent for integers, the postconditions are equivalent.
  have h_equiv : ∀ (n : ℤ), VerinaSpec.isOdd n ↔ Odd n := by
    -- By definition of `isOdd`, we know that `isOdd n` is true if and only if `n % 2 == 1`.
    simp [VerinaSpec.isOdd];
    exact?;
  -- Since `a[i]!` and `a[i]` are equivalent in this context, the two postconditions are equivalent.
  simp [LLMSpec.oddIndicesHoldOdd];
  simp +decide [ LLMSpec.oddIndex ];
  grind +ring

end Proof