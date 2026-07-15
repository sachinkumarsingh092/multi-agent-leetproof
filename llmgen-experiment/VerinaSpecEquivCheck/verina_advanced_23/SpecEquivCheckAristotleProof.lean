/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 70b1d160-d592-4931-98cf-f4539e671815

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (n : Int) : VerinaSpec.isPowerOfTwo_precond n ↔ LLMSpec.precondition n

- theorem postcondition_equiv (n : Int) (result : Bool) : LLMSpec.precondition n →
  (VerinaSpec.isPowerOfTwo_postcond n result ↔ LLMSpec.postcondition n result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def isPowerOfTwo_precond (n : Int) : Prop :=
  True

def pow (base : Int) (exp : Nat) : Int :=
  match exp with
  | 0 => 1
  | n+1 => base * pow base n

def isPowerOfTwo_postcond (n : Int) (result: Bool) : Prop :=
  if result then ∃ (x : Nat), (pow 2 x = n) ∧ (n > 0)
  else ¬ (∃ (x : Nat), (pow 2 x = n) ∧ (n > 0))

end VerinaSpec

namespace LLMSpec

-- A mathematical predicate describing when an integer is a (positive) power of two.
-- We use a natural exponent because integer exponentiation `(^)` takes a `Nat` exponent.
def IsPowerOfTwo (n : Int) : Prop :=
  (0 < n) ∧ (∃ k : Nat, n = (2 : Int) ^ k)

def precondition (n : Int) : Prop :=
  True

def postcondition (n : Int) (result : Bool) : Prop :=
  (result = true ↔ IsPowerOfTwo n)

end LLMSpec

section Proof

theorem precondition_equiv (n : Int) : VerinaSpec.isPowerOfTwo_precond n ↔ LLMSpec.precondition n := by
  -- Since both preconditions are True, their equivalence is trivial.
  simp [VerinaSpec.isPowerOfTwo_precond, LLMSpec.precondition]

theorem postcondition_equiv (n : Int) (result : Bool) : LLMSpec.precondition n →
  (VerinaSpec.isPowerOfTwo_postcond n result ↔ LLMSpec.postcondition n result) := by
  -- Unfold the definitions of the postconditions.
  simp [LLMSpec.postcondition, VerinaSpec.isPowerOfTwo_postcond];
  -- By definition of `VerinaSpec.pow`, we know that `VerinaSpec.pow 2 x = 2^x`.
  have h_pow : ∀ x : ℕ, VerinaSpec.pow 2 x = 2 ^ x := by
    intro x; induction x <;> simp +decide [ *, pow_succ' ] ;
    exact?;
  -- By definition of `IsPowerOfTwo`, we know that `IsPowerOfTwo n` is equivalent to `∃ x : ℕ, 2^x = n ∧ 0 < n`.
  simp [LLMSpec.IsPowerOfTwo];
  grind +ring

end Proof