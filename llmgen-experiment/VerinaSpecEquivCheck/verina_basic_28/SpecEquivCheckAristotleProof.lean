/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 852f10e6-f37d-48e8-8069-250221079e5e

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (n : Nat) : VerinaSpec.isPrime_precond n ↔ LLMSpec.precondition n

- theorem postcondition_equiv (n : Nat) (result : Bool) : LLMSpec.precondition n →
  (VerinaSpec.isPrime_postcond n result ↔ LLMSpec.postcondition n result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def isPrime_precond (n : Nat) : Prop :=
  n ≥ 2

def isPrime_postcond (n : Nat) (result: Bool) :=
  (result → (List.range' 2 (n - 2)).all (fun k => n % k ≠ 0)) ∧
  (¬ result → (List.range' 2 (n - 2)).any (fun k => n % k = 0))

end VerinaSpec

namespace LLMSpec

-- We use Mathlib's canonical primality predicate on Nat.

def precondition (n : Nat) : Prop :=
  n ≥ 2

def postcondition (n : Nat) (result : Bool) : Prop :=
  (result = true ↔ Nat.Prime n)

end LLMSpec

section Proof

theorem precondition_equiv (n : Nat) : VerinaSpec.isPrime_precond n ↔ LLMSpec.precondition n := by
  -- The preconditions are the same, so the equivalence is trivial.
  simp [VerinaSpec.isPrime_precond, LLMSpec.precondition]

theorem postcondition_equiv (n : Nat) (result : Bool) : LLMSpec.precondition n →
  (VerinaSpec.isPrime_postcond n result ↔ LLMSpec.postcondition n result) := by
  -- By definition of `isPrime_postcond` and `postcondition`, we can show that they are equivalent under the given preconditions.
  intros h_precond
  simp [VerinaSpec.isPrime_postcond, LLMSpec.postcondition];
  rcases n with ( _ | _ | _ | n ) <;> simp_all +arith +decide [ Nat.prime_def_lt' ];
  · cases h_precond;
  · contradiction;
  · cases result <;> simp +arith +decide [ * ];
  · by_cases h : result = Bool.true <;> simp_all +decide [ Nat.dvd_iff_mod_eq_zero ];
    simp +decide only [and_assoc]

end Proof