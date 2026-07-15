/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: f6ffe24c-dfdc-4e12-b2b6-ed4aec943d65

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (n : Int) : VerinaSpec.isItEight_precond n ↔ LLMSpec.precondition n

- theorem postcondition_equiv (n : Int) (result : Bool) : LLMSpec.precondition n →
  (VerinaSpec.isItEight_postcond n result ↔ LLMSpec.postcondition n result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def isItEight_precond (n : Int) : Prop :=
  True

def isItEight_postcond (n : Int) (result: Bool) : Prop :=
  let absN := Int.natAbs n;
  (n % 8 == 0 ∨ ∃ i, absN / (10^i) % 10 == 8) ↔ result

end VerinaSpec

namespace LLMSpec

-- Helper predicate: |n| has a decimal digit equal to 8.
-- We use Nat.digits 10 on the absolute value (as a Nat) to get base-10 digits.

def hasDigit8 (n : Int) : Prop :=
  (8 : Nat) ∈ Nat.digits 10 n.natAbs

-- Helper predicate: n is divisible by 8.
-- Int's `%` is Euclidean remainder (Int.emod), so this works uniformly for negative integers.

def divisibleBy8 (n : Int) : Prop :=
  n % (8 : Int) = 0

-- No input restrictions.

def precondition (n : Int) : Prop :=
  True

-- Postcondition: result is true iff n is divisible by 8 or has an 8 digit.
-- We avoid `decide` to not require a `Decidable` instance for the proposition.

def postcondition (n : Int) (result : Bool) : Prop :=
  (result = true ↔ (divisibleBy8 n ∨ hasDigit8 n))

end LLMSpec

section Proof

theorem precondition_equiv (n : Int) : VerinaSpec.isItEight_precond n ↔ LLMSpec.precondition n := by
  -- Since both preconditions are True, their equivalence is trivial.
  simp [VerinaSpec.isItEight_precond, LLMSpec.precondition]

theorem postcondition_equiv (n : Int) (result : Bool) : LLMSpec.precondition n →
  (VerinaSpec.isItEight_postcond n result ↔ LLMSpec.postcondition n result) := by
  simp +decide [ LLMSpec.precondition, VerinaSpec.isItEight_postcond, LLMSpec.postcondition ];
  -- By definition of `hasDigit8`, we know that `hasDigit8 n` is true if and only if there exists an `i` such that `(n.natAbs / 10^i) % 10 = 8`.
  have h_hasDigit8 : (8 : ℕ) ∈ Nat.digits 10 n.natAbs ↔ ∃ i, (n.natAbs / 10^i) % 10 = 8 := by
    constructor;
    · intro h
      obtain ⟨i, hi⟩ : ∃ i, (Nat.digits 10 n.natAbs).get! i = 8 := by
        obtain ⟨ i, hi ⟩ := List.mem_iff_get.mp h; use i; aesop;
      use i;
      have h_digit : ∀ (n : ℕ) (i : ℕ), (Nat.digits 10 n).get! i = (n / 10^i) % 10 := by
        intro n i; induction' i with i ih generalizing n <;> simp +decide [ Nat.pow_succ', ← Nat.div_div_eq_div_mul ] ;
        · cases n <;> simp +decide [ Nat.mod_eq_of_lt ];
        · rcases n <;> simp_all +decide [ Nat.div_div_eq_div_mul ];
      rw [ ← h_digit, hi ];
    · rintro ⟨ i, hi ⟩;
      have h_digit : ∀ m i : ℕ, (m / 10^i) % 10 = 8 → 8 ∈ Nat.digits 10 m := by
        intro m i hi; induction' i with i ih generalizing m <;> simp_all +decide [ Nat.pow_succ', ← Nat.div_div_eq_div_mul ] ;
        · cases m <;> simp_all +decide;
        · rcases m <;> simp_all +decide [ Nat.div_div_eq_div_mul ];
      exact h_digit _ _ hi;
  unfold LLMSpec.divisibleBy8 LLMSpec.hasDigit8; aesop;

end Proof