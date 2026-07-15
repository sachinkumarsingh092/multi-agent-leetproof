/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 6a5c7ed1-c293-46b2-8086-3a2d427c6c0c

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (n : Nat) (d : Nat) : VerinaSpec.countSumDivisibleBy_precond n d ↔ LLMSpec.precondition n d

- theorem postcondition_equiv (n : Nat) (d : Nat) (result : Nat) : LLMSpec.precondition n d →
  (VerinaSpec.countSumDivisibleBy_postcond n d result ↔ LLMSpec.postcondition n d result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def sumOfDigits (x : Nat) : Nat :=
  let rec go (n acc : Nat) : Nat :=
    if n = 0 then acc
    else go (n / 10) (acc + (n % 10))
  go x 0

def countSumDivisibleBy_precond (n : Nat) (d : Nat) : Prop :=
  d > 0

def isSumDivisibleBy (x : Nat) (d:Nat) : Bool :=
  (sumOfDigits x) % d = 0

def countSumDivisibleBy_postcond (n : Nat) (d : Nat) (result: Nat) : Prop :=
  (List.length (List.filter (fun x => x < n ∧ (sumOfDigits x) % d = 0) (List.range n))) - result = 0 ∧
  result ≤ (List.length (List.filter (fun x => x < n ∧ (sumOfDigits x) % d = 0) (List.range n)))

end VerinaSpec

namespace LLMSpec

-- Helper: sum of base-10 digits of a natural number.
-- Mathlib's `Nat.digits 10 x` gives the base-10 digits of `x` (least significant digit first).
-- Summing the digit list yields the digit sum.
def digitSum10 (x : Nat) : Nat :=
  (Nat.digits 10 x).sum

-- Boolean predicate: digit sum is divisible by d (using modulo).
-- We keep this as Bool so it can be used directly with `Finset.filter`.
def digitSumDivisibleB (x : Nat) (d : Nat) : Bool :=
  (digitSum10 x % d) == 0

def precondition (n : Nat) (d : Nat) : Prop :=
  d > 0

def postcondition (n : Nat) (d : Nat) (result : Nat) : Prop :=
  -- `result` is the number of naturals x with x < n and digitSum10(x) divisible by d.
  result = ((Finset.range n).filter (fun (x : Nat) => digitSumDivisibleB x d)).card

end LLMSpec

section Proof

theorem precondition_equiv (n : Nat) (d : Nat) : VerinaSpec.countSumDivisibleBy_precond n d ↔ LLMSpec.precondition n d := by
  -- The preconditions are identical, so the equivalence holds trivially.
  simp [VerinaSpec.countSumDivisibleBy_precond, LLMSpec.precondition]

theorem postcondition_equiv (n : Nat) (d : Nat) (result : Nat) : LLMSpec.precondition n d →
  (VerinaSpec.countSumDivisibleBy_postcond n d result ↔ LLMSpec.postcondition n d result) := by
  -- Since the sum of the digits of x is the same as the sum of the digits of x, the two postconditions are equivalent.
  simp [VerinaSpec.countSumDivisibleBy_postcond, LLMSpec.postcondition];
  -- By definition of sumOfDigits and digitSum10, we know that they are equal for all x.
  have h_sum_eq_digitSum : ∀ x, VerinaSpec.sumOfDigits x = LLMSpec.digitSum10 x := by
    -- By definition of `sumOfDigits`, we can prove that it is equal to `digitSum10` by induction on `x`.
    have h_sum_eq_digitSum_induction : ∀ x acc, VerinaSpec.sumOfDigits.go x acc = acc + (Nat.digits 10 x).sum := by
      intro x acc; induction' x using Nat.strong_induction_on with x ih generalizing acc; rcases x with ( _ | _ | x ) <;> simp_all +arith +decide;
      · unfold VerinaSpec.sumOfDigits.go; aesop;
      · unfold VerinaSpec.sumOfDigits.go; simp +arith +decide [ ih ] ;
      · unfold VerinaSpec.sumOfDigits.go; simp +arith +decide [ ih ] ; ring;
        grind +ring;
    exact fun x => by simpa using h_sum_eq_digitSum_induction x 0;
  simp_all +decide [ LLMSpec.digitSumDivisibleB ];
  simp +decide [ Finset.filter ];
  rw [ show ( Multiset.filter ( fun x => LLMSpec.digitSum10 x % d = 0 ) ( Multiset.range n ) ) = Multiset.ofList ( List.filter ( fun x => Decidable.decide ( x < n ) && Decidable.decide ( LLMSpec.digitSum10 x % d = 0 ) ) ( List.range n ) ) from ?_ ];
  · exact fun _ => ⟨ fun h => by linarith! [ Nat.sub_add_cancel h.2 ], fun h => ⟨ Nat.sub_eq_zero_of_le <| by linarith! [ Nat.sub_add_cancel <| show result ≤ ( List.filter ( fun x => Decidable.decide ( x < n ) && Decidable.decide ( LLMSpec.digitSum10 x % d = 0 ) ) ( List.range n ) ).length from by linarith! ], by linarith! ⟩ ⟩;
  · refine' Multiset.coe_eq_coe.mpr _;
    -- Since the condition x < n is always true for elements in the list range n, the two filtered lists are identical.
    have h_eq : List.filter (fun x => LLMSpec.digitSum10 x % d = 0) (List.range n) = List.filter (fun x => x < n ∧ LLMSpec.digitSum10 x % d = 0) (List.range n) := by
      exact List.filter_congr fun x hx => by aesop;
    grind

end Proof