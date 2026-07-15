/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 7943b9f3-ff06-4864-89c4-ae76fcf0dd3b

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Int) (b : Int) (c : Int) : VerinaSpec.maxOfThree_precond a b c ↔ LLMSpec.precondition a b c

- theorem postcondition_equiv (a : Int) (b : Int) (c : Int) (result : Int) : LLMSpec.precondition a b c →
  (VerinaSpec.maxOfThree_postcond a b c result ↔ LLMSpec.postcondition a b c result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def maxOfThree_precond (a : Int) (b : Int) (c : Int) : Prop :=
  True

def maxOfThree_postcond (a : Int) (b : Int) (c : Int) (result: Int) : Prop :=
  (result >= a ∧ result >= b ∧ result >= c) ∧ (result = a ∨ result = b ∨ result = c)

end VerinaSpec

namespace LLMSpec

-- No special preconditions are required for Int inputs.
def precondition (a : Int) (b : Int) (c : Int) : Prop :=
  True

-- Postcondition: result is the least upper bound of {a,b,c} and is achieved by one of them.
def postcondition (a : Int) (b : Int) (c : Int) (result : Int) : Prop :=
  (a ≤ result) ∧
  (b ≤ result) ∧
  (c ≤ result) ∧
  (result = a ∨ result = b ∨ result = c) ∧
  (∀ x : Int, a ≤ x → b ≤ x → c ≤ x → result ≤ x)

end LLMSpec

section Proof

theorem precondition_equiv (a : Int) (b : Int) (c : Int) : VerinaSpec.maxOfThree_precond a b c ↔ LLMSpec.precondition a b c := by
  -- Since both preconditions are True, their equivalence is trivial.
  simp [VerinaSpec.maxOfThree_precond, LLMSpec.precondition]

theorem postcondition_equiv (a : Int) (b : Int) (c : Int) (result : Int) : LLMSpec.precondition a b c →
  (VerinaSpec.maxOfThree_postcond a b c result ↔ LLMSpec.postcondition a b c result) := by
  -- To prove the equivalence, we can show that the conditions are equivalent by using the fact that if result is the maximum, then it must be the least upper bound, and vice versa.
  intros h_pre
  apply Iff.intro;
  · -- To prove the forward direction, assume the VerinaSpec conditions hold. We need to show that the LLMSpec conditions hold.
    intro hverina
    obtain ⟨hge, hachieved⟩ := hverina
    exact ⟨hge.left, hge.right.left, hge.right.right, hachieved, fun x hx₁ hx₂ hx₃ => by
      grind +ring⟩;
  · -- By definition of LLMSpec.postcondition, we know that result is an upper bound and is achieved by one of a, b, or c.
    intro h_post
    obtain ⟨h_upper, h_achieved⟩ := h_post;
    exact ⟨ ⟨ h_upper, h_achieved.1, h_achieved.2.1 ⟩, h_achieved.2.2.1 ⟩

end Proof