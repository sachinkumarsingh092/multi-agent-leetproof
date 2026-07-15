/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: a38e9e0d-1b4f-46a9-8888-b2cfd107896a

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (s : String) : VerinaSpec.reverseString_precond s ↔ LLMSpec.precondition s

- theorem postcondition_equiv (s : String) (result : String) : LLMSpec.precondition s →
  (VerinaSpec.reverseString_postcond s result ↔ LLMSpec.postcondition s result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def reverseString_precond (s : String) : Prop :=
  True

def reverseString_postcond (s : String) (result: String) : Prop :=
  result.length = s.length ∧ result.toList = s.toList.reverse

end VerinaSpec

namespace LLMSpec

-- We specify correctness using the list-of-characters view of strings.
-- Note: String.toList : String → List Char

def precondition (s : String) : Prop :=
  True

def postcondition (s : String) (result : String) : Prop :=
  let cs := s.toList
  let rs := result.toList
  rs.length = cs.length ∧
  ∀ (i : Nat), i < cs.length →
    rs[i]! = cs[cs.length - 1 - i]!

end LLMSpec

section Proof

theorem precondition_equiv (s : String) : VerinaSpec.reverseString_precond s ↔ LLMSpec.precondition s := by
  -- Since both preconditions are True, their equivalence is trivial.
  simp [VerinaSpec.reverseString_precond, LLMSpec.precondition]

theorem postcondition_equiv (s : String) (result : String) : LLMSpec.precondition s →
  (VerinaSpec.reverseString_postcond s result ↔ LLMSpec.postcondition s result) := by
  unfold VerinaSpec.reverseString_postcond LLMSpec.postcondition
  simp [List.length_reverse];
  -- To prove the equivalence, we can use the fact that the length of a list is preserved under reversal and that the elements are reversed in order.
  have h_equiv : ∀ (l1 l2 : List Char), l1.length = l2.length → (l1 = l2.reverse ↔ ∀ i < l1.length, l1[i]! = l2[l2.length - 1 - i]!) := by
    -- To prove the equivalence, we can use the fact that two lists are equal if and only if their elements are equal at every index.
    intro l1 l2 h_len
    constructor;
    · grind +ring;
    · intro h_eq
      apply List.ext_get
      simp [h_len];
      grind;
  specialize h_equiv result.data s.data ; aesop

end Proof