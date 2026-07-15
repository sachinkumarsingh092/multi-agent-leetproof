/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 6f9e5cb1-b3d0-4833-ba49-4f2dc043efe7

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (s : String) : VerinaSpec.allCharactersSame_precond s ↔ LLMSpec.precondition s

- theorem postcondition_equiv (s : String) (result : Bool) : LLMSpec.precondition s →
  (VerinaSpec.allCharactersSame_postcond s result ↔ LLMSpec.postcondition s result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def allCharactersSame_precond (s : String) : Prop :=
  True

def allCharactersSame_postcond (s : String) (result: Bool) :=
  let cs := s.toList
  (result → List.Pairwise (· = ·) cs) ∧
  (¬ result → (cs ≠ [] ∧ cs.any (fun x => x ≠ cs[0]!)))

end VerinaSpec

namespace LLMSpec

-- Helper predicate: all characters of a list are identical.
-- This is formulated without committing to any particular algorithm:
-- either the list is empty, or all elements in the tail equal the head.
-- (For a singleton list, the tail is empty, so the condition holds.)
def allCharsIdenticalList (lst : List Char) : Prop :=
  match lst with
  | [] => True
  | c :: cs => ∀ (d : Char), d ∈ cs → d = c

def precondition (s : String) : Prop :=
  True

def postcondition (s : String) (result : Bool) : Prop :=
  (result = true ↔ allCharsIdenticalList s.data)

end LLMSpec

section Proof

theorem precondition_equiv (s : String) : VerinaSpec.allCharactersSame_precond s ↔ LLMSpec.precondition s := by
  -- Since both preconditions are defined as True, the equivalence holds trivially.
  simp [VerinaSpec.allCharactersSame_precond, LLMSpec.precondition]

theorem postcondition_equiv (s : String) (result : Bool) : LLMSpec.precondition s →
  (VerinaSpec.allCharactersSame_postcond s result ↔ LLMSpec.postcondition s result) := by
  simp [VerinaSpec.allCharactersSame_postcond, LLMSpec.postcondition];
  -- By definition of `allCharsIdenticalList`, if `result = true`, then all elements in `s.data` are equal to the first element.
  have h_all_eq : (s.data.Pairwise (· = ·)) ↔ (s.data = [] ∨ ∀ x ∈ s.data.tail, x = s.data.head!) := by
    -- By definition of pairwise equality, if the list is pairwise equal, then either it is empty or all elements are equal to the head.
    induction' s.data with x xs ih;
    · grind;
    · cases xs <;> simp_all +decide [ List.pairwise_cons ];
      grind +ring;
  -- By combining the results from h_all_eq and the definitions of postconditions, we can conclude the equivalence.
  simp [h_all_eq, LLMSpec.allCharsIdenticalList];
  cases s.data <;> simp +decide [ * ];
  cases result <;> simp +decide [ * ]

end Proof