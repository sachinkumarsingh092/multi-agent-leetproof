/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 45b9dbc6-cb04-4cc6-b215-c431e28352f9

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (arr : Array Int) : VerinaSpec.uniqueProduct_precond arr ↔ LLMSpec.precondition arr

- theorem postcondition_equiv (arr : Array Int) (result : Int) : LLMSpec.precondition arr →
  (VerinaSpec.uniqueProduct_postcond arr result ↔ LLMSpec.postcondition arr result)
-/

import Mathlib.Tactic

import Std.Data.HashSet


namespace VerinaSpec

def uniqueProduct_precond (arr : Array Int) : Prop :=
  True

def uniqueProduct_postcond (arr : Array Int) (result: Int) :=
  result - (arr.toList.eraseDups.foldl (· * ·) 1) = 0 ∧
  (arr.toList.eraseDups.foldl (· * ·) 1) - result = 0

end VerinaSpec

namespace LLMSpec

-- Convert an array to a finset of the distinct values it contains.
-- This is a specification-level abstraction of “consider each unique integer only once”.
-- We avoid using `Array.toList` in specs.
def arrToFinset (arr : Array Int) : Finset Int :=
  arr.foldl (fun (s : Finset Int) (x : Int) => insert x s) (∅)

-- No input restrictions.
def precondition (arr : Array Int) : Prop :=
  True

-- The result equals the product of all distinct elements of the array.
-- `Finset.prod` uses `1` as the identity, hence the empty-array case yields `1`.
def postcondition (arr : Array Int) (result : Int) : Prop :=
  result = (arrToFinset arr).prod (fun (x : Int) => x)

end LLMSpec

section Proof

theorem precondition_equiv (arr : Array Int) : VerinaSpec.uniqueProduct_precond arr ↔ LLMSpec.precondition arr := by
  -- Since both preconditions are True, their equivalence is trivial.
  simp [VerinaSpec.uniqueProduct_precond, LLMSpec.precondition]

theorem postcondition_equiv (arr : Array Int) (result : Int) : LLMSpec.precondition arr →
  (VerinaSpec.uniqueProduct_postcond arr result ↔ LLMSpec.postcondition arr result) := by
  unfold LLMSpec.precondition VerinaSpec.uniqueProduct_postcond LLMSpec.postcondition;
  rw [ sub_eq_zero, eq_comm ];
  rw [ eq_comm, show LLMSpec.arrToFinset arr = arr.toList.eraseDups.toFinset from ?_ ];
  · rw [ List.prod_toFinset ];
    · rw [ List.prod_eq_foldl ] ; aesop;
    · -- By definition of `List.eraseDupsBy.loop`, the resulting list is nodup.
      have h_nodup : ∀ (l : List ℤ) (acc : List ℤ), List.Nodup acc → List.Nodup (List.eraseDupsBy.loop (fun x1 x2 => x1 == x2) l acc) := by
        intros l acc hacc; induction' l with x l ih generalizing acc <;> simp_all +decide [ List.eraseDupsBy.loop ] ;
        cases h : acc.any fun x2 => x == x2 <;> simp_all +decide [ List.eraseDupsBy.loop ];
        grind;
      exact h_nodup _ _ ( by simp +decide );
  · unfold LLMSpec.arrToFinset;
    induction arr using Array.recOn ; simp +decide [ * ];
    induction' ‹List ℤ› using List.reverseRecOn with x xs ih <;> simp +decide [ *, List.eraseDups_append ];
    by_cases h : xs ∈ x <;> simp_all +decide [ List.removeAll ];
    · have h_erase_dups : ∀ {l : List ℤ}, xs ∈ l → xs ∈ l.eraseDups := by
        intros l hl; induction' l using List.reverseRecOn with l ih <;> simp_all +decide [ List.eraseDups_cons ] ;
        grind;
      exact h_erase_dups h;
    · simp +decide [ Finset.ext_iff, List.eraseDups_cons ]

end Proof