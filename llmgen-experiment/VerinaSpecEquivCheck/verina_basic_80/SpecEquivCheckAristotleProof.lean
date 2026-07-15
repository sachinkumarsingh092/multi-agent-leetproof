/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 2e516360-6517-46b6-a587-612a401414d1

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int) (key : Int) : VerinaSpec.only_once_precond a key ↔ LLMSpec.precondition a key

- theorem postcondition_equiv (a : Array Int) (key : Int) (result : Bool) : LLMSpec.precondition a key →
  (VerinaSpec.only_once_postcond a key result ↔ LLMSpec.postcondition a key result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def only_once_precond (a : Array Int) (key : Int) : Prop :=
  True

def only_once_loop {T : Type} [DecidableEq T] (a : Array T) (key : T) (i keyCount : Nat) : Bool :=
  if i < a.size then
    match a[i]? with
    | some val =>
        let newCount := if val = key then keyCount + 1 else keyCount
        only_once_loop a key (i + 1) newCount
    | none => keyCount == 1
  else
    keyCount == 1

def count_occurrences {T : Type} [DecidableEq T] (a : Array T) (key : T) : Nat :=
  a.foldl (fun cnt x => if x = key then cnt + 1 else cnt) 0

def only_once_postcond (a : Array Int) (key : Int) (result: Bool) :=
  ((count_occurrences a key = 1) → result) ∧
  ((count_occurrences a key ≠ 1) → ¬ result)

end VerinaSpec

namespace LLMSpec

-- Helper definition: the key occurs exactly once iff its Array.count is 1.
def occursExactlyOnce (a : Array Int) (key : Int) : Prop :=
  a.count key = 1

def precondition (a : Array Int) (key : Int) : Prop :=
  True

def postcondition (a : Array Int) (key : Int) (result : Bool) : Prop :=
  (result = true ↔ occursExactlyOnce a key)

end LLMSpec

section Proof

theorem precondition_equiv (a : Array Int) (key : Int) : VerinaSpec.only_once_precond a key ↔ LLMSpec.precondition a key := by
  -- Since both preconditions are defined as True, they are trivially equivalent.
  simp [VerinaSpec.only_once_precond, LLMSpec.precondition]

theorem postcondition_equiv (a : Array Int) (key : Int) (result : Bool) : LLMSpec.precondition a key →
  (VerinaSpec.only_once_postcond a key result ↔ LLMSpec.postcondition a key result) := by
  -- By definition of `countOccurrences`, we know that `countOccurrences a key = 1` if and only if `occursExactlyOnce a key`.
  have h_count_eq : VerinaSpec.count_occurrences a key = 1 ↔ LLMSpec.occursExactlyOnce a key := by
    -- By definition of `count`, we know that `count a key` is equal to `count_occurrences a key`.
    have h_count_eq : ∀ (a : Array ℤ) (key : ℤ), a.count key = VerinaSpec.count_occurrences a key := by
      intros a key; induction' a using Array.recOn with a ih ; simp +decide [ *, VerinaSpec.count_occurrences ] ;
      induction a using List.reverseRecOn <;> aesop;
    exact h_count_eq a key ▸ Iff.rfl;
  unfold VerinaSpec.only_once_postcond LLMSpec.postcondition; aesop;

end Proof