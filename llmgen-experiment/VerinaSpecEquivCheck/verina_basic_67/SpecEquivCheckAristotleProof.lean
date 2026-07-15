/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 65947fe3-9bec-48c3-ae6f-f7f0737eb0ec

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (x : List Char) : VerinaSpec.IsPalindrome_precond x ↔ LLMSpec.precondition x

- theorem postcondition_equiv (x : List Char) (result : Bool) : LLMSpec.precondition x →
  (VerinaSpec.IsPalindrome_postcond x result ↔ LLMSpec.postcondition x result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def IsPalindrome_precond (x : List Char) : Prop :=
  True

def isPalindromeHelper (x : List Char) (i j : Nat) : Bool :=
  if i < j then
    match x[i]?, x[j]? with
    | some ci, some cj =>
      if ci ≠ cj then false else isPalindromeHelper x (i + 1) (j - 1)
    | _, _ => false  -- This case should not occur due to valid indices
  else true

def IsPalindrome_postcond (x : List Char) (result: Bool) :=
  result ↔ ∀ i : Nat, i < x.length → (x[i]! = x[x.length - i - 1]!)

end VerinaSpec

namespace LLMSpec

-- Helper predicate: x is a palindrome iff it equals its reverse.
-- We keep this as a Prop so it can be used in a logical postcondition.
def IsPalindrome (x : List Char) : Prop :=
  x.reverse = x

def precondition (x : List Char) : Prop :=
  True

def postcondition (x : List Char) (result : Bool) : Prop :=
  (result = true ↔ IsPalindrome x)

end LLMSpec

section Proof

theorem precondition_equiv (x : List Char) : VerinaSpec.IsPalindrome_precond x ↔ LLMSpec.precondition x := by
  -- Since both preconditions are defined as True, they are trivially equivalent.
  simp [VerinaSpec.IsPalindrome_precond, LLMSpec.precondition]

theorem postcondition_equiv (x : List Char) (result : Bool) : LLMSpec.precondition x →
  (VerinaSpec.IsPalindrome_postcond x result ↔ LLMSpec.postcondition x result) := by
  unfold VerinaSpec.IsPalindrome_postcond LLMSpec.postcondition;
  -- By definition of `IsPalindrome`, we know that `x.reverse = x` if and only if `∀ i < x.length, x[i]! = x[x.length - i - 1]!`.
  have h_palindrome_def : LLMSpec.IsPalindrome x ↔ ∀ i < x.length, x[i]! = x[x.length - i - 1]! := by
    constructor <;> intro h;
    · intro i hi; have := congr_arg ( fun l => l[i]! ) h; simp_all +decide [ List.getElem?_eq_getElem ] ;
      grind;
    · refine' List.ext_get _ _ <;> simp_all +decide [ List.get?_eq_get ];
      grind +ring;
  aesop

end Proof