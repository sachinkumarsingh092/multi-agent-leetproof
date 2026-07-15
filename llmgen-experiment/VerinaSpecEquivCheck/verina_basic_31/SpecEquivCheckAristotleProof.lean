/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 083190ab-d6e6-43cd-b072-8d9f3bdc2b3a

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (s : String) : VerinaSpec.toUppercase_precond s ↔ LLMSpec.precondition s

- theorem postcondition_equiv (s : String) (result : String) : LLMSpec.precondition s →
  (VerinaSpec.toUppercase_postcond s result ↔ LLMSpec.postcondition s result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def isLowerCase (c : Char) : Bool :=
  'a' ≤ c ∧ c ≤ 'z'

def shiftMinus32 (c : Char) : Char :=
  Char.ofNat ((c.toNat - 32) % 128)

def toUppercase_precond (s : String) : Prop :=
  True

def toUppercase_postcond (s : String) (result: String) :=
  let cs := s.toList
  let cs' := result.toList
  (result.length = s.length) ∧
  (∀ i, i < s.length →
    (isLowerCase cs[i]! → cs'[i]! = shiftMinus32 cs[i]!) ∧
    (¬isLowerCase cs[i]! → cs'[i]! = cs[i]!))

end VerinaSpec

namespace LLMSpec

-- Helper predicate: pointwise uppercase mapping over the `data : List Char` view of strings.
-- We specify the transformation character-by-character (not as a particular algorithm).
-- We also explicitly require length preservation at the character-list level.

def pointwiseToUpperData (s : String) (t : String) : Prop :=
  t.data.length = s.data.length ∧
  ∀ (i : Nat), i < s.data.length → t.data[i]! = (s.data[i]!).toUpper

def precondition (s : String) : Prop :=
  True

def postcondition (s : String) (result : String) : Prop :=
  pointwiseToUpperData s result

end LLMSpec

section Proof

theorem precondition_equiv (s : String) : VerinaSpec.toUppercase_precond s ↔ LLMSpec.precondition s := by
  -- Since both preconditions are True, their equivalence is trivial.
  simp [VerinaSpec.toUppercase_precond, LLMSpec.precondition]

theorem postcondition_equiv (s : String) (result : String) : LLMSpec.precondition s →
  (VerinaSpec.toUppercase_postcond s result ↔ LLMSpec.postcondition s result) := by
  -- By definition of `toUppercase_postcond`, we know that if `VerinaSpec.toUppercase_postcond s result` holds, then for every character in `s`, if it's lowercase, the corresponding character in `result` is the uppercase version.
  unfold VerinaSpec.toUppercase_postcond LLMSpec.postcondition LLMSpec.pointwiseToUpperData
  simp [VerinaSpec.shiftMinus32] at *;
  -- By definition of `Char.toUpper`, we know that for any character `c`, `c.toUpper` is equal to `Char.ofNat ((c.toNat - 32) % 128)` if `c` is lowercase, and `c` otherwise.
  have h_toUpper : ∀ c : Char, c.toUpper = if 'a' ≤ c ∧ c ≤ 'z' then Char.ofNat ((c.toNat - 32) % 128) else c := by
    -- By definition of `Char.toUpper`, we know that it is equivalent to `shiftMinus32` for lowercase letters and returns the character itself otherwise.
    intros c
    simp [Char.toUpper];
    split_ifs <;> simp_all +decide [ Char.toNat ];
    · rw [ Nat.mod_eq_of_lt ( by omega ) ];
    · exact absurd ( ‹'a' ≤ c → 'z' < c› ( by exact Nat.le_trans ( by decide ) ( ‹97 ≤ c.val.toNat ∧ c.val.toNat ≤ 122›.1 ) ) ) ( by exact not_lt_of_ge ( Nat.le_trans ( ‹97 ≤ c.val.toNat ∧ c.val.toNat ≤ 122›.2 ) ( by decide ) ) );
    · -- Since $97 \leq c.val.toNat$ and $c.val.toNat \leq 122$, we have $122 < c.val.toNat$ is false, leading to a contradiction.
      have h_contra : 97 ≤ c.val.toNat ∧ c.val.toNat ≤ 122 := by
        aesop;
      linarith [ ‹97 ≤ c.val.toNat → 122 < c.val.toNat› h_contra.1 ];
  -- By definition of `isLowerCase`, we know that `isLowerCase c` is true if and only if `c` is between 'a' and 'z'.
  have h_isLowerCase : ∀ c : Char, VerinaSpec.isLowerCase c = ('a' ≤ c ∧ c ≤ 'z') := by
    unfold VerinaSpec.isLowerCase; aesop;
  simp_all +decide [ String.length ];
  grind +ring

end Proof