/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 9d9315e2-0cf4-4409-8ebe-3085b84d2d4a

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (s : String) : VerinaSpec.toLowercase_precond s ↔ LLMSpec.precondition s

- theorem postcondition_equiv (s : String) (result : String) : LLMSpec.precondition s →
  (VerinaSpec.toLowercase_postcond s result ↔ LLMSpec.postcondition s result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def isUpperCase (c : Char) : Bool :=
  'A' ≤ c ∧ c ≤ 'Z'

def shift32 (c : Char) : Char :=
  Char.ofNat (c.toNat + 32)

def toLowercase_precond (s : String) : Prop :=
  True

def toLowercase_postcond (s : String) (result: String) :=
  let cs := s.toList
  let cs' := result.toList
  (result.length = s.length) ∧
  (∀ i : Nat, i < s.length →
    (isUpperCase cs[i]! → cs'[i]! = shift32 cs[i]!) ∧
    (¬isUpperCase cs[i]! → cs'[i]! = cs[i]!))

end VerinaSpec

namespace LLMSpec

-- Helper: the intended per-character transformation.
-- `Char.toLower` converts uppercase ASCII letters to their lowercase counterpart, and leaves other characters unchanged.
def lowerChar (c : Char) : Char :=
  c.toLower

def precondition (s : String) : Prop :=
  True

def postcondition (s : String) (result : String) : Prop :=
  let sl := s.toList
  let rl := result.toList
  rl.length = sl.length ∧
  ∀ (i : Nat), i < sl.length → rl[i]! = lowerChar (sl[i]!)

end LLMSpec

section Proof

theorem precondition_equiv (s : String) : VerinaSpec.toLowercase_precond s ↔ LLMSpec.precondition s := by
  -- Since both preconditions are True, the equivalence is trivial.
  simp [VerinaSpec.toLowercase_precond, LLMSpec.precondition]

theorem postcondition_equiv (s : String) (result : String) : LLMSpec.precondition s →
  (VerinaSpec.toLowercase_postcond s result ↔ LLMSpec.postcondition s result) := by
  -- To prove the equivalence, we can show that the two conditions are equivalent by definition.
  intro h_pre
  simp [VerinaSpec.toLowercase_postcond, LLMSpec.postcondition];
  -- By definition of `lowerChar`, we know that for any character `c`, `lowerChar c` is equal to `shift32 c` if `c` is uppercase, and equal to `c` otherwise.
  have h_lowerChar_shift32 : ∀ c : Char, LLMSpec.lowerChar c = if VerinaSpec.isUpperCase c then VerinaSpec.shift32 c else c := by
    intro c
    simp [LLMSpec.lowerChar, VerinaSpec.shift32, VerinaSpec.isUpperCase];
    split_ifs <;> simp_all +decide [ Char.toLower ];
    · exact fun h => absurd ( h ( by simpa using ‹'A' ≤ c ∧ c ≤ 'Z'›.1 ) ) ( by simpa using ‹'A' ≤ c ∧ c ≤ 'Z'›.2 );
    · exact fun h₁ h₂ => False.elim <| not_lt_of_ge h₂ <| ‹'A' ≤ c → 'Z' < c› <| by exact Nat.le_trans ( by decide ) h₁;
  congr! 2;
  cases s ; aesop

end Proof