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

theorem precondition_equiv (s : String) :
  VerinaSpec.toLowercase_precond s ↔ LLMSpec.precondition s := by
  sorry

theorem postcondition_equiv (s : String) (result: String) :
  LLMSpec.precondition s →
  (VerinaSpec.toLowercase_postcond s result ↔ LLMSpec.postcondition s result) := by
  sorry

end Proof
