import Mathlib.Tactic

namespace VerinaSpec


def Match_precond (s : String) (p : String) : Prop :=
  s.toList.length = p.toList.length

def Match_postcond (s : String) (p : String) (result: Bool) :=
  (result = true ↔ ∀ n : Nat, n < s.toList.length → ((s.toList[n]! = p.toList[n]!) ∨ (p.toList[n]! = '?')))

end VerinaSpec

namespace LLMSpec

-- A pattern character matches a text character if it is '?' or it equals the text character.
def charMatches (sc : Char) (pc : Char) : Prop :=
  pc = '?' ∨ pc = sc

-- Pointwise match predicate for equal-length arrays.
def matchesPattern (s : Array Char) (p : Array Char) : Prop :=
  ∀ (i : Nat), i < s.size → charMatches (s[i]!) (p[i]!)

-- The note states we may assume equal length, so we enforce it as a precondition.
def precondition (s : Array Char) (p : Array Char) : Prop :=
  s.size = p.size

def postcondition (s : Array Char) (p : Array Char) (result : Bool) : Prop :=
  (result = true ↔ matchesPattern s p) ∧
  (result = false ↔ ¬ matchesPattern s p)

end LLMSpec

section Proof

theorem precondition_equiv (s : String) (p : String) :
  VerinaSpec.Match_precond s p ↔ LLMSpec.precondition s.toList.toArray p.toList.toArray := by
  sorry

theorem postcondition_equiv (s : String) (p : String) (result: Bool) :
  LLMSpec.precondition s.toList.toArray p.toList.toArray →
  (VerinaSpec.Match_postcond s p result ↔ LLMSpec.postcondition s.toList.toArray p.toList.toArray result) := by
  sorry

end Proof
