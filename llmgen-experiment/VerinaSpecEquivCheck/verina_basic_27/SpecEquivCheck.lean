import Mathlib.Tactic
import Std.Data.HashSet

namespace VerinaSpec


def findFirstRepeatedChar_precond (s : String) : Prop :=
  True

def findFirstRepeatedChar_postcond (s : String) (result: Option Char) :=
  let cs := s.toList
  match result with
  | some c =>
    let secondIdx := cs.zipIdx.findIdx (fun (x, i) => x = c && i ≠ cs.idxOf c)
    cs.count c ≥ 2 ∧
    List.Pairwise (· ≠ ·) (cs.take secondIdx)
  | none =>
    List.Pairwise (· ≠ ·) cs

end VerinaSpec

namespace LLMSpec

-- We reason about a `String` via its underlying list of characters.
-- This is a definitional projection in Lean (`String.data : List Char`).
def chars (s : String) : List Char :=
  s.data

-- Predicate: index j (in the character list) is a repeated occurrence.
def isRepeatIndex (s : String) (j : Nat) : Prop :=
  j < (chars s).length ∧
  ∃ i : Nat, i < j ∧ (chars s)[i]! = (chars s)[j]!

-- Predicate: j is the first index (left-to-right) at which a repeat occurs.
def isFirstRepeatIndex (s : String) (j : Nat) : Prop :=
  isRepeatIndex s j ∧
  ∀ k : Nat, k < j → ¬ isRepeatIndex s k

-- No preconditions.
def precondition (s : String) : Prop :=
  True

def postcondition (s : String) (result : Option Char) : Prop :=
  -- `none` exactly when there is no repeated index
  (result = none ↔ (∀ j : Nat, j < (chars s).length → ¬ isRepeatIndex s j)) ∧
  -- if `some c`, then c is the character at some first-repeat index
  (∀ c : Char, result = some c → (∃ j : Nat, isFirstRepeatIndex s j ∧ (chars s)[j]! = c)) ∧
  -- uniqueness: any first-repeat index must have the returned character
  (∀ c : Char, result = some c → (∀ j : Nat, isFirstRepeatIndex s j → (chars s)[j]! = c))

end LLMSpec

section Proof

theorem precondition_equiv (s : String) :
  VerinaSpec.findFirstRepeatedChar_precond s ↔ LLMSpec.precondition s := by
  sorry

theorem postcondition_equiv (s : String) (result: Option Char) :
  LLMSpec.precondition s →
  (VerinaSpec.findFirstRepeatedChar_postcond s result ↔ LLMSpec.postcondition s result) := by
  sorry

end Proof
