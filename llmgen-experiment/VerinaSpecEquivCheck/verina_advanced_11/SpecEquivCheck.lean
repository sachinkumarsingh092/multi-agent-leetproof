import Mathlib.Tactic

namespace VerinaSpec


def findMajorityElement_precond (lst : List Int) : Prop :=
  True

def countOccurrences (n : Int) (lst : List Int) : Nat :=
  lst.foldl (fun acc x => if x = n then acc + 1 else acc) 0

def findMajorityElement_postcond (lst : List Int) (result: Int) : Prop :=
  let count := fun x => (lst.filter (fun y => y = x)).length
  let n := lst.length
  let majority := count result > n / 2 ∧ lst.all (fun x => count x ≤ n / 2 ∨ x = result)
  (result = -1 → lst.all (count · ≤ n / 2) ∨ majority) ∧
  (result ≠ -1 → majority)

end VerinaSpec

namespace LLMSpec

-- Helper predicate: x is a majority element of lst iff it appears strictly more than half the time.
-- We avoid division by using the equivalent inequality 2 * count(x) > length.
-- Note: `lst.count x : Nat` and `lst.length : Nat`.
def isMajority (lst : List Int) (x : Int) : Prop :=
  (2 * lst.count x) > lst.length

def precondition (lst : List Int) : Prop :=
  True

-- Postcondition:
-- 1. If a majority element exists, `result` is that unique majority element.
-- 2. If no majority element exists, `result = -1`.
-- This matches the prompt's requirement "return the majority element if one exists, otherwise -1".
def postcondition (lst : List Int) (result : Int) : Prop :=
  ((∃ x : Int, isMajority lst x) →
      (isMajority lst result ∧ ∀ x : Int, isMajority lst x → x = result)) ∧
  ((¬ (∃ x : Int, isMajority lst x)) → result = (-1))

end LLMSpec

section Proof

theorem precondition_equiv (lst : List Int) :
  VerinaSpec.findMajorityElement_precond lst ↔ LLMSpec.precondition lst := by
  sorry

theorem postcondition_equiv (lst : List Int) (result: Int) :
  LLMSpec.precondition lst →
  (VerinaSpec.findMajorityElement_postcond lst result ↔ LLMSpec.postcondition lst result) := by
  sorry

end Proof
