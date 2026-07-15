import Mathlib.Tactic

namespace VerinaSpec


def isEven (n : Int) : Bool :=
  n % 2 = 0

def findEvenNumbers_precond (arr : Array Int) : Prop :=
  True

def findEvenNumbers_postcond (arr : Array Int) (result: Array Int) :=
  (∀ x, x ∈ result → isEven x ∧ x ∈ arr.toList) ∧
  (∀ x, x ∈ arr.toList → isEven x → x ∈ result) ∧
  (∀ x y, x ∈ arr.toList → y ∈ arr.toList →
    isEven x → isEven y →
    arr.toList.idxOf x ≤ arr.toList.idxOf y →
    result.toList.idxOf x ≤ result.toList.idxOf y)

end VerinaSpec

namespace LLMSpec

-- Helper predicate: evenness for Int.
-- We keep it as a Prop; we avoid needing decidability by never branching (`if`) on it in specs.
def EvenInt (x : Int) : Prop := x % 2 = 0

-- Order preservation: `result` is obtained by selecting elements from `arr` at strictly increasing indices.
-- This expresses that `result` is a subsequence of `arr` (with multiplicity), and preserves order.
def isOrderPreservingSelection (arr : Array Int) (result : Array Int) : Prop :=
  ∃ f : Nat → Nat,
    (∀ i : Nat, i < result.size → f i < arr.size ∧ result[i]! = arr[f i]!) ∧
    (∀ i : Nat, ∀ j : Nat, i < j → j < result.size → f i < f j)

-- No preconditions.
def precondition (arr : Array Int) : Prop :=
  True

-- Postcondition:
-- 1) Every element in `result` is even.
-- 2) For each integer value x:
--    - if x is even, its multiplicity is preserved (same count as in `arr`)
--    - if x is odd, it does not appear in `result` (count = 0)
-- 3) The relative order of the kept elements matches their order in `arr`.
def postcondition (arr : Array Int) (result : Array Int) : Prop :=
  (∀ i : Nat, i < result.size → EvenInt (result[i]!)) ∧
  (∀ x : Int, EvenInt x → result.count x = arr.count x) ∧
  (∀ x : Int, ¬ EvenInt x → result.count x = 0) ∧
  isOrderPreservingSelection arr result

end LLMSpec

section Proof

theorem precondition_equiv (arr : Array Int) :
  VerinaSpec.findEvenNumbers_precond arr ↔ LLMSpec.precondition arr := by
  sorry

theorem postcondition_equiv (arr : Array Int) (result: Array Int) :
  LLMSpec.precondition arr →
  (VerinaSpec.findEvenNumbers_postcond arr result ↔ LLMSpec.postcondition arr result) := by
  sorry

end Proof
