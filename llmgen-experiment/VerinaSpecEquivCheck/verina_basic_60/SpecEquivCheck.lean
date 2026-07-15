import Mathlib.Tactic

namespace VerinaSpec


def isEven (n : Int) : Bool :=
  n % 2 = 0

def FindEvenNumbers_precond (arr : Array Int) : Prop :=
  True

def FindEvenNumbers_postcond (arr : Array Int) (result: Array Int) :=
  result.all (fun x => isEven x) ∧
  result.toList.Sublist arr.toList ∧
  result.size = arr.toList.countP isEven

end VerinaSpec

namespace LLMSpec

-- Helper predicate: evenness as a Prop (Mathlib's `Even`).
def isEven (x : Int) : Prop := Even x

-- Helper predicate: evenness as a Bool (useful for `countP`).
def isEvenB (x : Int) : Bool := (x % 2) == 0

-- Order preservation expressed via an increasing index mapping from `result` indices to `arr` indices.
def orderPreserved (arr : Array Int) (result : Array Int) : Prop :=
  ∃ f : Nat → Nat,
    (∀ (i : Nat), i < result.size →
      f i < arr.size ∧ arr[f i]! = result[i]!) ∧
    (∀ (i : Nat) (j : Nat), i < j → j < result.size → f i < f j)

-- No additional preconditions.
def precondition (arr : Array Int) : Prop :=
  True

def postcondition (arr : Array Int) (result : Array Int) : Prop :=
  -- All outputs are even
  (∀ (i : Nat), i < result.size → isEven (result[i]!)) ∧
  -- Exact multiplicity of each value: even values are kept, odd values are removed
  (∀ (x : Int), (isEven x → result.count x = arr.count x) ∧ (¬ isEven x → result.count x = 0)) ∧
  -- Order is preserved relative to the input
  orderPreserved arr result ∧
  -- Size matches the number of even elements in the input
  (result.size = arr.countP isEvenB)

end LLMSpec

section Proof

theorem precondition_equiv (arr : Array Int) :
  VerinaSpec.FindEvenNumbers_precond arr ↔ LLMSpec.precondition arr := by
  sorry

theorem postcondition_equiv (arr : Array Int) (result: Array Int) :
  LLMSpec.precondition arr →
  (VerinaSpec.FindEvenNumbers_postcond arr result ↔ LLMSpec.postcondition arr result) := by
  sorry

end Proof
