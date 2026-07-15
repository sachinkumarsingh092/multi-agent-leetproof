import Mathlib.Tactic

namespace VerinaSpec


def CountLessThan_precond (numbers : Array Int) (threshold : Int) : Prop :=
  True

def countLessThan (numbers : Array Int) (threshold : Int) : Nat :=
  let rec count (i : Nat) (acc : Nat) : Nat :=
    if i < numbers.size then
      let new_acc := if numbers[i]! < threshold then acc + 1 else acc
      count (i + 1) new_acc
    else
      acc
  count 0 0

def CountLessThan_postcond (numbers : Array Int) (threshold : Int) (result: Nat) :=
  result - numbers.foldl (fun count n => if n < threshold then count + 1 else count) 0 = 0 ∧
  numbers.foldl (fun count n => if n < threshold then count + 1 else count) 0 - result = 0

end VerinaSpec

namespace LLMSpec

-- We specify the count as the cardinality of the set of valid indices whose elements are < threshold.
-- This uses only standard Mathlib/Lean constructions: `Finset.range`, `Finset.filter`, and `Finset.card`.

def precondition (numbers : Array Int) (threshold : Int) : Prop :=
  True

def postcondition (numbers : Array Int) (threshold : Int) (result : Nat) : Prop :=
  result = ((Finset.range numbers.size).filter (fun (i : Nat) => numbers[i]! < threshold)).card ∧
  result ≤ numbers.size

end LLMSpec

section Proof

theorem precondition_equiv (numbers : Array Int) (threshold : Int) :
  VerinaSpec.CountLessThan_precond numbers threshold ↔ LLMSpec.precondition numbers threshold := by
  sorry

theorem postcondition_equiv (numbers : Array Int) (threshold : Int) (result: Nat) :
  LLMSpec.precondition numbers threshold →
  (VerinaSpec.CountLessThan_postcond numbers threshold result ↔ LLMSpec.postcondition numbers threshold result) := by
  sorry

end Proof
