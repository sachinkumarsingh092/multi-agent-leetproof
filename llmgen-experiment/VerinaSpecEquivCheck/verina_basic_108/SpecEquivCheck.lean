import Mathlib.Tactic

namespace VerinaSpec


def below_zero_precond (operations : List Int) : Prop :=
  True

def buildS (operations : List Int) : Array Int :=
  let sList := operations.foldl
    (fun (acc : List Int) (op : Int) =>
      let last := acc.getLast? |>.getD 0
      acc.append [last + op])
    [0]
  Array.mk sList

def below_zero_postcond (operations : List Int) (result: (Array Int × Bool)) :=
  let s := result.1
  let result := result.2
  s.size = operations.length + 1 ∧
  s[0]? = some 0 ∧
  (List.range (s.size - 1)).all (fun i => s[i + 1]? = some (s[i]! + operations[i]!)) ∧
  ((result = true) → ((List.range (operations.length)).any (fun i => s[i + 1]! < 0))) ∧
  ((result = false) → s.all (· ≥ 0))

end VerinaSpec

namespace LLMSpec

-- Helper: interpret a partial sum at index i as the sum of the first i operations.
-- We rely on Mathlib/Init definitions: List.take and List.sum.

def precondition (operations : List Int) : Prop :=
  True

def postcondition (operations : List Int) (result : (Array Int × Bool)) : Prop :=
  let ps : Array Int := result.1
  let neg : Bool := result.2
  -- Shape of the partial-sum array
  ps.size = operations.length + 1 ∧
  -- Each position i contains the sum of the first i operations
  (∀ (i : Nat), i < ps.size → ps[i]! = (operations.take i).sum) ∧
  -- Negativity flag: some partial sum after index 0 is negative
  (neg = true ↔ ∃ (i : Nat), i < ps.size ∧ i ≠ 0 ∧ ps[i]! < 0)

end LLMSpec

section Proof

theorem precondition_equiv (operations : List Int) :
  VerinaSpec.below_zero_precond operations ↔ LLMSpec.precondition operations := by
  sorry

theorem postcondition_equiv (operations : List Int) (result: (Array Int × Bool)) :
  LLMSpec.precondition operations →
  (VerinaSpec.below_zero_postcond operations result ↔ LLMSpec.postcondition operations result) := by
  sorry

end Proof
