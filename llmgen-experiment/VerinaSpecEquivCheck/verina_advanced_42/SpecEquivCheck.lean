import Mathlib.Tactic

namespace VerinaSpec


def maxProfit_precond (prices : List Nat) : Prop :=
  True

def updateMinAndProfit (price : Nat) (minSoFar : Nat) (maxProfit : Nat) : (Nat × Nat) :=
  let newMin := Nat.min minSoFar price
  let profit := if price > minSoFar then price - minSoFar else 0
  let newMaxProfit := Nat.max maxProfit profit
  (newMin, newMaxProfit)

def maxProfitAux (prices : List Nat) (minSoFar : Nat) (maxProfit : Nat) : Nat :=
  match prices with
  | [] => maxProfit
  | p :: ps =>
    let (newMin, newProfit) := updateMinAndProfit p minSoFar maxProfit
    maxProfitAux ps newMin newProfit

def maxProfit_postcond (prices : List Nat) (result: Nat) : Prop :=
  List.Pairwise (fun ⟨pi, i⟩ ⟨pj, j⟩ => i < j → pj - pi ≤ result) prices.zipIdx ∧
  (result = 0 ↔
    (prices.length ≤ 1 ∨
     prices.zipIdx.all (fun ⟨pi, i⟩ =>
       prices.zipIdx.all (fun ⟨pj, j⟩ => i ≥ j ∨ pj ≤ pi)))) ∧
  (result > 0 → prices.zipIdx.any (fun ⟨pi, i⟩ =>
    prices.zipIdx.any (fun ⟨pj, j⟩ => i < j ∧ pj - pi = result)))

end VerinaSpec

namespace LLMSpec

-- A realizable profit value from one buy/sell transaction.
def IsTransactionProfit (prices : List Nat) (p : Nat) : Prop :=
  ∃ (i : Nat) (j : Nat),
    i < j ∧ j < prices.length ∧ p = (prices[j]! - prices[i]!)

-- The result upper-bounds all transaction profits.
def IsUpperBoundProfit (prices : List Nat) (ub : Nat) : Prop :=
  ∀ (i : Nat) (j : Nat),
    i < j → j < prices.length → (prices[j]! - prices[i]!) ≤ ub

def precondition (prices : List Nat) : Prop :=
  True

def postcondition (prices : List Nat) (result : Nat) : Prop :=
  (prices.length < 2 ∧ result = 0) ∨
  (2 ≤ prices.length ∧
    IsTransactionProfit prices result ∧
    IsUpperBoundProfit prices result)

end LLMSpec

section Proof

theorem precondition_equiv (prices : List Nat) : VerinaSpec.maxProfit_precond prices ↔ LLMSpec.precondition prices := by
  -- Since both preconditions are True, their equivalence is trivial.
  simp [VerinaSpec.maxProfit_precond, LLMSpec.precondition]

theorem postcondition_equiv (prices : List Nat) (result : Nat) : LLMSpec.precondition prices →
  VerinaSpec.maxProfit_postcond prices result ↔ LLMSpec.postcondition prices result := by
  sorry

end Proof
