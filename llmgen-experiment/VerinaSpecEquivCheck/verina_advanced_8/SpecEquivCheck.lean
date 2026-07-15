import Mathlib.Tactic

namespace VerinaSpec


def canCompleteCircuit_precond (gas : List Int) (cost : List Int) : Prop :=
  gas.length > 0 ∧ gas.length = cost.length

def canCompleteCircuit_postcond (gas : List Int) (cost : List Int) (result: Int) : Prop :=
  let valid (start : Nat) := List.range gas.length |>.all (fun i =>
    let acc := List.range (i + 1) |>.foldl (fun t j =>
      let jdx := (start + j) % gas.length
      t + gas[jdx]! - cost[jdx]!) 0
    acc ≥ 0)
  (result = -1 → (List.range gas.length).all (fun start => ¬ valid start)) ∧
  (result ≥ 0 → result < gas.length ∧ valid result.toNat ∧ (List.range result.toNat).all (fun start => ¬ valid start))

end VerinaSpec

namespace LLMSpec

-- Helper: integer sum of a list.
-- We use `foldl` because it is a standard Mathlib/List operation.
def sumIntList (xs : List Int) : Int :=
  xs.foldl (fun acc x => acc + x) 0

-- Helper: circular index; meaningful when `n > 0`.
def circIdx (n : Nat) (i : Nat) : Nat :=
  i % n

-- Helper: net gain at (circular) station index `i`.
def circDiff (gas : List Int) (cost : List Int) (i : Nat) : Int :=
  let n : Nat := gas.length
  let j : Nat := circIdx n i
  gas[j]! - cost[j]!

-- Helper: balance after taking exactly `t` steps starting from `start`.
-- This is a mathematical finite sum over the range `{0,1,...,t-1}`.
def balanceFrom (gas : List Int) (cost : List Int) (start : Nat) (t : Nat) : Int :=
  (Finset.range t).sum (fun k => circDiff gas cost (start + k))

-- Helper: a start index is valid if all prefix balances along the `n` steps are nonnegative.
def validStart (gas : List Int) (cost : List Int) (start : Nat) : Prop :=
  let n : Nat := gas.length
  start < n ∧
    (∀ t : Nat, t ≤ n → 0 ≤ balanceFrom gas cost start t)

-- Helper: existence of some valid start.
def existsValidStart (gas : List Int) (cost : List Int) : Prop :=
  let n : Nat := gas.length
  ∃ s : Nat, s < n ∧ validStart gas cost s

-- Preconditions: lists have equal non-zero length.
def precondition (gas : List Int) (cost : List Int) : Prop :=
  gas.length = cost.length ∧ gas.length > 0

-- Postcondition:
-- * If no valid start exists, result is `-1`.
-- * Otherwise, result is a valid start index (as a nonnegative Int within range)
--   and is minimal among all valid starts.
def postcondition (gas : List Int) (cost : List Int) (result : Int) : Prop :=
  let n : Nat := gas.length
  (result = (-1) ↔ ¬ existsValidStart gas cost) ∧
  (result ≠ (-1) →
      0 ≤ result ∧
      result.toNat < n ∧
      validStart gas cost result.toNat ∧
      (∀ s : Nat, s < n → validStart gas cost s → result.toNat ≤ s))

end LLMSpec

section Proof

theorem precondition_equiv (gas : List Int) (cost : List Int) :
  VerinaSpec.canCompleteCircuit_precond gas cost ↔ LLMSpec.precondition gas cost := by
  sorry

theorem postcondition_equiv (gas : List Int) (cost : List Int) (result: Int) :
  LLMSpec.precondition gas cost →
  (VerinaSpec.canCompleteCircuit_postcond gas cost result ↔ LLMSpec.postcondition gas cost result) := by
  sorry

end Proof
