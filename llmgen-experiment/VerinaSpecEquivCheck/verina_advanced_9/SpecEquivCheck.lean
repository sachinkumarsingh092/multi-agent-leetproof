import Mathlib.Tactic

namespace VerinaSpec


def sumOfDigits (x : Nat) : Nat :=
  let rec go (n acc : Nat) : Nat :=
    if n = 0 then acc
    else go (n / 10) (acc + (n % 10))
  go x 0

def countSumDivisibleBy_precond (n : Nat) (d : Nat) : Prop :=
  d > 0

def isSumDivisibleBy (x : Nat) (d:Nat) : Bool :=
  (sumOfDigits x) % d = 0

def countSumDivisibleBy_postcond (n : Nat) (d : Nat) (result: Nat) : Prop :=
  (List.length (List.filter (fun x => x < n ∧ (sumOfDigits x) % d = 0) (List.range n))) - result = 0 ∧
  result ≤ (List.length (List.filter (fun x => x < n ∧ (sumOfDigits x) % d = 0) (List.range n)))

end VerinaSpec

namespace LLMSpec

-- Helper: sum of base-10 digits of a natural number.
-- Mathlib's `Nat.digits 10 x` gives the base-10 digits of `x` (least significant digit first).
-- Summing the digit list yields the digit sum.
def digitSum10 (x : Nat) : Nat :=
  (Nat.digits 10 x).sum

-- Boolean predicate: digit sum is divisible by d (using modulo).
-- We keep this as Bool so it can be used directly with `Finset.filter`.
def digitSumDivisibleB (x : Nat) (d : Nat) : Bool :=
  (digitSum10 x % d) == 0

def precondition (n : Nat) (d : Nat) : Prop :=
  d > 0

def postcondition (n : Nat) (d : Nat) (result : Nat) : Prop :=
  -- `result` is the number of naturals x with x < n and digitSum10(x) divisible by d.
  result = ((Finset.range n).filter (fun (x : Nat) => digitSumDivisibleB x d)).card

end LLMSpec

section Proof

theorem precondition_equiv (n : Nat) (d : Nat) :
  VerinaSpec.countSumDivisibleBy_precond n d ↔ LLMSpec.precondition n d := by
  sorry

theorem postcondition_equiv (n : Nat) (d : Nat) (result: Nat) :
  LLMSpec.precondition n d →
  (VerinaSpec.countSumDivisibleBy_postcond n d result ↔ LLMSpec.postcondition n d result) := by
  sorry

end Proof
