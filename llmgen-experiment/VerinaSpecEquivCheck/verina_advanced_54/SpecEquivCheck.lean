import Mathlib.Tactic

namespace VerinaSpec


def missingNumber_precond (nums : List Nat) : Prop :=
  nums.all (fun x => x ≤ nums.length) ∧ List.Nodup nums

def missingNumber_postcond (nums : List Nat) (result: Nat) : Prop :=
  let n := nums.length
  (result ∈ List.range (n + 1)) ∧
  ¬(result ∈ nums) ∧
  ∀ x, (x ∈ List.range (n + 1)) → x ≠ result → x ∈ nums

end VerinaSpec

namespace LLMSpec

-- Helper: predicate stating a Nat is within the expected inclusive range [0, nums.length].
-- Note: lower bound 0 is automatic for Nat.
def inRange0n (nums : List Nat) (x : Nat) : Prop :=
  x ≤ nums.length

-- Preconditions:
-- - no duplicates
-- - all elements are within [0, n]
-- - there exists a missing number in [0, n]
-- - the missing number is unique

def precondition (nums : List Nat) : Prop :=
  nums.Nodup ∧
  (∀ (x : Nat), x ∈ nums → inRange0n nums x) ∧
  (∃ (m : Nat), inRange0n nums m ∧ m ∉ nums) ∧
  (∀ (m1 : Nat) (m2 : Nat),
    inRange0n nums m1 → inRange0n nums m2 → m1 ∉ nums → m2 ∉ nums → m1 = m2)

-- Postconditions:
-- - result is within [0, n]
-- - result is not present in the list
-- - result is the unique missing number in [0, n]

def postcondition (nums : List Nat) (result : Nat) : Prop :=
  inRange0n nums result ∧
  result ∉ nums ∧
  (∀ (x : Nat), inRange0n nums x → x ∉ nums → x = result)

end LLMSpec

section Proof

theorem precondition_equiv (nums : List Nat) :
  VerinaSpec.missingNumber_precond nums ↔ LLMSpec.precondition nums := by
  sorry

theorem postcondition_equiv (nums : List Nat) (result: Nat) :
  LLMSpec.precondition nums →
  (VerinaSpec.missingNumber_postcond nums result ↔ LLMSpec.postcondition nums result) := by
  sorry

end Proof
