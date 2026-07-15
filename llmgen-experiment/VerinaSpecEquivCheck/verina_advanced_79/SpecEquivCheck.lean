import Mathlib.Tactic

namespace VerinaSpec


def twoSum_precond (nums : List Int) (target : Int) : Prop :=
  True

def twoSum_postcond (nums : List Int) (target : Int) (result: Option (Nat × Nat)) : Prop :=
    match result with
    | none => List.Pairwise (· + · ≠ target) nums
    | some (i, j) =>
        i < j ∧
        j < nums.length ∧
        nums[i]! + nums[j]! = target ∧
        (nums.take i).zipIdx.all (fun ⟨a, i'⟩ =>
          (nums.drop (i' + 1)).all (fun b => a + b ≠ target)) ∧
        ((nums.drop (i + 1)).take (j - i - 1)).all (fun b => nums[i]! + b ≠ target)

end VerinaSpec

namespace LLMSpec

-- Lexicographic (non-strict) order on pairs of natural numbers.
-- `a ≤lex b` iff `a.1 < b.1` or (`a.1 = b.1` and `a.2 ≤ b.2`).
def lexLE (a : Nat × Nat) (b : Nat × Nat) : Prop :=
  a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2)

-- A pair of indices is valid for TwoSum if it is in-bounds, ordered i<j, and sums to target.
def ValidPair (nums : List Int) (target : Int) (p : Nat × Nat) : Prop :=
  p.1 < p.2 ∧ p.2 < nums.length ∧ nums[p.1]! + nums[p.2]! = target

-- No preconditions: all lists and targets are allowed.
def precondition (nums : List Int) (target : Int) : Prop :=
  True

def postcondition (nums : List Int) (target : Int) (result : Option (Nat × Nat)) : Prop :=
  match result with
  | none =>
      -- No valid pair exists.
      ∀ (i : Nat) (j : Nat), i < j → j < nums.length → nums[i]! + nums[j]! ≠ target
  | some p =>
      -- Returned pair is valid and lexicographically minimal among all valid pairs.
      ValidPair nums target p ∧
      (∀ (q : Nat × Nat), ValidPair nums target q → lexLE p q)

end LLMSpec

section Proof

theorem precondition_equiv (nums : List Int) (target : Int) :
  VerinaSpec.twoSum_precond nums target ↔ LLMSpec.precondition nums target := by
  sorry

theorem postcondition_equiv (nums : List Int) (target : Int) (result: Option (Nat × Nat)) :
  LLMSpec.precondition nums target →
  (VerinaSpec.twoSum_postcond nums target result ↔ LLMSpec.postcondition nums target result) := by
  sorry

end Proof
