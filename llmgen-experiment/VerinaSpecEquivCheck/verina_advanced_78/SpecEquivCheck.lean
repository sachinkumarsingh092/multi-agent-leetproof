import Mathlib.Tactic

namespace VerinaSpec


def twoSum_precond (nums : List Int) (target : Int) : Prop :=
  let pairwiseSum := List.range nums.length |>.flatMap (fun i =>
    nums.drop (i + 1) |>.map (fun y => nums[i]! + y))
  nums.length > 1 ∧ pairwiseSum.count target = 1

def findComplement (nums : List Int) (target : Int) (i : Nat) (x : Int) : Option Nat :=
  let rec aux (nums : List Int) (j : Nat) : Option Nat :=
    match nums with
    | []      => none
    | y :: ys => if x + y = target then some (i + j + 1) else aux ys (j + 1)
  aux nums 0

def twoSumAux (nums : List Int) (target : Int) (i : Nat) : Prod Nat Nat :=
  match nums with
  | []      => panic! "No solution exists"
  | x :: xs =>
    match findComplement xs target i x with
    | some j => (i, j)
    | none   => twoSumAux xs target (i + 1)

def twoSum_postcond (nums : List Int) (target : Int) (result: Prod Nat Nat) : Prop :=
  let i := result.fst;
  let j := result.snd;
  (i < j) ∧
  (i < nums.length) ∧ (j < nums.length) ∧
  (nums[i]!) + (nums[j]!) = target

end VerinaSpec

namespace LLMSpec

-- (i,j) is a valid TwoSum witness for (nums,target) when it is ordered, in-bounds, and sums to target.
-- Note: `j < nums.length` together with `i < j` implies `i < nums.length`, so we do not repeat it.
def IsTwoSumWitness (nums : List Int) (target : Int) (i : Nat) (j : Nat) : Prop :=
  i < j ∧ j < nums.length ∧ nums[i]! + nums[j]! = target

-- There exists exactly one witness pair with i<j.
def HasUniqueTwoSum (nums : List Int) (target : Int) : Prop :=
  (∃ i : Nat, ∃ j : Nat, IsTwoSumWitness nums target i j) ∧
  (∀ i1 : Nat, ∀ j1 : Nat, ∀ i2 : Nat, ∀ j2 : Nat,
    IsTwoSumWitness nums target i1 j1 →
    IsTwoSumWitness nums target i2 j2 →
    (i1 = i2 ∧ j1 = j2))

-- Preconditions:
-- 1) The input admits exactly one solution pair (i,j) with i<j.
def precondition (nums : List Int) (target : Int) : Prop :=
  HasUniqueTwoSum nums target

-- Postcondition:
-- 1) The returned pair is a valid witness.
-- 2) Any other valid witness must have the same indices (so the returned pair is the unique solution).
def postcondition (nums : List Int) (target : Int) (result : Prod Nat Nat) : Prop :=
  IsTwoSumWitness nums target result.1 result.2 ∧
  (∀ i : Nat, ∀ j : Nat,
    IsTwoSumWitness nums target i j → (i = result.1 ∧ j = result.2))

end LLMSpec

section Proof

theorem precondition_equiv (nums : List Int) (target : Int) :
  VerinaSpec.twoSum_precond nums target ↔ LLMSpec.precondition nums target := by
  sorry

theorem postcondition_equiv (nums : List Int) (target : Int) (result: Prod Nat Nat) :
  LLMSpec.precondition nums target →
  (VerinaSpec.twoSum_postcond nums target result ↔ LLMSpec.postcondition nums target result) := by
  sorry

end Proof
