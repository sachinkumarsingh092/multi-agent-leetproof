import Mathlib.Tactic

namespace VerinaSpec


def semiOrderedPermutation_precond (nums : List Int) : Prop :=
  let n := nums.length
  n > 0 ∧
  List.Nodup nums ∧
  nums.all (fun x => 1 ≤ x ∧ x ≤ Int.ofNat n)

def semiOrderedPermutation_postcond (nums : List Int) (result: Int) : Prop :=
  let n := nums.length
  let pos1 := nums.idxOf 1
  let posn := nums.idxOf (Int.ofNat n)
  if pos1 > posn then
    pos1 + n = result + 2 + posn
  else
    pos1 + n = result + 1 + posn

end VerinaSpec

namespace LLMSpec

-- Helper: the intended size n as an Int.
def nVal (nums : List Int) : Int :=
  Int.ofNat nums.length

-- Helper: index of a value, using boolean equality.
-- For valid inputs (permutation of 1..n), the searched elements are present.
def indexOfInt (a : Int) (nums : List Int) : Nat :=
  nums.findIdx (fun x => x == a)

-- Helper: range constraint for permutation elements: every element is in [1..n].
def elemsInRange (nums : List Int) : Prop :=
  ∀ (i : Nat), i < nums.length →
    (1 ≤ nums[i]!) ∧ (nums[i]! ≤ nVal nums)

-- Helper: the swap-count formula (as Nat).
def swapCountNat (nums : List Int) : Nat :=
  let pos1 : Nat := indexOfInt 1 nums
  let posN : Nat := indexOfInt (nVal nums) nums
  let cost1 : Nat := pos1
  let costN : Nat := (nums.length - 1) - posN
  let overlap : Nat := if pos1 > posN then 1 else 0
  cost1 + costN - overlap

-- Preconditions
-- We keep them mostly decidable and avoid heavy permutation machinery.
-- We assume:
-- 1) n = nums.length is at least 1
-- 2) all elements are within [1..n]
-- 3) no duplicates
-- 4) 1 and n actually occur (captured via findIdx bounds)
def precondition (nums : List Int) : Prop :=
  nums.length ≥ 1 ∧
  elemsInRange nums ∧
  nums.Nodup ∧
  indexOfInt 1 nums < nums.length ∧
  indexOfInt (nVal nums) nums < nums.length

-- Postcondition
-- The result is exactly the minimal number of adjacent swaps, characterized by the index-based formula.
-- We return it as an Int equal to the Nat formula coerced to Int.
def postcondition (nums : List Int) (result : Int) : Prop :=
  result = Int.ofNat (swapCountNat nums)

end LLMSpec

section Proof

theorem precondition_equiv (nums : List Int) :
  VerinaSpec.semiOrderedPermutation_precond nums ↔ LLMSpec.precondition nums := by
  sorry

theorem postcondition_equiv (nums : List Int) (result: Int) :
  LLMSpec.precondition nums →
  (VerinaSpec.semiOrderedPermutation_postcond nums result ↔ LLMSpec.postcondition nums result) := by
  sorry

end Proof
