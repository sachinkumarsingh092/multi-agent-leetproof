import Mathlib.Tactic

namespace VerinaSpec


def nextGreaterElement_precond (nums1 : List Int) (nums2 : List Int) : Prop :=
  List.Nodup nums1 ∧
  List.Nodup nums2 ∧
  nums1.all (fun x => x ∈ nums2)

def nextGreaterElement_postcond (nums1 : List Int) (nums2 : List Int) (result: List Int) : Prop :=
  result.length = nums1.length ∧
  (List.range nums1.length |>.all (fun i =>
    let val := nums1[i]!
    let resultVal := result[i]!
    let j := nums2.findIdx? (fun x => x == val)
    match j with
    | none => false
    | some idx =>
      let nextGreater := (List.range (nums2.length - idx - 1)).find? (fun k =>
        let pos := idx + k + 1
        nums2[pos]! > val
      )
      match nextGreater with
      | none => resultVal = -1
      | some offset => resultVal = nums2[idx + offset + 1]!
  )) ∧
  (result.all (fun val =>
    val = -1 ∨ val ∈ nums2
  ))

end VerinaSpec

namespace LLMSpec

-- Helper predicate: x occurs at index i in list l.
-- We use Nat indices and `l[i]!` for safe indexing under the bound proof.
def At (l : List Int) (i : Nat) (x : Int) : Prop :=
  i < l.length ∧ l[i]! = x

-- Helper predicate: y is the next greater element of x in nums2.
-- This is defined via positions ix and iy in nums2:
--   * x is at ix, y is at iy, and ix < iy
--   * y is strictly greater than x
--   * among all elements to the right of ix that are > x, iy is the least index
--     (i.e., there is no earlier position between ix and iy with value > x).
def IsNextGreater (nums2 : List Int) (x : Int) (y : Int) : Prop :=
  ∃ (ix : Nat) (iy : Nat),
    At nums2 ix x ∧
    At nums2 iy y ∧
    ix < iy ∧
    x < y ∧
    (∀ (j : Nat), j < nums2.length → ix < j → nums2[j]! > x → iy ≤ j)

-- Helper predicate: x has no greater element to its right in nums2.
def HasNoGreaterToRight (nums2 : List Int) (x : Int) : Prop :=
  ∃ (ix : Nat),
    At nums2 ix x ∧
    (∀ (j : Nat), j < nums2.length → ix < j → nums2[j]! ≤ x)

-- Preconditions:
-- 1) nums1 and nums2 contain no duplicates
-- 2) every element of nums1 occurs in nums2

def precondition (nums1 : List Int) (nums2 : List Int) : Prop :=
  nums1.Nodup ∧
  nums2.Nodup ∧
  (∀ (x : Int), x ∈ nums1 → x ∈ nums2)

-- Postconditions:
-- 1) result has the same length as nums1
-- 2) for each i, result[i] is either -1 (and there is no greater element to the right in nums2),
--    or a value y that is the first greater element to the right.

def postcondition (nums1 : List Int) (nums2 : List Int) (result : List Int) : Prop :=
  result.length = nums1.length ∧
  (∀ (i : Nat), i < nums1.length →
    let x : Int := nums1[i]!
    (result[i]! = (-1) ∧ HasNoGreaterToRight nums2 x) ∨
    (result[i]! ≠ (-1) ∧ IsNextGreater nums2 x (result[i]!)))

end LLMSpec

section Proof

theorem precondition_equiv (nums1 : List Int) (nums2 : List Int) :
  VerinaSpec.nextGreaterElement_precond nums1 nums2 ↔ LLMSpec.precondition nums1 nums2 := by
  sorry

theorem postcondition_equiv (nums1 : List Int) (nums2 : List Int) (result: List Int) :
  LLMSpec.precondition nums1 nums2 →
  (VerinaSpec.nextGreaterElement_postcond nums1 nums2 result ↔ LLMSpec.postcondition nums1 nums2 result) := by
  sorry

end Proof
