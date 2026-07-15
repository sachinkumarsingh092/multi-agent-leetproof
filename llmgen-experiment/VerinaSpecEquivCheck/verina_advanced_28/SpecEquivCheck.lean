import Mathlib.Tactic
import Std.Data.HashSet
import Mathlib

namespace VerinaSpec

open Std

def longestConsecutive_precond (nums : List Int) : Prop :=
  List.Nodup nums

def isConsecutive (seq : List Int) : Bool :=
  seq.length = 0 ∨ seq.zipIdx.all (fun (x, i) => x = i + seq[0]!)

def longestConsecutive_postcond (nums : List Int) (result: Nat) : Prop :=
  let sorted_nums := nums.mergeSort
  let consec_sublist_lens := List.range nums.length |>.flatMap (fun start =>
    List.range (nums.length - start + 1) |>.map (fun len => sorted_nums.extract start (start + len))) |>.filter isConsecutive |>.map (·.length)
  (nums = [] → result = 0) ∧
  (nums ≠ [] → consec_sublist_lens.contains result ∧ consec_sublist_lens.all (· ≤ result))

end VerinaSpec

namespace LLMSpec

-- An interval [a,b] is fully contained in nums if every integer k with a ≤ k ≤ b appears in nums.
-- We include the side condition a ≤ b to avoid degenerate "backwards" intervals.
def intervalContained (nums : List Int) (a : Int) (b : Int) : Prop :=
  a ≤ b ∧ ∀ (k : Int), a ≤ k ∧ k ≤ b → k ∈ nums

-- The length of an integer interval [a,b] as a natural number.
-- This is only meaningful when a ≤ b; the definition uses Int.toNat, so we pair it with a ≤ b in specs.
def intervalLength (a : Int) (b : Int) : Nat :=
  Int.toNat (b - a + 1)

def precondition (nums : List Int) : Prop :=
  nums.Nodup

def postcondition (nums : List Int) (result : Nat) : Prop :=
  (nums = [] → result = 0) ∧
  (nums ≠ [] →
    (∃ (a : Int) (b : Int),
      intervalContained nums a b ∧
      result = intervalLength a b) ∧
    (∀ (a : Int) (b : Int),
      intervalContained nums a b → intervalLength a b ≤ result) ∧
    (1 ≤ result) ∧
    (result ≤ nums.length))

end LLMSpec

section Proof

theorem precondition_equiv (nums : List Int) :
  VerinaSpec.longestConsecutive_precond nums ↔ LLMSpec.precondition nums := by
  sorry

theorem postcondition_equiv (nums : List Int) (result: Nat) :
  LLMSpec.precondition nums →
  (VerinaSpec.longestConsecutive_postcond nums result ↔ LLMSpec.postcondition nums result) := by
  sorry

end Proof
