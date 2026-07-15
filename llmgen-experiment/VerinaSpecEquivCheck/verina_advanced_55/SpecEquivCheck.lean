import Mathlib.Tactic
import Std.Data.HashMap

namespace VerinaSpec

open Std

def mostFrequent_precond (xs : List Int) : Prop :=
  xs ≠ []

def countMap (xs : List Int) : HashMap Int Nat :=
  let step := fun m x =>
    let current := m.getD x 0
    m.insert x (current + 1)
  let init := (HashMap.empty : HashMap Int Nat)
  xs.foldl step init

def getMaxFrequency (m : HashMap Int Nat) : Nat :=
  let step := fun acc (_k, v) =>
    if v > acc then v else acc
  let init := 0
  m.toList.foldl step init

def getCandidates (m : HashMap Int Nat) (maxFreq : Nat) : List Int :=
  let isTarget := fun (_k, v) => v = maxFreq
  let extract := fun (k, _) => k
  m.toList.filter isTarget |>.map extract

def getFirstWithFreq (xs : List Int) (candidates : List Int) : Int :=
  match xs.find? (fun x => candidates.contains x) with
  | some x => x
  | none => 0

def mostFrequent_postcond (xs : List Int) (result: Int) : Prop :=
  let count := fun x => xs.countP (fun y => y = x)
  result ∈ xs ∧
  xs.all (fun x => count x ≤ count result) ∧
  ((xs.filter (fun x => count x = count result)).head? = some result)

end VerinaSpec

namespace LLMSpec

-- Helper: first index of `x` in `xs` if present; otherwise `xs.length`.
-- In the postcondition we only compare first indices for values known to be in `xs`.
def firstIndex (xs : List Int) (x : Int) : Nat :=
  (xs.findIdx? (fun y => y = x)).getD xs.length

-- Precondition: input list is non-empty.
def precondition (xs : List Int) : Prop :=
  xs ≠ []

-- Postcondition: `result` is a most frequent element, and among ties it occurs first.
def postcondition (xs : List Int) (result : Int) : Prop :=
  result ∈ xs ∧
  (∀ (y : Int), y ∈ xs → xs.count y ≤ xs.count result) ∧
  (∀ (y : Int), y ∈ xs → xs.count y = xs.count result → firstIndex xs result ≤ firstIndex xs y)

end LLMSpec

section Proof

theorem precondition_equiv (xs : List Int) :
  VerinaSpec.mostFrequent_precond xs ↔ LLMSpec.precondition xs := by
  sorry

theorem postcondition_equiv (xs : List Int) (result: Int) :
  LLMSpec.precondition xs →
  (VerinaSpec.mostFrequent_postcond xs result ↔ LLMSpec.postcondition xs result) := by
  sorry

end Proof
