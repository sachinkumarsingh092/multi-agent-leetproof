import Velvet.Std
import Extensions.Testing
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem: findFirstOccurrence

section Specs

register_specdef_allow_recursion

def precondition (arr : Array Int) (target : Int) : Prop :=
  List.Pairwise (· ≤ ·) arr.toList

instance instDecidablePrecond (arr : Array Int) (target : Int) : Decidable (precondition arr target) := by
  unfold precondition
  infer_instance

def postcondition (arr : Array Int) (target : Int) (result : Int) :=
  (result ≥ 0 →
  arr[result.toNat]! = target ∧
  (∀ i : Nat, i < result.toNat → arr[i]! ≠ target)) ∧
(result = -1 →
  (∀ i : Nat, i < arr.size → arr[i]! ≠ target))

end Specs

section Impl

def findFirstOccurrence (arr : Array Int) (target : Int) : Int :=
  let rec loop (i : Nat) : Int :=
    if i < arr.size then
      let a := arr[i]!
      if a = target then i
      else if a > target then -1
      else loop (i + 1)
    else -1
  loop 0

end Impl

section TestCases

def test1_arr : Array Int := #[1, 2, 2, 3, 4, 5]
def test1_target : Int := 2
def test1_Expected : Int := 1

def test2_arr : Array Int := #[1, 2, 2, 3, 4, 5]
def test2_target : Int := 6
def test2_Expected : Int := -1

def test3_arr : Array Int := #[1, 2, 3, 4, 5]
def test3_target : Int := 1
def test3_Expected : Int := 0

def test4_arr : Array Int := #[1, 2, 3, 4, 5]
def test4_target : Int := 5
def test4_Expected : Int := 4

def test5_arr : Array Int := #[1, 2, 3, 4, 5]
def test5_target : Int := 0
def test5_Expected : Int := -1

end TestCases

set_option maxHeartbeats 500000

def uniqueness_test1'' (result : Int) :
  result ≠ test1_Expected →
  ¬ postcondition test1_arr test1_target result := by
  try dsimp at *
  plausible'_mut (seeds := #[test1_Expected]) (config := { numInst := 100000 })
