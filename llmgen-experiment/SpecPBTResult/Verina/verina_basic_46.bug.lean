import Velvet.Std
import Extensions.Testing
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem: lastPosition

section Specs

register_specdef_allow_recursion

def precondition (arr : Array Int) (elem : Int) : Prop :=
  List.Pairwise (· ≤ ·) arr.toList

instance instDecidablePrecond (arr : Array Int) (elem : Int) : Decidable (precondition arr elem) := by
  unfold precondition
  infer_instance

def postcondition (arr : Array Int) (elem : Int) (result : Int) :=
  (result ≥ 0 →
    arr[result.toNat]! = elem ∧ (arr.toList.drop (result.toNat + 1)).all (· ≠ elem)) ∧
  (result = -1 → arr.toList.all (· ≠ elem))

end Specs

section Impl

def lastPosition (arr : Array Int) (elem : Int) : Int :=
  let rec loop (i : Nat) (pos : Int) : Int :=
      if i < arr.size then
        let a := arr[i]!
        if a = elem then loop (i + 1) i
        else loop (i + 1) pos
      else pos
    loop 0 (-1)

end Impl

section TestCases

def test1_arr : Array Int := #[1, 2, 2, 3, 4, 5]
def test1_elem : Int := 2
def test1_Expected : Int := 2

def test2_arr : Array Int := #[1, 2, 2, 3, 4, 5]
def test2_elem : Int := 6
def test2_Expected : Int := -1

def test3_arr : Array Int := #[1, 2, 2, 3, 4, 5]
def test3_elem : Int := 5
def test3_Expected : Int := 5

def test4_arr : Array Int := #[1]
def test4_elem : Int := 1
def test4_Expected : Int := 0

def test5_arr : Array Int := #[1, 1, 1, 1]
def test5_elem : Int := 1
def test5_Expected : Int := 3

def test6_arr : Array Int := #[2, 2, 3, 3, 3]
def test6_elem : Int := 3
def test6_Expected : Int := 4

end TestCases

set_option maxHeartbeats 500000

def uniqueness_test1 (result : Int) :
  result ≠ test1_Expected →
  ¬ postcondition test1_arr test1_elem result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  plausible'_mut (seeds := #[test1_Expected]) (config := { numInst := 100000 })
