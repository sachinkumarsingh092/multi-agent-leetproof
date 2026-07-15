import Velvet.Std
import Extensions.Testing
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem: findEvenNumbers

section Specs

register_specdef_allow_recursion

def isEven (n : Int) : Bool :=
  n % 2 = 0

def precondition (arr : Array Int) : Prop :=
  True

instance instDecidablePrecond (arr : Array Int) : Decidable (precondition arr) := by
  unfold precondition
  infer_instance

def postcondition (arr : Array Int) (result : Array Int) :=
  (∀ x, x ∈ result → isEven x ∧ x ∈ arr.toList) ∧
  (∀ x, x ∈ arr.toList → isEven x → x ∈ result) ∧
  (∀ x y, x ∈ arr.toList → y ∈ arr.toList →
    isEven x → isEven y →
    arr.toList.idxOf x ≤ arr.toList.idxOf y →
    result.toList.idxOf x ≤ result.toList.idxOf y)

end Specs

section Impl

def findEvenNumbers (arr : Array Int) : Array Int :=
  arr.foldl (fun acc x => if isEven x then acc.push x else acc) #[]

end Impl

section TestCases

def test1_arr : Array Int := #[1, 2, 3, 4, 5, 6]
def test1_Expected : Array Int := #[2, 4, 6]

def test2_arr : Array Int := #[7, 8, 10, 13, 14]
def test2_Expected : Array Int := #[8, 10, 14]

def test3_arr : Array Int := #[1, 3, 5, 7]
def test3_Expected : Array Int := #[]

def test4_arr : Array Int := #[]
def test4_Expected : Array Int := #[]

def test5_arr : Array Int := #[0, -2, -3, -4, 5]
def test5_Expected : Array Int := #[0, -2, -4]

end TestCases

set_option maxHeartbeats 500000

def uniqueness_test1 (result : Array Int) :
  result ≠ test1_Expected →
  ¬ postcondition test1_arr result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  plausible'_mut (seeds := #[test1_Expected]) (config := { numInst := 100000 })
