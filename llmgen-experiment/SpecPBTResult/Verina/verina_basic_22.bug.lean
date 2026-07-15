import Velvet.Std
import Extensions.Testing
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem: dissimilarElements

section Specs

register_specdef_allow_recursion

def inArray (a : Array Int) (x : Int) : Bool :=
  a.any (fun y => y = x)

def precondition (a : Array Int) (b : Array Int) : Prop :=
  True

instance instDecidablePrecond (a : Array Int) (b : Array Int) : Decidable (precondition a b) := by
  unfold precondition
  infer_instance

def postcondition (a : Array Int) (b : Array Int) (result : Array Int) :=
  result.all (fun x => inArray a x ≠ inArray b x)∧
  result.toList.Pairwise (· ≤ ·) ∧
  a.all (fun x => if x ∈ b then x ∉ result else x ∈ result) ∧
  b.all (fun x => if x ∈ a then x ∉ result else x ∈ result)

end Specs

section Impl

def dissimilarElements (a : Array Int) (b : Array Int) : Array Int :=
  let res := a.foldl (fun acc x => if !inArray b x then acc.insert x else acc) Std.HashSet.empty
    let res := b.foldl (fun acc x => if !inArray a x then acc.insert x else acc) res
    res.toArray.insertionSort

end Impl

section TestCases

def test1_a : Array Int := #[1, 2, 3, 4]
def test1_b : Array Int := #[3, 4, 5, 6]
def test1_Expected : Array Int := #[1, 2, 5, 6]

def test2_a : Array Int := #[1, 1, 2]
def test2_b : Array Int := #[2, 3]
def test2_Expected : Array Int := #[1, 3]

def test3_a : Array Int := #[]
def test3_b : Array Int := #[4, 5]
def test3_Expected : Array Int := #[4, 5]

def test4_a : Array Int := #[7, 8]
def test4_b : Array Int := #[]
def test4_Expected : Array Int := #[7, 8]

def test5_a : Array Int := #[1, 2, 3]
def test5_b : Array Int := #[1, 2, 3]
def test5_Expected : Array Int := #[]

def test6_a : Array Int := #[1, 2, 3]
def test6_b : Array Int := #[4, 5, 6]
def test6_Expected : Array Int := #[1, 2, 3, 4, 5, 6]

def test7_a : Array Int := #[-1, 0, 1]
def test7_b : Array Int := #[0]
def test7_Expected : Array Int := #[-1, 1]

end TestCases

set_option maxHeartbeats 500000

def uniqueness_test1 (result : Array Int) :
  result ≠ test1_Expected →
  ¬ postcondition test1_a test1_b result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  plausible'_mut (seeds := #[test1_Expected]) (config := { numInst := 100000 })
