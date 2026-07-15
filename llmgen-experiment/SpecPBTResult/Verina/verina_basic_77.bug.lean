import Velvet.Std
import Extensions.Testing
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem: modify_array_element

section Specs

register_specdef_allow_recursion

def precondition (arr : Array (Array Nat)) (index1 : Nat) (index2 : Nat) (val : Nat) : Prop :=
  index1 < arr.size ∧
index2 < (arr[index1]!).size

instance instDecidablePrecond (arr : Array (Array Nat)) (index1 : Nat) (index2 : Nat) (val : Nat) : Decidable (precondition arr index1 index2 val) := by
  unfold precondition
  infer_instance

def postcondition (arr : Array (Array Nat)) (index1 : Nat) (index2 : Nat) (val : Nat) (result : Array (Array Nat)) :=
  (∀ i, i < arr.size → i ≠ index1 → result[i]! = arr[i]!) ∧
(∀ j, j < (arr[index1]!).size → j ≠ index2 → (result[index1]!)[j]! = (arr[index1]!)[j]!) ∧
((result[index1]!)[index2]! = val)

end Specs

section Impl

def updateInner (a : Array Nat) (idx val : Nat) : Array Nat :=
  a.set! idx val

def modify_array_element (arr : Array (Array Nat)) (index1 : Nat) (index2 : Nat) (val : Nat) : Array (Array Nat) :=
  let inner := arr[index1]!
  let inner' := updateInner inner index2 val
  arr.set! index1 inner'

end Impl

section TestCases

def test1_arr : Array (Array Nat) := #[#[1, 2, 3], #[4, 5, 6]]
def test1_index1 : Nat := 0
def test1_index2 : Nat := 1
def test1_val : Nat := 99
def test1_Expected : Array (Array Nat) := #[#[1, 99, 3], #[4, 5, 6]]

def test2_arr : Array (Array Nat) := #[#[7, 8], #[9, 10]]
def test2_index1 : Nat := 1
def test2_index2 : Nat := 0
def test2_val : Nat := 0
def test2_Expected : Array (Array Nat) := #[#[7, 8], #[0, 10]]

def test3_arr : Array (Array Nat) := #[#[0, 0, 0]]
def test3_index1 : Nat := 0
def test3_index2 : Nat := 2
def test3_val : Nat := 5
def test3_Expected : Array (Array Nat) := #[#[0, 0, 5]]

def test4_arr : Array (Array Nat) := #[#[3, 4, 5], #[6, 7, 8], #[9, 10, 11]]
def test4_index1 : Nat := 2
def test4_index2 : Nat := 1
def test4_val : Nat := 100
def test4_Expected : Array (Array Nat) := #[#[3, 4, 5], #[6, 7, 8], #[9, 100, 11]]

def test5_arr : Array (Array Nat) := #[#[1]]
def test5_index1 : Nat := 0
def test5_index2 : Nat := 0
def test5_val : Nat := 42
def test5_Expected : Array (Array Nat) := #[#[42]]

end TestCases

set_option maxHeartbeats 500000

def uniqueness_test1 (result : Array (Array Nat)) :
  result ≠ test1_Expected →
  ¬ postcondition test1_arr test1_index1 test1_index2 test1_val result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  plausible'_mut (seeds := #[test1_Expected]) (config := { numInst := 100000 })
