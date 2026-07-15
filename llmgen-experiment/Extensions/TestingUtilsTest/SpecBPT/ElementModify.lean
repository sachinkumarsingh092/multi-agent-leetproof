import Velvet.Std
import Extensions.Testing
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem: UpdateElements

section Specs

register_specdef_allow_recursion

def precondition (a : Array Int) : Prop :=
  a.size ≥ 8

instance instDecidablePrecond (a : Array Int) : Decidable (precondition a) := by
  unfold precondition
  infer_instance

def postcondition (a : Array Int) (result : Array Int) :=
  result[4]! = (a[4]!) + 3 ∧
  result[7]! = 516 ∧
  (∀ i, i < a.size → i ≠ 4 → i ≠ 7 → result[i]! = a[i]!)

end Specs

section Impl

def UpdateElements (a : Array Int) : Array Int :=
  let a1 := a.set! 4 ((a[4]!) + 3)
  let a2 := a1.set! 7 516
  a2

end Impl

section TestCases

def test1_a : Array Int := #[0, 1, 2, 3, 4, 5, 6, 7, 8]
def test1_Expected : Array Int := #[0, 1, 2, 3, 7, 5, 6, 516, 8]

def test2_a : Array Int := #[10, 20, 30, 40, 50, 60, 70, 80]
def test2_Expected : Array Int := #[10, 20, 30, 40, 53, 60, 70, 516]

def test3_a : Array Int := #[-1, -2, -3, -4, -5, -6, -7, -8, -9, -10]
def test3_Expected : Array Int := #[-1, -2, -3, -4, -2, -6, -7, 516, -9, -10]

def uniqueness_test2 (result : Array Int) :
  result ≠ test2_Expected →
  ¬ postcondition test2_a result := by
  -- unfold postcondition test6_arr test6_Expected PairFromDistinctIndices
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  plausible'_mut (seeds := #[test2_Expected])
