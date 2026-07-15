import Velvet.Std
import CaseStudies.TestingUtil
import Extensions.SpecDSL
import Extensions.Testing
import Extensions.VelvetPBT
-- Never add new imports here

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

section Specs

def inArray (a : Array Int) (x : Int) : Bool :=
  a.any (fun y => y = x)

def precondition (a : Array Int) (b : Array Int) : Prop :=
  -- !benchmark @start precond
  True

def postcondition (a : Array Int) (b : Array Int) (result: Array Int) :=
  -- !benchmark @start postcond
  result.all (fun x => inArray a x ≠ inArray b x)∧
  result.toList.Pairwise (· ≤ ·) ∧
  a.all (fun x => if x ∈ b then x ∉ result else x ∈ result) ∧
  b.all (fun x => if x ∈ a then x ∉ result else x ∈ result)

end Specs

section TestCases

def test1_a : Array Int := #[1, 2, 3, 4]
def test1_b : Array Int := #[3, 4, 5, 6]
def test1_Expected : Array Int := #[1, 2, 5, 6]

def test2_a : Array Int := #[1]
def test2_b : Array Int := #[2]
def test2_Expected : Array Int := #[1, 2]

end TestCases

def uniqueness_test1 (result : Array Int) :
  result ≠ test1_Expected →
  ¬ postcondition test1_a test1_b result := by
  -- unfold postcondition test6_arr test6_Expected PairFromDistinctIndices
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  plausible' (config := { numInst := 30000, numRetries := 1 })

def uniqueness_test1' (result : Array Int) :
  result ≠ test1_Expected →
  ¬ postcondition test1_a test1_b result := by
  -- unfold postcondition test6_arr test6_Expected PairFromDistinctIndices
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible' (config := { numInst := 30000, numRetries := 1 })

def uniqueness_test2 (result : Array Int) :
  result ≠ test2_Expected →
  ¬ postcondition test2_a test2_b result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  plausible' (config := { numInst := 100000, numRetries := 1 })

def uniqueness_test2' (result : Array Int) :
  result ≠ test2_Expected →
  ¬ postcondition test2_a test2_b result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible' (config := { numInst := 100000, numRetries := 1 })
