import Velvet.Std
import CaseStudies.TestingUtil
import Extensions.SpecDSL
import Extensions.Testing
import Extensions.VelvetPBT
-- Never add new imports here

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

section Specs

def precondition (gas : List Int) (cost : List Int) : Prop :=
  -- !benchmark @start precond
  gas.length > 0 ∧ gas.length = cost.length

def postcondition (gas : List Int) (cost : List Int) (result: Int) : Prop :=
  -- !benchmark @start postcond
  let valid (start : Nat) := List.range gas.length |>.all (fun i =>
    let acc := List.range (i + 1) |>.foldl (fun t j =>
      let jdx := (start + j) % gas.length
      t + gas[jdx]! - cost[jdx]!) 0
    acc ≥ 0)
  -- For result = -1: It's impossible to complete the circuit starting from any index
  -- In other words, there's no starting point from which we can always maintain a non-negative gas tank
  (result = -1 → (List.range gas.length).all (fun start => ¬ valid start)) ∧
  -- For result ≥ 0: This is the valid starting point
  -- When starting from this index, the gas tank never becomes negative during the entire circuit
  (result ≥ 0 → result < gas.length ∧ valid result.toNat ∧ (List.range result.toNat).all (fun start => ¬ valid start))

end Specs

def test1_gas := [3, 3, 4]
def test1_cost := [3, 4, 4]
def test1_Expected := -1

def uniqueness_test1 (result : Int) :
  result ≠ test1_Expected →
  ¬ postcondition test1_gas test1_cost result := by
  -- unfold postcondition test6_arr test6_Expected PairFromDistinctIndices
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop
  plausible' (config := { numInst := 30000, numRetries := 1 })
