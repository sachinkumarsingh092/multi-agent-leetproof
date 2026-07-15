import Velvet.Std
import Extensions.Testing
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem: canCompleteCircuit

section Specs

register_specdef_allow_recursion

def precondition (gas : List Int) (cost : List Int) : Prop :=
  gas.length > 0 ∧ gas.length = cost.length

instance instDecidablePrecond (gas : List Int) (cost : List Int) : Decidable (precondition gas cost) := by
  unfold precondition
  infer_instance

def postcondition (gas : List Int) (cost : List Int) (result : Int) :=
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

section Impl

def canCompleteCircuit (gas : List Int) (cost : List Int) : Int :=
  let totalGas := gas.foldl (· + ·) 0
    let totalCost := cost.foldl (· + ·) 0

    if totalGas < totalCost then
      -1
    else
      let rec loop (g c : List Int) (idx : Nat) (tank : Int) (start : Nat) : Int :=
        match g, c with
        | [], [] => start
        | gi :: gs, ci :: cs =>
          let tank' := tank + gi - ci
          if tank' < 0 then
            loop gs cs (idx + 1) 0 (idx + 1)
          else
            loop gs cs (idx + 1) tank' start
        | _, _ => -1  -- lengths don’t match

      let zipped := List.zip gas cost
      let rec walk (pairs : List (Int × Int)) (i : Nat) (tank : Int) (start : Nat) : Int :=
        match pairs with
        | [] => start
        | (g, c) :: rest =>
          let newTank := tank + g - c
          if newTank < 0 then
            walk rest (i + 1) 0 (i + 1)
          else
            walk rest (i + 1) newTank start

      walk zipped 0 0 0

end Impl

section TestCases

def test1_gas : List Int := [1, 2, 3, 4, 5]
def test1_cost : List Int := [3, 4, 5, 1, 2]
def test1_Expected : Int := 3

def test2_gas : List Int := [2, 3, 4]
def test2_cost : List Int := [3, 4, 3]
def test2_Expected : Int := -1

def test3_gas : List Int := [5, 1, 2, 3, 4]
def test3_cost : List Int := [4, 4, 1, 5, 1]
def test3_Expected : Int := 4

def test4_gas : List Int := [3, 3, 4]
def test4_cost : List Int := [3, 4, 4]
def test4_Expected : Int := -1

def test5_gas : List Int := [1, 2, 3]
def test5_cost : List Int := [1, 2, 3]
def test5_Expected : Int := 0

def test6_gas : List Int := [1, 2, 3, 4]
def test6_cost : List Int := [2, 2, 2, 2]
def test6_Expected : Int := 1

def test7_gas : List Int := [0, 0, 0]
def test7_cost : List Int := [1, 1, 1]
def test7_Expected : Int := -1

end TestCases

set_option maxHeartbeats 500000

def uniqueness_test1'' (result : Int) :
  result ≠ test1_Expected →
  ¬ postcondition test1_gas test1_cost result := by
  try dsimp at *
  plausible'_mut (seeds := #[test1_Expected]) (config := { numInst := 100000 })
