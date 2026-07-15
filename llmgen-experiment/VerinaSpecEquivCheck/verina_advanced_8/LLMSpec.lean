import Velvet.Std
import Extensions.Tactics
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false
set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

/- Problem Description
    GasStationCircuit: determine the smallest starting gas station index that permits a full clockwise circuit.

    Natural language breakdown:
    1. We are given two lists of integers `gas` and `cost`.
    2. `gas` and `cost` have equal, non-zero length `n`.
    3. Starting at a chosen station `s` with an empty tank, we repeatedly visit stations clockwise.
    4. At each visited station, we gain `gas[i]` units of fuel, then we must pay `cost[i]` units to travel to the next station.
    5. Indices are circular: after station `n-1`, the next station is station `0`.
    6. A start index `s` is valid if during the `n` moves, the running tank balance never becomes negative.
    7. If at least one valid start index exists, the output is the smallest such index.
    8. If no valid start exists, the output is `-1`.
-/

section Specs
-- Helper: integer sum of a list.
-- We use `foldl` because it is a standard Mathlib/List operation.
def sumIntList (xs : List Int) : Int :=
  xs.foldl (fun acc x => acc + x) 0

-- Helper: circular index; meaningful when `n > 0`.
def circIdx (n : Nat) (i : Nat) : Nat :=
  i % n

-- Helper: net gain at (circular) station index `i`.
def circDiff (gas : List Int) (cost : List Int) (i : Nat) : Int :=
  let n : Nat := gas.length
  let j : Nat := circIdx n i
  gas[j]! - cost[j]!

-- Helper: balance after taking exactly `t` steps starting from `start`.
-- This is a mathematical finite sum over the range `{0,1,...,t-1}`.
def balanceFrom (gas : List Int) (cost : List Int) (start : Nat) (t : Nat) : Int :=
  (Finset.range t).sum (fun k => circDiff gas cost (start + k))

-- Helper: a start index is valid if all prefix balances along the `n` steps are nonnegative.
def validStart (gas : List Int) (cost : List Int) (start : Nat) : Prop :=
  let n : Nat := gas.length
  start < n ∧
    (∀ t : Nat, t ≤ n → 0 ≤ balanceFrom gas cost start t)

-- Helper: existence of some valid start.
def existsValidStart (gas : List Int) (cost : List Int) : Prop :=
  let n : Nat := gas.length
  ∃ s : Nat, s < n ∧ validStart gas cost s

-- Preconditions: lists have equal non-zero length.
def precondition (gas : List Int) (cost : List Int) : Prop :=
  gas.length = cost.length ∧ gas.length > 0

-- Postcondition:
-- * If no valid start exists, result is `-1`.
-- * Otherwise, result is a valid start index (as a nonnegative Int within range)
--   and is minimal among all valid starts.
def postcondition (gas : List Int) (cost : List Int) (result : Int) : Prop :=
  let n : Nat := gas.length
  (result = (-1) ↔ ¬ existsValidStart gas cost) ∧
  (result ≠ (-1) →
      0 ≤ result ∧
      result.toNat < n ∧
      validStart gas cost result.toNat ∧
      (∀ s : Nat, s < n → validStart gas cost s → result.toNat ≤ s))
end Specs

section Impl
method GasStationCircuit (gas : List Int) (cost : List Int)
  return (result : Int)
  require precondition gas cost
  ensures postcondition gas cost result
  do
  pure (-1)  -- placeholder body only

end Impl

section TestCases
-- Test case 1: classic example with unique solution at index 3
-- gas = [1,2,3,4,5], cost = [3,4,5,1,2] => answer 3

def test1_gas : List Int := [1, 2, 3, 4, 5]
def test1_cost : List Int := [3, 4, 5, 1, 2]
def test1_Expected : Int := 3

-- Test case 2: impossible instance (no valid start)

def test2_gas : List Int := [2, 3, 4]
def test2_cost : List Int := [3, 4, 3]
def test2_Expected : Int := (-1)

-- Test case 3: single station feasible (0 is the only index)

def test3_gas : List Int := [5]
def test3_cost : List Int := [4]
def test3_Expected : Int := 0

-- Test case 4: single station infeasible

def test4_gas : List Int := [1]
def test4_cost : List Int := [2]
def test4_Expected : Int := (-1)

-- Test case 5: multiple solutions exist, smallest index required

def test5_gas : List Int := [2, 2, 2]
def test5_cost : List Int := [1, 1, 1]
def test5_Expected : Int := 0

-- Test case 6: all zeros, any start works, smallest index required

def test6_gas : List Int := [0, 0, 0]
def test6_cost : List Int := [0, 0, 0]
def test6_Expected : Int := 0

-- Test case 7: total net zero but smallest valid start is not 0

def test7_gas : List Int := [1, 2, 3]
def test7_cost : List Int := [2, 2, 2]
def test7_Expected : Int := 1

-- Test case 8: includes negative gas value; still feasible from index 1

def test8_gas : List Int := [-1, 5]
def test8_cost : List Int := [0, 3]
def test8_Expected : Int := 1

-- Test case 9: length 2, exact feasibility with smallest index 0

def test9_gas : List Int := [3, 1]
def test9_cost : List Int := [2, 2]
def test9_Expected : Int := 0

-- Recommend to validate: precondition (equal nonzero length), validStart prefix-balance condition, minimality of returned index
end TestCases
