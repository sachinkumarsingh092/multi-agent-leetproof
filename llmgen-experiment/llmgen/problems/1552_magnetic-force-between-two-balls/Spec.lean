import Velvet.Std
import Extensions.Tactics
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false
set_option pp.funBinderTypes true
set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

/- Problem Description
    1552. Magnetic Force Between Two Balls: maximize the minimum distance between any two placed balls.
    **Important: complexity should be O(n log n) time and O(1) space**
    Natural language breakdown:
    1. We are given n basket positions as natural numbers in an array `position`.
    2. The input array `position` is given in ascending sorted order.
    3. We must place exactly m balls into m distinct baskets (so we choose m distinct indices).
    4. The magnetic force between two balls at positions x and y is |x - y|.
    5. For a particular placement, its score is the minimum force among all pairs of chosen baskets.
    6. The required answer is the maximum score achievable over all valid placements.
    7. Constraints imply m ≥ 2 and m ≤ n; basket positions are pairwise distinct.
-/

section Specs
-- Strictly increasing indices inside an array.
def StrictlyIncreasing (idxs : Array Nat) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < idxs.size → idxs[i]! < idxs[j]!

-- All indices are within bounds of the positions array.
def IndicesInRange (pos : Array Nat) (idxs : Array Nat) : Prop :=
  ∀ (k : Nat), k < idxs.size → idxs[k]! < pos.size

-- Pairwise distance lower bound for the chosen indices.
def PairwiseDistGE (pos : Array Nat) (idxs : Array Nat) (d : Nat) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < idxs.size →
    d ≤ (pos[idxs[j]!]!) - (pos[idxs[i]!]!)

-- Feasibility predicate: there exists a selection of exactly m baskets
-- whose pairwise distances are all at least d.
def Feasible (pos : Array Nat) (m : Nat) (d : Nat) : Prop :=
  ∃ (idxs : Array Nat),
    idxs.size = m ∧
    StrictlyIncreasing idxs ∧
    IndicesInRange pos idxs ∧
    PairwiseDistGE pos idxs d

def precondition (position : Array Nat) (m : Nat) : Prop :=
  m ≥ 2 ∧ m ≤ position.size ∧ StrictlyIncreasing position

-- The result is the maximum d such that placing m balls with minimum pairwise distance ≥ d is feasible.
def postcondition (position : Array Nat) (m : Nat) (result : Nat) : Prop :=
  Feasible position m result ∧
  (∀ (d' : Nat), result < d' → ¬ Feasible position m d')
end Specs

section Impl
method MagneticForceBetweenTwoBalls (position : Array Nat) (m : Nat)
  return (result : Nat)
  require precondition position m
  ensures postcondition position m result
  do
  pure 0

end Impl

section TestCases
-- Test case 1: Example 1 (sorted)
-- position = [1,2,3,4,7], m = 3 => 3
def test1_position : Array Nat := #[1, 2, 3, 4, 7]
def test1_m : Nat := 3
def test1_Expected : Nat := 3

-- Test case 2: Example 2 (sorted)
-- position = [1,2,3,4,5,1000000000], m = 2 => 999999999
def test2_position : Array Nat := #[1, 2, 3, 4, 5, 1000000000]
def test2_m : Nat := 2
def test2_Expected : Nat := 999999999

-- Test case 3: Smallest valid n and m (two baskets, two balls)
def test3_position : Array Nat := #[10, 20]
def test3_m : Nat := 2
def test3_Expected : Nat := 10

-- Test case 4: m = n (must place in every basket; answer is min adjacent gap)
def test4_position : Array Nat := #[1, 6, 11, 20]
def test4_m : Nat := 4
def test4_Expected : Nat := 5

-- Test case 5: Spread-out positions; m=2 => max distance between endpoints
def test5_position : Array Nat := #[0, 7, 10, 19]
def test5_m : Nat := 2
def test5_Expected : Nat := 19

-- Test case 6: Many close positions; m=3
-- Choose 0,4,10 gives min distance 4; cannot reach 5.
def test6_position : Array Nat := #[0, 1, 2, 4, 8, 10]
def test6_m : Nat := 3
def test6_Expected : Nat := 4

-- Test case 7: Sorted input; m=3
-- Choose 1,9,17 gives min 8.
def test7_position : Array Nat := #[1, 9, 10, 17]
def test7_m : Nat := 3
def test7_Expected : Nat := 8

-- Test case 8: Symmetric spacing; m=3
-- Choose 0,3,6 yields min 3.
def test8_position : Array Nat := #[0, 2, 3, 5, 6]
def test8_m : Nat := 3
def test8_Expected : Nat := 3

-- Test case 9: Sorted; m=2 (answer is distance between min and max)
def test9_position : Array Nat := #[0, 25, 50, 75, 100]
def test9_m : Nat := 2
def test9_Expected : Nat := 100
end TestCases
