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
    TrappingRainWater: compute how much water can be trapped between elevations after it rains.
    Natural language breakdown:
    1. The input is a list of natural numbers representing bar heights (non-negative elevations).
    2. For each index i within the list length, define leftMax(i) as the maximum height among indices 0..i.
    3. For each index i within the list length, define rightMax(i) as the maximum height among indices i..(n-1).
    4. The water level above index i is limited by min(leftMax(i), rightMax(i)).
    5. The trapped water at index i is max(0, min(leftMax(i), rightMax(i)) - height[i]).
       Since we work in Nat, truncated subtraction `a - b` already represents max(0, a-b).
    6. The total trapped water is the sum of trapped water at every valid index i.
    7. Edge cases:
       a. An empty list traps 0 water.
       b. A singleton list traps 0 water.
-/

section Specs
-- A characterization that `m` is the maximum height on the prefix {0..i} (inclusive),
-- assuming `i` is a valid index (< height.length).
-- This is expressed as:
--   (1) every prefix element is ≤ m (upper bound)
--   (2) some prefix element equals m (attainment)
def isPrefixMax (height : List Nat) (i : Nat) (m : Nat) : Prop :=
  i < height.length ∧
  (∀ (j : Nat), j ≤ i → j < height.length → height[j]! ≤ m) ∧
  (∃ (j : Nat), j ≤ i ∧ j < height.length ∧ height[j]! = m)

-- A characterization that `m` is the maximum height on the suffix {i..n-1} (inclusive),
-- assuming `i` is a valid index (< height.length).
def isSuffixMax (height : List Nat) (i : Nat) (m : Nat) : Prop :=
  i < height.length ∧
  (∀ (j : Nat), i ≤ j → j < height.length → height[j]! ≤ m) ∧
  (∃ (j : Nat), i ≤ j ∧ j < height.length ∧ height[j]! = m)

-- Water trapped at index i; defined as 0 for out-of-bounds indices to keep it total.
def waterAt (height : List Nat) (i : Nat) : Nat :=
  if h : i < height.length then
    let hi : Nat := height[i]!
    -- Choose left/right maxima concretely for the computation; the postcondition will relate them
    -- to the abstract maximum characterization.
    let lmax : Nat := (height.take (i + 1)).foldl Nat.max 0
    let rmax : Nat := (height.drop i).foldl Nat.max 0
    (Nat.min lmax rmax) - hi
  else
    0

-- Precondition: no restrictions beyond the stated domain (List Nat is already non-negative).
-- We mention `height` to avoid unused-variable warnings.
def precondition (height : List Nat) : Prop :=
  height.length = height.length

-- Postcondition:
-- There exist functions L and R giving, for each valid index i,
-- the prefix and suffix maxima respectively.
-- The result is the sum over indices of min(L i, R i) - height[i] (truncated subtraction).
def postcondition (height : List Nat) (result : Nat) : Prop :=
  let n : Nat := height.length
  (∃ (L : Nat → Nat),
    (∀ (i : Nat), i < n → isPrefixMax height i (L i)) ∧
    (∃ (R : Nat → Nat),
      (∀ (i : Nat), i < n → isSuffixMax height i (R i)) ∧
      result = (List.range n).foldl
        (fun (acc : Nat) (i : Nat) => acc + (Nat.min (L i) (R i) - height[i]!))
        0))
end Specs

section Impl
method TrappingRainWater (height : List Nat)
  return (result : Nat)
  require precondition height
  ensures postcondition height result
  do
    pure 0

end Impl

section TestCases
-- Test case 1: classic example
-- heights = [0,1,0,2,1,0,1,3,2,1,2,1] traps 6

def test1_height : List Nat := [0, 1, 0, 2, 1, 0, 1, 3, 2, 1, 2, 1]
def test1_Expected : Nat := 6

-- Test case 2: another standard example
-- heights = [4,2,0,3,2,5] traps 9

def test2_height : List Nat := [4, 2, 0, 3, 2, 5]
def test2_Expected : Nat := 9

-- Test case 3: empty list traps 0

def test3_height : List Nat := []
def test3_Expected : Nat := 0

-- Test case 4: singleton list traps 0

def test4_height : List Nat := [7]
def test4_Expected : Nat := 0

-- Test case 5: simple bowl [2,0,2] traps 2

def test5_height : List Nat := [2, 0, 2]
def test5_Expected : Nat := 2

-- Test case 6: strictly increasing traps 0

def test6_height : List Nat := [0, 1, 2, 3]
def test6_Expected : Nat := 0

-- Test case 7: strictly decreasing traps 0

def test7_height : List Nat := [3, 2, 1, 0]
def test7_Expected : Nat := 0

-- Test case 8: all equal plateau traps 0

def test8_height : List Nat := [3, 3, 3]
def test8_Expected : Nat := 0

-- Test case 9: wide valley [5,0,0,0,5] traps 15

def test9_height : List Nat := [5, 0, 0, 0, 5]
def test9_Expected : Nat := 15

-- Test case 10: small valley with multiple basins
-- heights = [1,0,2,0,1] traps 2

def test10_height : List Nat := [1, 0, 2, 0, 1]
def test10_Expected : Nat := 2

-- Recommend to validate: empty/singleton, monotone cases, classic multi-basin example
end TestCases
