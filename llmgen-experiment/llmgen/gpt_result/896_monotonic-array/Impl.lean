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
    896. Monotonic Array: decide whether an integer array is monotone increasing or monotone decreasing.
    **Important: complexity should be O(n) time and O(1) space**
    Natural language breakdown:
    1. Input is an array of integers `nums`.
    2. `nums` is monotone increasing if for all indices i and j with i ≤ j, we have nums[i] ≤ nums[j].
    3. `nums` is monotone decreasing if for all indices i and j with i ≤ j, we have nums[i] ≥ nums[j].
    4. The array is monotonic if it is monotone increasing or monotone decreasing.
    5. The function returns `true` exactly when the input array is monotonic, otherwise `false`.
    6. Empty arrays and single-element arrays are monotonic (both conditions hold vacuously).
-/

section Specs
-- A property-based definition of monotone increasing over Array Int using Nat indices.
-- We quantify over all i ≤ j that are valid indices.
def monotoneIncreasing (nums : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < nums.size → j < nums.size → i ≤ j → nums[i]! ≤ nums[j]!

-- A property-based definition of monotone decreasing over Array Int using Nat indices.
def monotoneDecreasing (nums : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < nums.size → j < nums.size → i ≤ j → nums[i]! ≥ nums[j]!

def monotonic (nums : Array Int) : Prop :=
  monotoneIncreasing nums ∨ monotoneDecreasing nums

def precondition (nums : Array Int) : Prop :=
  True

def postcondition (nums : Array Int) (result : Bool) : Prop :=
  (result = true ↔ monotonic nums) ∧
  (result = false ↔ ¬ monotonic nums)
end Specs

section Impl
method MonotonicArray (nums : Array Int)
  return (result : Bool)
  require precondition nums
  ensures postcondition nums result
  do
  -- O(n) time, O(1) extra space
  if nums.size ≤ 1 then
    return true
  else
    let mut inc : Bool := true
    let mut dec : Bool := true
    let mut i : Nat := 1
    while i < nums.size
      -- i stays within bounds; needed for safe indexing at i-1 and i
      invariant "inv_bounds" (1 ≤ i ∧ i ≤ nums.size)
      -- If inc is true, the prefix nums[0..i) is monotone increasing (pairwise)
      -- Init: for i=1 holds trivially. Preserve: if inc remains true then prev ≤ cur extends pairwise order.
      invariant "inv_inc_prefix" (inc = true → ∀ a b : Nat, a < i → b < i → a ≤ b → nums[a]! ≤ nums[b]!)
      -- If dec is true, the prefix nums[0..i) is monotone decreasing (pairwise)
      invariant "inv_dec_prefix" (dec = true → ∀ a b : Nat, a < i → b < i → a ≤ b → nums[a]! ≥ nums[b]!)
      -- If the whole array is monotone increasing, inc can never be falsified by an adjacent comparison
      invariant "inv_global_inc" (monotoneIncreasing nums → inc = true)
      -- If the whole array is monotone decreasing, dec can never be falsified by an adjacent comparison
      invariant "inv_global_dec" (monotoneDecreasing nums → dec = true)
      decreasing nums.size - i
    do
      let prev := nums[i-1]!
      let cur := nums[i]!
      if prev < cur then
        dec := false
      else
        if prev > cur then
          inc := false
      i := i + 1
    return (inc || dec)
end Impl

section TestCases
-- Test case 1: Example 1
-- Input: [1,2,2,3]
-- Output: true
def test1_nums : Array Int := #[1, 2, 2, 3]
def test1_Expected : Bool := true

-- Test case 2: Example 2
-- Input: [6,5,4,4]
-- Output: true
def test2_nums : Array Int := #[6, 5, 4, 4]
def test2_Expected : Bool := true

-- Test case 3: Example 3
-- Input: [1,3,2]
-- Output: false
def test3_nums : Array Int := #[1, 3, 2]
def test3_Expected : Bool := false

-- Test case 4: Empty array (vacuously monotonic)
def test4_nums : Array Int := #[]
def test4_Expected : Bool := true

-- Test case 5: Singleton array (vacuously monotonic)
def test5_nums : Array Int := #[0]
def test5_Expected : Bool := true

-- Test case 6: Constant array (both increasing and decreasing)
def test6_nums : Array Int := #[2, 2, 2, 2]
def test6_Expected : Bool := true

-- Test case 7: Strictly increasing with negatives and positives (covers -1,0,1)
def test7_nums : Array Int := #[-1, 0, 1]
def test7_Expected : Bool := true

-- Test case 8: Strictly decreasing with negatives and positives (covers 1,0,-1)
def test8_nums : Array Int := #[1, 0, -1]
def test8_Expected : Bool := true

-- Test case 9: Not monotonic due to a rise then fall
def test9_nums : Array Int := #[1, 2, 1, 2]
def test9_Expected : Bool := false
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((MonotonicArray test1_nums).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((MonotonicArray test2_nums).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((MonotonicArray test3_nums).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((MonotonicArray test4_nums).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((MonotonicArray test5_nums).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((MonotonicArray test6_nums).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((MonotonicArray test7_nums).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((MonotonicArray test8_nums).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((MonotonicArray test9_nums).run), DivM.res test9_Expected ]
end Assertions

section Pbt
velvet_plausible_test MonotonicArray (config := { maxMs := some 20000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000

theorem goal_0
    (nums : Array ℤ)
    (if_neg : ¬nums.size ≤ OfNat.ofNat 1)
    (i_1 : Bool)
    (i_2 : ℕ)
    (inc_1 : Bool)
    (invariant_inv_global_dec : monotoneDecreasing nums → i_1 = true)
    (a : OfNat.ofNat 1 ≤ i_2)
    (a_1 : i_2 ≤ nums.size)
    (done_1 : ¬i_2 < nums.size)
    (invariant_inv_dec_prefix : i_1 = true → ∀ (a b : ℕ), a < i_2 → b < i_2 → a ≤ b → nums[a]! ≥ nums[b]!)
    (invariant_inv_global_inc : monotoneIncreasing nums → inc_1 = true)
    (invariant_inv_inc_prefix : inc_1 = true → ∀ (a b : ℕ), a < i_2 → b < i_2 → a ≤ b → nums[a]! ≤ nums[b]!)
    : postcondition nums (inc_1 || i_1) := by
    intros; expose_names; try simp_all; try grind


prove_correct MonotonicArray by
  loom_solve <;> (try injections; try subst_vars; try (conv => congr <;> simp) ; try expose_names)
  exact (goal_0 nums if_neg i_1 i_2 inc_1 invariant_inv_global_dec a a_1 done_1 invariant_inv_dec_prefix invariant_inv_global_inc invariant_inv_inc_prefix)
end Proof
