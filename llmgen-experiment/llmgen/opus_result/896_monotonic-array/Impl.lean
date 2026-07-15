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
  if nums.size <= 1 then
    return true
  else
    let mut isIncr := true
    let mut isDecr := true
    let mut i : Nat := 1
    while i < nums.size
      -- i is bounded: starts at 1, incremented up to nums.size
      invariant "i_lower" 1 ≤ i
      invariant "i_upper" i ≤ nums.size
      -- Size context from the else branch
      invariant "size_gt_1" nums.size > 1
      -- Adjacent formulation: isIncr/isDecr track adjacent pair comparisons up to index i
      -- Init: at i=1, vacuously true for both directions. Preservation: extends by one adjacent pair.
      invariant "isIncr_adj" (isIncr = true ↔ ∀ (k : Nat), 1 ≤ k ∧ k < i → nums[k-1]! ≤ nums[k]!)
      invariant "isDecr_adj" (isDecr = true ↔ ∀ (k : Nat), 1 ≤ k ∧ k < i → nums[k-1]! ≥ nums[k]!)
      -- Global formulation: directly matches monotoneIncreasing/monotoneDecreasing at loop exit
      -- Init: at i=1, only index 0 exists so all pairs (a,b) with a<1,b<1,a≤b trivially satisfy.
      -- Sufficiency: when i=nums.size, this becomes exactly the definition of monotoneIncreasing/monotoneDecreasing.
      invariant "isIncr_global" (isIncr = true ↔ ∀ (a b : Nat), a < i → b < i → a ≤ b → nums[a]! ≤ nums[b]!)
      invariant "isDecr_global" (isDecr = true ↔ ∀ (a b : Nat), a < i → b < i → a ≤ b → nums[a]! ≥ nums[b]!)
      decreasing nums.size - i
    do
      if nums[i - 1]! > nums[i]! then
        isIncr := false
      if nums[i - 1]! < nums[i]! then
        isDecr := false
      i := i + 1
    return (isIncr || isDecr)
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
    (i : ℕ)
    (isDecr : Bool)
    (invariant_i_lower : OfNat.ofNat 1 ≤ i)
    (invariant_isDecr_global : isDecr = true ↔ ∀ (a b : ℕ), a < i → b < i → a ≤ b → nums[b]! ≤ nums[a]!)
    (if_neg_1 : nums[i]! ≤ nums[i - OfNat.ofNat 1]!)
    : isDecr = true ↔ ∀ (a b : ℕ), a < i + OfNat.ofNat 1 → b < i + OfNat.ofNat 1 → a ≤ b → nums[b]! ≤ nums[a]! := by
    have h1 : OfNat.ofNat 1 = 1 := rfl
    rw [h1] at *
    constructor
    · intro h
      have hg := invariant_isDecr_global.mp h
      intro a b ha hb hab
      by_cases hbeq : b < i
      · exact hg a b (by omega) hbeq hab
      · have hb_eq_i : b = i := by omega
        by_cases haeq : a < i
        · have hi_sub_lt : i - 1 < i := by omega
          have ha_le : a ≤ i - 1 := by omega
          have h2 : nums[i - 1]! ≤ nums[a]! := hg a (i - 1) haeq hi_sub_lt ha_le
          rw [hb_eq_i]
          exact le_trans if_neg_1 h2
        · have ha_eq_i : a = i := by omega
          rw [hb_eq_i, ha_eq_i]
    · intro h
      rw [invariant_isDecr_global]
      intro a b ha hb hab
      exact h a b (by omega) (by omega) hab

theorem goal_1
    (nums : Array ℤ)
    (i : ℕ)
    (isIncr : Bool)
    (invariant_i_lower : OfNat.ofNat 1 ≤ i)
    (invariant_isIncr_global : isIncr = true ↔ ∀ (a b : ℕ), a < i → b < i → a ≤ b → nums[a]! ≤ nums[b]!)
    (if_neg_1 : nums[i - OfNat.ofNat 1]! ≤ nums[i]!)
    : isIncr = true ↔ ∀ (a b : ℕ), a < i + OfNat.ofNat 1 → b < i + OfNat.ofNat 1 → a ≤ b → nums[a]! ≤ nums[b]! := by
    have h1le : (1 : ℕ) ≤ i := invariant_i_lower
    constructor
    · intro hIncr a b ha hb hab
      have hOld := invariant_isIncr_global.mp hIncr
      have ha' : a ≤ i := Nat.lt_succ_iff.mp ha
      have hb' : b ≤ i := Nat.lt_succ_iff.mp hb
      by_cases hbi : b < i
      · exact hOld a b (Nat.lt_of_le_of_lt hab hbi) hbi hab
      · have hbeq : b = i := Nat.le_antisymm hb' (Nat.le_of_not_lt hbi)
        by_cases hai : a < i
        · have h1 : i - 1 < i := Nat.sub_one_lt_of_le h1le (Nat.le_refl i)
          have h2 : a ≤ i - 1 := Nat.le_sub_one_of_lt hai
          have h3 := hOld a (i - 1) hai h1 h2
          rw [hbeq]
          exact le_trans h3 if_neg_1
        · have haeq : a = i := Nat.le_antisymm ha' (Nat.le_of_not_lt hai)
          rw [haeq, hbeq]
    · intro hNew
      rw [invariant_isIncr_global]
      intro a b ha hb hab
      have ha' : a < i + OfNat.ofNat 1 := Nat.lt_of_lt_of_le ha (Nat.le_succ i)
      have hb' : b < i + OfNat.ofNat 1 := Nat.lt_of_lt_of_le hb (Nat.le_succ i)
      exact hNew a b ha' hb' hab

theorem goal_2
    (nums : Array ℤ)
    (i : ℕ)
    (isIncr : Bool)
    (invariant_i_lower : OfNat.ofNat 1 ≤ i)
    (invariant_isIncr_global : isIncr = true ↔ ∀ (a b : ℕ), a < i → b < i → a ≤ b → nums[a]! ≤ nums[b]!)
    (if_neg_1 : nums[i - OfNat.ofNat 1]! ≤ nums[i]!)
    : isIncr = true ↔ ∀ (a b : ℕ), a < i + OfNat.ofNat 1 → b < i + OfNat.ofNat 1 → a ≤ b → nums[a]! ≤ nums[b]! := by
    intros; expose_names; exact
        goal_1 nums i isIncr invariant_i_lower invariant_isIncr_global if_neg_1

theorem goal_3
    (nums : Array ℤ)
    (i : ℕ)
    (isDecr : Bool)
    (invariant_i_lower : OfNat.ofNat 1 ≤ i)
    (invariant_isDecr_global : isDecr = true ↔ ∀ (a b : ℕ), a < i → b < i → a ≤ b → nums[b]! ≤ nums[a]!)
    (if_neg_2 : nums[i]! ≤ nums[i - OfNat.ofNat 1]!)
    : isDecr = true ↔ ∀ (a b : ℕ), a < i + OfNat.ofNat 1 → b < i + OfNat.ofNat 1 → a ≤ b → nums[b]! ≤ nums[a]! := by
    intros; expose_names; exact
        goal_0 nums i isDecr invariant_i_lower invariant_isDecr_global if_neg_2

theorem goal_4
    (nums : Array ℤ)
    (i_1 : ℕ)
    (i_2 : Bool)
    (isIncr_1 : Bool)
    (invariant_i_upper : i_1 ≤ nums.size)
    (invariant_isIncr_adj : isIncr_1 = true ↔ ∀ (k : ℕ), OfNat.ofNat 1 ≤ k → k < i_1 → nums[k - OfNat.ofNat 1]! ≤ nums[k]!)
    (invariant_isIncr_global : isIncr_1 = true ↔ ∀ (a b : ℕ), a < i_1 → b < i_1 → a ≤ b → nums[a]! ≤ nums[b]!)
    (invariant_size_gt_1 : OfNat.ofNat 1 < nums.size)
    (done_1 : nums.size ≤ i_1)
    (invariant_isDecr_adj : i_2 = true ↔ ∀ (k : ℕ), OfNat.ofNat 1 ≤ k → k < i_1 → nums[k]! ≤ nums[k - OfNat.ofNat 1]!)
    (invariant_isDecr_global : i_2 = true ↔ ∀ (a b : ℕ), a < i_1 → b < i_1 → a ≤ b → nums[b]! ≤ nums[a]!)
    : postcondition nums (isIncr_1 || i_2) := by
    intros; expose_names; try simp_all; try grind


prove_correct MonotonicArray by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at *); try (conv => congr <;> simp) ; try expose_names)
  exact (goal_0 nums i isDecr invariant_i_lower invariant_isDecr_global if_neg_1)
  exact (goal_1 nums i isIncr invariant_i_lower invariant_isIncr_global if_neg_1)
  exact (goal_2 nums i isIncr invariant_i_lower invariant_isIncr_global if_neg_1)
  exact (goal_3 nums i isDecr invariant_i_lower invariant_isDecr_global if_neg_2)
  exact (goal_4 nums i_1 i_2 isIncr_1 invariant_i_upper invariant_isIncr_adj invariant_isIncr_global invariant_size_gt_1 done_1 invariant_isDecr_adj invariant_isDecr_global)
end Proof
