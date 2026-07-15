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
    TwoSumIISorted: Given a 1-indexed sorted array of integers, return the (1-indexed) positions of
    the unique pair of distinct elements whose sum equals a target.
    Natural language breakdown:
    1. Input is an array `numbers : Array Int` sorted in non-decreasing order.
    2. We are given an integer `target : Int`.
    3. There exist indices i and j with 0 ≤ i < j < numbers.size such that numbers[i] + numbers[j] = target.
    4. The problem guarantees this pair is unique (exactly one solution).
    5. Output is an array of length 2 containing the 1-based indices: [i+1, j+1].
    6. The two indices must be strictly increasing and within 1..numbers.size.
    7. We must not use the same element twice (captured by i < j).
    Your algorithm should run in **O(n)** time and **O(1)** extra space.
-/

section Specs
-- Helper: non-decreasing order on an Int array.
-- We use the standard relational characterization of sortedness by indices.
def isSortedNondecreasing (numbers : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < numbers.size → numbers[i]! ≤ numbers[j]!

-- Helper: a valid 0-based pair (i,j) witnessing the target sum.
def isWitnessPair (numbers : Array Int) (target : Int) (i : Nat) (j : Nat) : Prop :=
  i < j ∧ j < numbers.size ∧ numbers[i]! + numbers[j]! = target

-- Helper: uniqueness of the witness pair, expressed over 0-based indices.
def hasUniqueWitnessPair (numbers : Array Int) (target : Int) : Prop :=
  (∃ (i : Nat) (j : Nat), isWitnessPair numbers target i j) ∧
  (∀ (i₁ : Nat) (j₁ : Nat) (i₂ : Nat) (j₂ : Nat),
    isWitnessPair numbers target i₁ j₁ → isWitnessPair numbers target i₂ j₂ → i₁ = i₂ ∧ j₁ = j₂)

-- Helper: output shape/validity and correspondence to a witness pair.
def outputMatchesUniquePair (numbers : Array Int) (target : Int) (result : Array Nat) : Prop :=
  result.size = 2 ∧
  (1 ≤ result[0]!) ∧ (result[0]! < result[1]!) ∧ (result[1]! ≤ numbers.size) ∧
  (numbers[(result[0]! - 1)]! + numbers[(result[1]! - 1)]! = target) ∧
  (∀ (i : Nat) (j : Nat), isWitnessPair numbers target i j →
    result[0]! = i + 1 ∧ result[1]! = j + 1)

-- Preconditions
-- We keep them simple and decidable-ish (arith + array bounds), and capture the problem guarantees.
def precondition (numbers : Array Int) (target : Int) : Prop :=
  numbers.size ≥ 2 ∧
  isSortedNondecreasing numbers ∧
  hasUniqueWitnessPair numbers target

-- Postconditions
-- Ensure the result is exactly the 1-based indices of the unique witness pair.
def postcondition (numbers : Array Int) (target : Int) (result : Array Nat) : Prop :=
  outputMatchesUniquePair numbers target result
end Specs

section Impl
method TwoSumIISorted (numbers : Array Int) (target : Int)
  return (result : Array Nat)
  require precondition numbers target
  ensures postcondition numbers target result
  do
  let mut l : Nat := 0
  let mut r : Nat := numbers.size - 1
  let mut found : Bool := false
  let mut ansL : Nat := 0
  let mut ansR : Nat := 1

  while (l < r ∧ found = false)
    -- Keep precondition facts available
    invariant "ts_size_ge2" (numbers.size ≥ 2)
    invariant "ts_sorted" (isSortedNondecreasing numbers)
    -- Derived monotonicity: sortedness also implies i ≤ j → numbers[i] ≤ numbers[j]
    -- Initialization: follows from ts_sorted by cases i=j / i<j.
    -- Preservation: numbers is immutable.
    invariant "ts_sorted_le" (∀ (i : Nat) (j : Nat), i ≤ j → j < numbers.size → numbers[i]! ≤ numbers[j]!)
    invariant "ts_unique" (hasUniqueWitnessPair numbers target)

    -- Pointer bounds
    -- Initialization: l=0, r=size-1, and size≥2.
    -- Preservation: only l++ or r-- while l<r.
    invariant "ts_l_le_r" (l ≤ r)
    invariant "ts_r_lt_size" (r < numbers.size)
    invariant "ts_l_lt_size" (l < numbers.size)

    -- If we have found an answer, it is a valid (0-based) witness pair
    invariant "ts_found_is_witness" (found = true → isWitnessPair numbers target ansL ansR)

    -- If not found yet, the (unique) witness remains in the current window [l, r]
    -- Preservation relies on monotonicity (ts_sorted_le) and sum comparisons to rule out the eliminated index.
    invariant "ts_witness_in_window" (
      found = false →
        ∃ wL wR, isWitnessPair numbers target wL wR ∧ l ≤ wL ∧ wR ≤ r)

    -- Termination: either we set found=true (measure drops to 0), or we shrink the window (r-l decreases).
    decreasing (if found then 0 else r - l)
  do
    let sum : Int := numbers[l]! + numbers[r]!
    if sum = target then
      ansL := l
      ansR := r
      found := true
    else
      if sum < target then
        l := l + 1
      else
        r := r - 1

  -- Convert 0-based indices to 1-based as required
  return #[ansL + 1, ansR + 1]
end Impl

section TestCases
-- Test case 1: Example 1
-- numbers = [2,7,11,15], target = 9 => [1,2]
def test1_numbers : Array Int := #[2, 7, 11, 15]
def test1_target : Int := 9
def test1_Expected : Array Nat := #[1, 2]

-- Test case 2: Example 2
-- numbers = [2,3,4], target = 6 => [1,3]
def test2_numbers : Array Int := #[2, 3, 4]
def test2_target : Int := 6
def test2_Expected : Array Nat := #[1, 3]

-- Test case 3: Example 3 (includes negative)
-- numbers = [-1,0], target = -1 => [1,2]
def test3_numbers : Array Int := #[-1, 0]
def test3_target : Int := -1
def test3_Expected : Array Nat := #[1, 2]

-- Test case 4: Contains duplicates, unique solution uses equal values
-- numbers = [1,1,3,4], target = 2 => [1,2]
def test4_numbers : Array Int := #[1, 1, 3, 4]
def test4_target : Int := 2
def test4_Expected : Array Nat := #[1, 2]

-- Test case 5: Duplicates but solution uses farthest pair
-- numbers = [0,0,3,4], target = 4 => [1,4]
def test5_numbers : Array Int := #[0, 0, 3, 4]
def test5_target : Int := 4
def test5_Expected : Array Nat := #[1, 4]

-- Test case 6: All negative, minimal size 2
-- numbers = [-5,-2], target = -7 => [1,2]
def test6_numbers : Array Int := #[-5, -2]
def test6_target : Int := -7
def test6_Expected : Array Nat := #[1, 2]

-- Test case 7: Larger array, solution in the middle
-- numbers = [-10,-3,0,5,9,12], target = 6 => [-3 + 9]
-- indices 2 and 5 (1-based)
def test7_numbers : Array Int := #[-10, -3, 0, 5, 9, 12]
def test7_target : Int := 6
def test7_Expected : Array Nat := #[2, 5]

-- Test case 8: Boundary-ish: uses first and last elements
-- numbers = [1,2,3,4,10], target = 11 => [1,5]
def test8_numbers : Array Int := #[1, 2, 3, 4, 10]
def test8_target : Int := 11
def test8_Expected : Array Nat := #[1, 5]

-- Test case 9: Includes many equal elements, unique solution still exists
-- numbers = [2,2,2,2,9], target = 11 => [1,5]
def test9_numbers : Array Int := #[2, 2, 2, 2, 9]
def test9_target : Int := 11
def test9_Expected : Array Nat := #[1, 5]
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((TwoSumIISorted test1_numbers test1_target).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((TwoSumIISorted test2_numbers test2_target).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((TwoSumIISorted test3_numbers test3_target).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((TwoSumIISorted test4_numbers test4_target).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((TwoSumIISorted test5_numbers test5_target).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((TwoSumIISorted test6_numbers test6_target).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((TwoSumIISorted test7_numbers test7_target).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((TwoSumIISorted test8_numbers test8_target).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((TwoSumIISorted test9_numbers test9_target).run), DivM.res test9_Expected ]
end Assertions

section Pbt
-- Decidable instance synthesis failed for this method's conditions. Giving up on PBT.

-- velvet_plausible_test TwoSumIISorted (config := { maxMs := some 5000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000

theorem goal_0
    (numbers : Array ℤ)
    (target : ℤ)
    (require_1 : precondition numbers target)
    (ansL : ℕ)
    (ansR : ℕ)
    (l : ℕ)
    (r : ℕ)
    (invariant_ts_size_ge2 : numbers.size ≥ OfNat.ofNat 2)
    (invariant_ts_sorted : isSortedNondecreasing numbers)
    (invariant_ts_sorted_le : ∀ (i j : ℕ), i ≤ j → j < numbers.size → numbers[i]! ≤ numbers[j]!)
    (invariant_ts_unique : hasUniqueWitnessPair numbers target)
    (invariant_ts_l_le_r : l ≤ r)
    (invariant_ts_r_lt_size : r < numbers.size)
    (invariant_ts_l_lt_size : l < numbers.size)
    (a : l < r)
    (if_neg : ¬numbers[l]! + numbers[r]! = target)
    (if_pos : numbers[l]! + numbers[r]! < target)
    (invariant_ts_found_is_witness : false = true → isWitnessPair numbers target ansL ansR)
    (invariant_ts_witness_in_window : false = false → ∃ wL wR, isWitnessPair numbers target wL wR ∧ l ≤ wL ∧ wR ≤ r)
    : r - (l + OfNat.ofNat 1) < r - l := by
    intros; expose_names; try ( simp at * ); try grind

theorem goal_1
    (numbers : Array ℤ)
    (target : ℤ)
    (l : ℕ)
    (r : ℕ)
    (invariant_ts_sorted_le : ∀ (i j : ℕ), i ≤ j → j < numbers.size → numbers[i]! ≤ numbers[j]!)
    (if_neg : ¬numbers[l]! + numbers[r]! = target)
    (if_neg_1 : ¬numbers[l]! + numbers[r]! < target)
    (invariant_ts_witness_in_window : false = false → ∃ wL wR, isWitnessPair numbers target wL wR ∧ l ≤ wL ∧ wR ≤ r)
    : True → ∃ wL wR, (wL < wR ∧ wR < numbers.size ∧ numbers[wL]! + numbers[wR]! = target) ∧ l ≤ wL ∧ wR ≤ r - OfNat.ofNat 1 := by
  intro _
  rcases invariant_ts_witness_in_window rfl with ⟨wL, wR, hw, hlw, hwr⟩
  rcases hw with ⟨hwLt, hwSize, hwSum⟩
  refine ⟨wL, wR, ?_, hlw, ?_⟩
  · exact ⟨hwLt, hwSize, hwSum⟩
  · -- show wR ≤ r - 1
    have hle : target ≤ numbers[l]! + numbers[r]! := by
      -- `if_neg_1` is `¬ (numbers[l]! + numbers[r]! < target)`
      exact le_of_not_gt (by simpa using if_neg_1)
    have hne : target ≠ numbers[l]! + numbers[r]! := by
      intro h
      exact if_neg h.symm
    have htarget_lt : target < numbers[l]! + numbers[r]! := hne.lt_of_le hle

    have hne_r : wR ≠ r := by
      intro hEq
      have hwlSize : wL < numbers.size := lt_trans hwLt hwSize
      have hmono : numbers[l]! ≤ numbers[wL]! := invariant_ts_sorted_le l wL hlw hwlSize
      have hsum_le : numbers[l]! + numbers[r]! ≤ numbers[wL]! + numbers[r]! :=
        add_le_add_right hmono (numbers[r]!)
      have hwSum' : numbers[wL]! + numbers[r]! = target := by
        simpa [hEq] using hwSum
      have hsum_le_target : numbers[l]! + numbers[r]! ≤ target := by
        calc
          numbers[l]! + numbers[r]! ≤ numbers[wL]! + numbers[r]! := hsum_le
          _ = target := hwSum'
      have : ¬ target < numbers[l]! + numbers[r]! := not_lt_of_ge hsum_le_target
      exact this htarget_lt

    have hltR : wR < r := hne_r.lt_of_le hwr
    simpa using hltR.le_pred

theorem goal_2
    (l : ℕ)
    (r : ℕ)
    (a : l < r)
    : r - OfNat.ofNat 1 - l < r - l := by
    -- purely arithmetic: shrinking `r` by 1 shrinks the window size `r - l`
    change r - 1 - l < r - l

    have hl : l ≤ Nat.pred r := a.le_pred

    have hrpos : 0 < r := lt_of_le_of_lt (Nat.zero_le l) a
    have hr0 : r ≠ 0 := Nat.ne_of_gt hrpos

    have hpred : Nat.pred r - l < r - l :=
      (Nat.sub_lt_sub_iff_right hl).2 (Nat.pred_lt hr0)

    -- turn the goal into the `Nat.pred` form
    rw [Nat.sub_one]
    exact hpred

theorem goal_3
    (numbers : Array ℤ)
    (target : ℤ)
    (invariant_ts_unique : hasUniqueWitnessPair numbers target)
    (i : ℕ)
    (i_1 : ℕ)
    (i_2 : Bool)
    (i_3 : ℕ)
    (r_1 : ℕ)
    (invariant_ts_found_is_witness : i_2 = true → isWitnessPair numbers target i i_1)
    (invariant_ts_l_le_r : i_3 ≤ r_1)
    (invariant_ts_witness_in_window : i_2 = false → ∃ wL wR, isWitnessPair numbers target wL wR ∧ i_3 ≤ wL ∧ wR ≤ r_1)
    (done_1 : ¬(i_3 < r_1 ∧ i_2 = false))
    : postcondition numbers target #[i + OfNat.ofNat 1, i_1 + OfNat.ofNat 1] := by
  -- Prove found = true from the loop exit condition.
  have hfound : i_2 = true := by
    cases h2 : i_2 with
    | false =>
        -- In this branch, the goal is `false = true`, i.e. `False`.
        have hnot : ¬ i_3 < r_1 := by
          -- done_1 specializes to ¬(i_3 < r_1)
          simpa [h2] using done_1
        have hle : r_1 ≤ i_3 := Nat.not_lt.mp hnot
        have heq : i_3 = r_1 := Nat.le_antisymm invariant_ts_l_le_r hle
        -- But the witness-in-window invariant cannot hold if l=r.
        rcases (invariant_ts_witness_in_window (by simpa [h2])) with ⟨wL, wR, hw, hl, hr⟩
        have hlt : wL < wR := hw.1
        have hwrle : wR ≤ i_3 := by simpa [heq] using hr
        have hwllt : wL < i_3 := Nat.lt_of_lt_of_le hlt hwrle
        have : ¬ wL < i_3 := Nat.not_lt_of_ge hl
        exact (this hwllt).elim
    | true =>
        simpa [h2]

  have hwitness : isWitnessPair numbers target i i_1 := invariant_ts_found_is_witness hfound
  rcases invariant_ts_unique with ⟨hex, huniq⟩

  -- Unfold the postcondition
  dsimp [postcondition, outputMatchesUniquePair]
  -- show all conjuncts
  refine And.intro (by simp) ?_
  refine And.intro (by simp) ?_
  refine And.intro ?_ ?_
  · -- result[0]! < result[1]!
    have hi_lt : i < i_1 := hwitness.1
    simpa using Nat.add_lt_add_right hi_lt 1
  refine And.intro ?_ ?_
  · -- result[1]! ≤ numbers.size
    exact Nat.succ_le_of_lt hwitness.2.1
  refine And.intro ?_ ?_
  · -- sum at those indices
    -- simp reduces (i+1)-1 = i and array indexing on literal arrays
    simpa using hwitness.2.2
  · intro i' j' hW
    have hEq : i' = i ∧ j' = i_1 := huniq i' j' i i_1 hW hwitness
    constructor <;> simp [hEq.1, hEq.2]

set_option loom.solver "custom"

macro_rules
| `(tactic|loom_solver) => `(tactic|(
  try injections
  try subst_vars
  try grind (gen := 4)))


prove_correct TwoSumIISorted by
  loom_solve <;> (try injections; try subst_vars; try (conv => congr <;> simp) ; try expose_names)
  exact (goal_0 numbers target require_1 ansL ansR l r invariant_ts_size_ge2 invariant_ts_sorted invariant_ts_sorted_le invariant_ts_unique invariant_ts_l_le_r invariant_ts_r_lt_size invariant_ts_l_lt_size a if_neg if_pos invariant_ts_found_is_witness invariant_ts_witness_in_window)
  exact (goal_1 numbers target l r invariant_ts_sorted_le if_neg if_neg_1 invariant_ts_witness_in_window)
  exact (goal_2 l r a)
  exact (goal_3 numbers target invariant_ts_unique i i_1 i_2 i_3 r_1 invariant_ts_found_is_witness invariant_ts_l_le_r invariant_ts_witness_in_window done_1)
end Proof
