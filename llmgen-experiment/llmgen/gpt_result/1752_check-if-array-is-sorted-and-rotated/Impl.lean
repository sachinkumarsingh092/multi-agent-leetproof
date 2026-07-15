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
    1752. Check if Array Is Sorted and Rotated: decide whether an array can be obtained by rotating a non-decreasingly sorted array.
    **Important: complexity should be O(n) time and O(1) space**
    Natural language breakdown:
    1. We are given an array `nums` of integers; duplicates are allowed.
    2. A non-decreasingly sorted array has no adjacent decrease: for each valid i, A[i] ≤ A[i+1].
    3. Rotating an array by x positions shifts elements cyclically; rotation by 0 leaves the array unchanged.
    4. The input `nums` is valid iff there exists some rotation of `nums` that is non-decreasing.
    5. Equivalent circular characterization: scanning the array cyclically, there is at most one index i where nums[i] > nums[(i+1) mod n].
    6. Arrays of length 0 or 1 are always considered sorted-and-rotated.
-/

section Specs
-- A “drop” is a strict decrease from an element to its cyclic successor.
-- We define it as a Prop so it can be used in specifications.

def isDrop (nums : Array Int) (i : Nat) : Prop :=
  nums.size > 0 ∧ i < nums.size ∧ nums[(i + 1) % nums.size]! < nums[i]!

-- `rotSortedProp nums` holds exactly when `nums` is sorted-and-rotated in the sense of the problem.
-- Using the standard circular-drop characterization: at most one drop.

def rotSortedProp (nums : Array Int) : Prop :=
  nums.size ≤ 1 ∨ (∀ (i : Nat) (j : Nat), isDrop nums i → isDrop nums j → i = j)

-- No input constraints.

def precondition (nums : Array Int) : Prop :=
  True

def postcondition (nums : Array Int) (result : Bool) : Prop :=
  (result = true ↔ rotSortedProp nums) ∧
  (result = false ↔ ¬ rotSortedProp nums)
end Specs

section Impl
method CheckSortedAndRotated (nums : Array Int)
  return (result : Bool)
  require precondition nums
  ensures postcondition nums result
  do
  let n := nums.size
  if n ≤ 1 then
    return true
  else
    let mut drops : Nat := 0
    let mut i : Nat := 0
    while i < n
      -- i stays within [0,n], ensuring array accesses are in-bounds.
      invariant "inv_bounds" i ≤ n
      -- n is the array size (and fixed throughout the loop).
      invariant "inv_n_def" n = nums.size
      -- In this branch we have n > 1, hence n > 0 (needed for modulo indexing).
      invariant "inv_n_pos" n > 0
      -- drops equals the number of strict decreases among indices already processed: k ∈ [0,i).
      invariant "inv_drops_count" drops = (Finset.filter (fun k : Nat => nums[(k + 1) % n]! < nums[k]!) (Finset.range i)).card
      decreasing n - i
    do
      let a := nums[i]!
      let b := nums[(i + 1) % n]!
      if b < a then
        drops := drops + 1
      i := i + 1
    if drops ≤ 1 then
      return true
    else
      return false
end Impl

section TestCases
-- Test case 1: Example 1
-- nums = [3,4,5,1,2] -> true

def test1_nums : Array Int := #[3, 4, 5, 1, 2]

def test1_Expected : Bool := true

-- Test case 2: Example 2
-- nums = [2,1,3,4] -> false

def test2_nums : Array Int := #[2, 1, 3, 4]

def test2_Expected : Bool := false

-- Test case 3: Example 3
-- nums = [1,2,3] -> true

def test3_nums : Array Int := #[1, 2, 3]

def test3_Expected : Bool := true

-- Test case 4: Empty array (degenerate)

def test4_nums : Array Int := #[]

def test4_Expected : Bool := true

-- Test case 5: Singleton array (degenerate)

def test5_nums : Array Int := #[42]

def test5_Expected : Bool := true

-- Test case 6: All equal elements (duplicates; any rotation is the same)

def test6_nums : Array Int := #[7, 7, 7, 7]

def test6_Expected : Bool := true

-- Test case 7: Sorted but not rotated (0 rotation)

def test7_nums : Array Int := #[0, 0, 1, 2, 2, 5]

def test7_Expected : Bool := true

-- Test case 8: Rotated with duplicates, still valid
-- Original sorted: [1,1,2,3,3], rotate by 3 -> [3,3,1,1,2]

def test8_nums : Array Int := #[3, 3, 1, 1, 2]

def test8_Expected : Bool := true

-- Test case 9: Two drops in the cyclic scan -> invalid
-- Drops at 0: 3>1 and at 2: 2>0

def test9_nums : Array Int := #[3, 1, 2, 0]

def test9_Expected : Bool := false
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((CheckSortedAndRotated test1_nums).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((CheckSortedAndRotated test2_nums).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((CheckSortedAndRotated test3_nums).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((CheckSortedAndRotated test4_nums).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((CheckSortedAndRotated test5_nums).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((CheckSortedAndRotated test6_nums).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((CheckSortedAndRotated test7_nums).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((CheckSortedAndRotated test8_nums).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((CheckSortedAndRotated test9_nums).run), DivM.res test9_Expected ]
end Assertions

section Pbt
velvet_plausible_test CheckSortedAndRotated (config := { maxMs := some 20000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000

theorem goal_0
    (nums : Array ℤ)
    (i : ℕ)
    (if_pos_1 : nums[(i + OfNat.ofNat 1) % nums.size]! < nums[i]!)
    : {k ∈ Finset.range i | nums[(k + OfNat.ofNat 1) % nums.size]! < nums[k]!}.card + OfNat.ofNat 1 = {k ∈ Finset.range (i + OfNat.ofNat 1) | nums[(k + OfNat.ofNat 1) % nums.size]! < nums[k]!}.card := by
    classical
    -- Predicate for a strict decrease from an index to its cyclic successor.
    let P : Nat → Prop := fun k => nums[(k + (1 : Nat)) % nums.size]! < nums[k]!

    have hPi : P i := by
      simpa [P] using if_pos_1

    have hi_not : i ∉ {k ∈ Finset.range i | P k} := by
      -- Membership in `range i` forces `i < i`, impossible.
      simp [P, Finset.mem_range]

    -- Going from `range i` to `range (i+1)` adds exactly `i`.
    -- Since `P i` holds and `i` was not previously in the filtered range, the card increases by 1.
    simp [P, Finset.range_add_one, Finset.filter_insert, hPi, hi_not, Finset.card_insert_of_not_mem]

theorem goal_1
    (nums : Array ℤ)
    (i : ℕ)
    (if_neg_1 : nums[i]! ≤ nums[(i + OfNat.ofNat 1) % nums.size]!)
    : {k ∈ Finset.range i | nums[(k + OfNat.ofNat 1) % nums.size]! < nums[k]!}.card = {k ∈ Finset.range (i + OfNat.ofNat 1) | nums[(k + OfNat.ofNat 1) % nums.size]! < nums[k]!}.card := by
    classical
    let P : ℕ → Prop := fun k => nums[(k + 1) % nums.size]! < nums[k]!
    have hPi : ¬ P i := by
      dsimp [P]
      exact not_lt_of_ge if_neg_1

    -- Rewrite the set-builder notation as a filter.
    change (Finset.filter P (Finset.range i)).card =
        (Finset.filter P (Finset.range (i + 1))).card

    have hrange : Finset.range (i + 1) = insert i (Finset.range i) := by
      -- `Finset.range_succ` is stated with `Nat.succ`, and `i + 1` reduces to `Nat.succ i`.
      simpa using (Finset.range_succ (n := i))

    rw [hrange]
    -- Since `P i` is false, filtering the inserted element does not change the result.
    simp [Finset.filter_insert, hPi]

theorem goal_2
    (nums : Array ℤ)
    (i_2 : ℕ)
    (invariant_inv_bounds : i_2 ≤ nums.size)
    (if_pos : {k ∈ Finset.range i_2 | nums[(k + OfNat.ofNat 1) % nums.size]! < nums[k]!}.card ≤ OfNat.ofNat 1)
    (done_1 : nums.size ≤ i_2)
    : postcondition nums true := by
  classical

  have hsize : i_2 = nums.size := le_antisymm invariant_inv_bounds done_1
  have hcard :
      ({k ∈ Finset.range nums.size | nums[(k + 1) % nums.size]! < nums[k]!}.card ≤ (1 : Nat)) := by
    simpa [hsize] using if_pos

  have hrot : rotSortedProp nums := by
    right
    intro i j hi hj
    rcases hi with ⟨_, hi_lt, hi_drop⟩
    rcases hj with ⟨_, hj_lt, hj_drop⟩

    have huniq :
        ∀ {a b : Nat},
          a ∈ {k ∈ Finset.range nums.size | nums[(k + 1) % nums.size]! < nums[k]!} →
          b ∈ {k ∈ Finset.range nums.size | nums[(k + 1) % nums.size]! < nums[k]!} →
          a = b :=
      (Finset.card_le_one_iff).1 hcard

    have hi_drop' : nums[(i + 1) % nums.size]! < nums[i]'hi_lt := by
      simpa [getElem!_pos (c := nums) (i := i) hi_lt] using hi_drop
    have hj_drop' : nums[(j + 1) % nums.size]! < nums[j]'hj_lt := by
      simpa [getElem!_pos (c := nums) (i := j) hj_lt] using hj_drop

    have hi_mem : i ∈ {k ∈ Finset.range nums.size | nums[(k + 1) % nums.size]! < nums[k]!} := by
      -- `simp` turns membership in the filtered range into the conjunction of the two facts.
      simp [hi_lt, hi_drop']
    have hj_mem : j ∈ {k ∈ Finset.range nums.size | nums[(k + 1) % nums.size]! < nums[k]!} := by
      simp [hj_lt, hj_drop']

    exact huniq hi_mem hj_mem

  unfold postcondition
  refine And.intro ?_ ?_
  · constructor
    · intro _
      exact hrot
    · intro _
      trivial
  · constructor
    · intro h
      cases h
    · intro hnot
      exact False.elim (hnot hrot)

theorem goal_3
    (nums : Array ℤ)
    (i_2 : ℕ)
    (invariant_inv_bounds : i_2 ≤ nums.size)
    (if_neg : OfNat.ofNat 1 < nums.size)
    (invariant_inv_n_pos : OfNat.ofNat 0 < nums.size)
    (done_1 : nums.size ≤ i_2)
    (if_neg_1 : OfNat.ofNat 1 < {k ∈ Finset.range i_2 | nums[(k + OfNat.ofNat 1) % nums.size]! < nums[k]!}.card)
    : postcondition nums false := by
  classical

  have hi : i_2 = nums.size := Nat.le_antisymm invariant_inv_bounds done_1

  have hcard : (1 : Nat) < {k ∈ Finset.range nums.size | nums[(k + 1) % nums.size]! < nums[k]!}.card := by
    simpa [hi] using if_neg_1

  rcases (Finset.one_lt_card).1 hcard with ⟨a, ha, b, hb, hab⟩

  have ha' : a < nums.size ∧ nums[(a + 1) % nums.size]! < nums[a]! := by
    simpa [Finset.mem_range, and_assoc, and_left_comm, and_comm] using ha

  have hb' : b < nums.size ∧ nums[(b + 1) % nums.size]! < nums[b]! := by
    simpa [Finset.mem_range, and_assoc, and_left_comm, and_comm] using hb

  have hdrop_a : isDrop nums a := by
    refine ⟨invariant_inv_n_pos, ha'.1, ha'.2⟩

  have hdrop_b : isDrop nums b := by
    refine ⟨invariant_inv_n_pos, hb'.1, hb'.2⟩

  have hnot : ¬ rotSortedProp nums := by
    intro hrot
    rcases hrot with hle1 | hunique
    · exact (Nat.not_le_of_gt if_neg) hle1
    · have hEq : a = b := hunique a b hdrop_a hdrop_b
      exact hab hEq

  unfold postcondition
  constructor
  · constructor
    · intro h
      cases h
    · intro hrot
      exfalso
      exact hnot hrot
  · constructor
    · intro _
      exact hnot
    · intro _
      rfl


prove_correct CheckSortedAndRotated by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at *); try (conv => congr <;> simp) ; try expose_names)
  exact (goal_0 nums i if_pos_1)
  exact (goal_1 nums i if_neg_1)
  exact (goal_2 nums i_2 invariant_inv_bounds if_pos done_1)
  exact (goal_3 nums i_2 invariant_inv_bounds if_neg invariant_inv_n_pos done_1 if_neg_1)
end Proof
