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
    MaximumSubarray: return the maximum possible sum of a non-empty contiguous subarray.
    **Important: complexity should be O(n) time and O(1) space**
    Natural language breakdown:
    1. Input is an array of integers `nums`.
    2. A contiguous subarray is determined by indices `start` and `stop` with `start < stop`.
    3. The sum of a subarray is the sum of the elements in `nums[start:stop]`.
    4. The result is the sum of some non-empty contiguous subarray (achievability).
    5. The result is greater than or equal to the sum of every non-empty contiguous subarray (maximality).
    6. The input must be non-empty so that at least one non-empty subarray exists.
-/

section Specs
-- Sum of all elements in an array.
def arraySum (arr : Array Int) : Int :=
  arr.foldl (fun acc x => acc + x) 0

-- Sum of the contiguous segment nums[start:stop].
-- This uses Array.extract; the spec restricts start/stop so no clamping occurs.
def rangeSum (nums : Array Int) (start : Nat) (stop : Nat) : Int :=
  arraySum (nums.extract start stop)

-- Input must be non-empty.
def precondition (nums : Array Int) : Prop :=
  nums.size > 0

-- result is the maximum sum among all non-empty contiguous subarrays.
def postcondition (nums : Array Int) (result : Int) : Prop :=
  (∃ (start : Nat) (stop : Nat),
      start < stop ∧ stop ≤ nums.size ∧ rangeSum nums start stop = result) ∧
  (∀ (start : Nat) (stop : Nat),
      start < stop ∧ stop ≤ nums.size → rangeSum nums start stop ≤ result)
end Specs

section Impl
method MaximumSubarray (nums : Array Int)
  return (result : Int)
  require precondition nums
  ensures postcondition nums result
  do
  -- Kadane's algorithm: O(n) time, O(1) extra space.
  let mut i : Nat := 1
  let mut bestEndingHere : Int := nums[0]!
  let mut bestSoFar : Int := nums[0]!

  while i < nums.size
    -- i tracks the next index to process; we have already processed [0, i).
    -- Initialization: i = 1 and precondition gives nums.size > 0, so 1 ≤ i ≤ nums.size.
    -- Preservation: loop increments i by 1 and guard enforces i < nums.size.
    invariant "inv_bounds" (1 ≤ i ∧ i ≤ nums.size)

    -- bestEndingHere is the maximum rangeSum over all non-empty subarrays ending at stop = i.
    -- Initialization: at i = 1, the only such subarray is [0,1).
    -- Preservation: Kadane update picks max of starting fresh at i (x) vs extending previous best ending at i.
    invariant "inv_ending_ex" (∃ start : Nat, start < i ∧ rangeSum nums start i = bestEndingHere)
    invariant "inv_ending_max" (∀ start : Nat, start < i → rangeSum nums start i ≤ bestEndingHere)

    -- bestSoFar is the maximum rangeSum over all non-empty subarrays fully contained in the processed prefix [0,i).
    -- Initialization: at i = 1, the only subarray contained in the prefix is [0,1).
    -- Preservation: bestSoFar is updated when bestEndingHere improves it.
    invariant "inv_sofar_ex" (∃ start stop : Nat, start < stop ∧ stop ≤ i ∧ rangeSum nums start stop = bestSoFar)
    invariant "inv_sofar_max" (∀ start stop : Nat, start < stop ∧ stop ≤ i → rangeSum nums start stop ≤ bestSoFar)

    -- Termination: each iteration increases i, so nums.size - i decreases.
    decreasing nums.size - i
  do
    let x : Int := nums[i]!
    let extend : Int := bestEndingHere + x
    if x >= extend then
      bestEndingHere := x
    else
      bestEndingHere := extend

    if bestEndingHere > bestSoFar then
      bestSoFar := bestEndingHere

    i := i + 1

  return bestSoFar
end Impl

section TestCases
-- Test case 1: Example 1
-- nums = [-2,1,-3,4,-1,2,1,-5,4] => 6 (subarray [4,-1,2,1])
def test1_nums : Array Int := #[-2, 1, -3, 4, -1, 2, 1, -5, 4]
def test1_Expected : Int := 6

-- Test case 2: Example 2 (single element)
def test2_nums : Array Int := #[1]
def test2_Expected : Int := 1

-- Test case 3: Example 3 (whole array is best)
def test3_nums : Array Int := #[5, 4, -1, 7, 8]
def test3_Expected : Int := 23

-- Test case 4: All negative (best is the least negative single element)
def test4_nums : Array Int := #[-8, -3, -6, -2, -5, -4]
def test4_Expected : Int := -2

-- Test case 5: Contains zeros; best is 0 (choose [0])
def test5_nums : Array Int := #[0, -1, 0, -2]
def test5_Expected : Int := 0

-- Test case 6: Mixed, best is a suffix/prefix segment
-- Best subarray is [3, -1, 2] with sum 4

def test6_nums : Array Int := #[-2, 3, -1, 2, -1]
def test6_Expected : Int := 4

-- Test case 7: Alternating small values
-- Best subarray is [1, -1, 1, -1, 1] has max 1 (any single 1)
def test7_nums : Array Int := #[1, -1, 1, -1, 1]
def test7_Expected : Int := 1

-- Test case 8: Best is the entire array

def test8_nums : Array Int := #[2, 3, 1]
def test8_Expected : Int := 6

-- Test case 9: Two elements, decreasing
-- Best is [10] not [10,-20]
def test9_nums : Array Int := #[10, -20]
def test9_Expected : Int := 10
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((MaximumSubarray test1_nums).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((MaximumSubarray test2_nums).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((MaximumSubarray test3_nums).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((MaximumSubarray test4_nums).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((MaximumSubarray test5_nums).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((MaximumSubarray test6_nums).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((MaximumSubarray test7_nums).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((MaximumSubarray test8_nums).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((MaximumSubarray test9_nums).run), DivM.res test9_Expected ]
end Assertions

section Pbt
velvet_plausible_test MaximumSubarray (config := { maxMs := some 20000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000

theorem goal_0
    (nums : Array ℤ)
    (i : ℕ)
    (a : OfNat.ofNat 1 ≤ i)
    (if_pos : i < nums.size)
    : ∃ start < i + OfNat.ofNat 1, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start (i + OfNat.ofNat 1)) (OfNat.ofNat 0) (min (i + OfNat.ofNat 1) nums.size - start) = nums[i]! := by
  refine ⟨i, Nat.lt_succ_self i, ?_⟩
  have hi1 : i + 1 ≤ nums.size := Nat.succ_le_of_lt if_pos
  have hmin : min (i + 1) nums.size = i + 1 := Nat.min_eq_left hi1
  have hsub : i + 1 - i = 1 := by simpa using (Nat.add_sub_cancel i 1)

  have hsize : (nums.extract i (i+1)).size = 1 := by
    simp [Array.size_extract, hmin, hsub]

  have hextract : nums.extract i (i + 1) = (#[nums[i]!] : Array ℤ) := by
    -- ext with size and elements
    apply Array.ext
    · -- size
      simpa [hsize]
    · intro j hj
      -- since size is 1, j must be 0
      have hj1 : j < 1 := by simpa [hsize] using hj
      have hj0 : j = 0 := by
        have : j ≤ 0 := (Nat.lt_succ_iff).1 (by simpa using hj1)
        exact Nat.le_zero.mp this
      subst hj0
      have h0 : (0 : Nat) < (nums.extract i (i+1)).size := by
        simpa [hsize] using (Nat.zero_lt_one : (0:Nat) < 1)
      -- evaluate the extracted element
      have hget0 : (nums.extract i (i+1))[0] = nums[i + 0]'(Array.getElem_extract_aux (xs:=nums) (start:=i) (stop:=i+1) (i:=0) h0) := by
        simpa using (Array.getElem_extract (xs:=nums) (start:=i) (stop:=i+1) (i:=0) h0)
      -- simplify RHS and the singleton array
      simpa [hget0, if_pos, Nat.zero_add, Array.getElem_singleton]
  -- finish by rewriting to a singleton fold
  -- also simplify the min/sub expression to 1
  simp [hmin, hsub, hextract]

theorem goal_1
    (nums : Array ℤ)
    (bestEndingHere : ℤ)
    (i : ℕ)
    (a : OfNat.ofNat 1 ≤ i)
    (if_pos : i < nums.size)
    (invariant_inv_ending_max : ∀ start < i, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start i) (OfNat.ofNat 0) (min i nums.size - start) ≤ bestEndingHere)
    (if_pos_1 : bestEndingHere ≤ OfNat.ofNat 0)
    : ∀ start < i + OfNat.ofNat 1, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start (i + OfNat.ofNat 1)) (OfNat.ofNat 0) (min (i + OfNat.ofNat 1) nums.size - start) ≤ nums[i]! := by
  classical
  intro start hstart
  have hi1 : i + 1 ≤ nums.size := Nat.succ_le_of_lt if_pos

  -- Convert the goal's `foldl` with explicit stop into the full-array `foldl`.
  have hgoal_fold :
      Array.foldl (fun acc x : ℤ => acc + x) 0 (nums.extract start (i + 1)) 0 (min (i + 1) nums.size - start)
        = Array.foldl (fun acc x : ℤ => acc + x) 0 (nums.extract start (i + 1)) := by
    have hs : (nums.extract start (i + 1)).size = min (i + 1) nums.size - start := by
      simpa using (Array.size_extract (xs := nums) (start := start) (stop := i + 1))
    -- After rewriting the stop to `size`, the statement is definitional.
    simpa [hs]

  -- `extract i (i+1)` is the singleton array containing `nums[i]!`.
  have hbang : nums[i]! = nums[i] := by
    simp [Array.getElem!_eq_getD, Array.getD, if_pos]

  have hopt : nums[i]? = some nums[i]! := by
    have h1 : nums[i]? = some nums[i] := Array.getElem?_eq_getElem if_pos
    simpa [hbang] using h1

  have hextract_single : nums.extract i (i + 1) = #[nums[i]!] := by
    apply Array.ext_getElem?
    intro j
    cases j with
    | zero =>
        -- lhs is `nums[i]?`, rhs is `some nums[i]!`
        -- compute each side separately to avoid over-simplification
        have hlhs : (nums.extract i (i + 1))[0]? = nums[i]? := by
          simp [Array.getElem?_extract, Nat.min_eq_left hi1]
        have hrhs : (#[nums[i]!] : Array ℤ)[0]? = some nums[i]! := by
          simp
        -- combine
        simpa [hlhs, hrhs] using hopt
    | succ j =>
        have : ¬ Nat.succ j < 1 := by simp
        simp [Array.getElem?_extract, Nat.min_eq_left hi1, this]

  have hle : start ≤ i := (Nat.lt_succ_iff.mp hstart)
  rcases lt_or_eq_of_le hle with hlt | hEq

  · -- Case: start < i
    -- Convert the invariant's fold into full-array fold.
    have hinv_fold :
        Array.foldl (fun acc x : ℤ => acc + x) 0 (nums.extract start i) 0 (min i nums.size - start)
          = Array.foldl (fun acc x : ℤ => acc + x) 0 (nums.extract start i) := by
      have hs : (nums.extract start i).size = min i nums.size - start := by
        simpa using (Array.size_extract (xs := nums) (start := start) (stop := i))
      simpa [hs]

    have hsum_le_end :
        Array.foldl (fun acc x : ℤ => acc + x) 0 (nums.extract start i) ≤ bestEndingHere := by
      have := invariant_inv_ending_max start hlt
      simpa [hinv_fold] using this

    have hsum_le_zero :
        Array.foldl (fun acc x : ℤ => acc + x) 0 (nums.extract start i) ≤ 0 :=
      le_trans hsum_le_end if_pos_1

    -- split extract at i
    have hextract_split : nums.extract start (i + 1) = nums.extract start i ++ nums.extract i (i + 1) := by
      have h := (@Array.extract_append_extract ℤ nums start i (i + 1))
      have hmin : Nat.min start i = start := Nat.min_eq_left (Nat.le_of_lt hlt)
      have hmax : Nat.max i (i + 1) = i + 1 := Nat.max_eq_right (Nat.le_succ i)
      simpa [hmin, hmax] using h.symm

    have hdecomp :
        Array.foldl (fun acc x : ℤ => acc + x) 0 (nums.extract start (i + 1))
          = Array.foldl (fun acc x : ℤ => acc + x) 0 (nums.extract start i) + nums[i]! := by
      calc
        Array.foldl (fun acc x : ℤ => acc + x) 0 (nums.extract start (i + 1))
            = Array.foldl (fun acc x : ℤ => acc + x) 0 (nums.extract start i ++ nums.extract i (i + 1)) := by
                simpa [hextract_split]
        _ = Array.foldl (fun acc x : ℤ => acc + x)
              (Array.foldl (fun acc x : ℤ => acc + x) 0 (nums.extract start i)) (nums.extract i (i + 1)) := by
              -- `foldl_append` is for the method `.foldl`; rewrite it in `Array.foldl` form.
              simpa using (Array.foldl_append (xs := nums.extract start i) (ys := nums.extract i (i + 1))
                (f := fun acc x : ℤ => acc + x) (b := (0 : ℤ)))
        _ = Array.foldl (fun acc x : ℤ => acc + x)
              (Array.foldl (fun acc x : ℤ => acc + x) 0 (nums.extract start i)) (#[nums[i]!] : Array ℤ) := by
              simpa [hextract_single]
        _ = Array.foldl (fun acc x : ℤ => acc + x) 0 (nums.extract start i) + nums[i]! := by
              simp

    have hfinal_full :
        Array.foldl (fun acc x : ℤ => acc + x) 0 (nums.extract start (i + 1)) ≤ nums[i]! := by
      calc
        Array.foldl (fun acc x : ℤ => acc + x) 0 (nums.extract start (i + 1))
            = Array.foldl (fun acc x : ℤ => acc + x) 0 (nums.extract start i) + nums[i]! := hdecomp
        _ ≤ 0 + nums[i]! := by
              exact add_le_add_right hsum_le_zero _
        _ = nums[i]! := by simp

    -- return to the original goal form
    have :
        Array.foldl (fun acc x : ℤ => acc + x) 0 (nums.extract start (i + 1)) 0 (min (i + 1) nums.size - start)
          ≤ nums[i]! := by
      simpa [hgoal_fold] using hfinal_full
    simpa using this

  · -- Case: start = i
    cases hEq
    -- goal becomes a singleton sum
    have hfinal_full : Array.foldl (fun acc x : ℤ => acc + x) 0 (nums.extract i (i + 1)) ≤ nums[i]! := by
      -- compute the singleton fold
      simp [hextract_single]
    -- convert back to the original goal form
    simpa [hgoal_fold] using hfinal_full

theorem goal_2
    (nums : Array ℤ)
    (i : ℕ)
    (a : OfNat.ofNat 1 ≤ i)
    (if_pos : i < nums.size)
    : ∃ start stop, start < stop ∧ stop ≤ i + OfNat.ofNat 1 ∧ Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) = nums[i]! := by
    rcases goal_0 nums i a if_pos with ⟨start, hlt, hsum⟩
    refine ⟨start, i + OfNat.ofNat 1, ?_, ?_, ?_⟩
    · exact hlt
    · exact le_rfl
    · simpa using hsum

theorem goal_3
    (nums : Array ℤ)
    (bestEndingHere : ℤ)
    (bestSoFar : ℤ)
    (i : ℕ)
    (a : OfNat.ofNat 1 ≤ i)
    (if_pos : i < nums.size)
    (invariant_inv_ending_max : ∀ start < i, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start i) (OfNat.ofNat 0) (min i nums.size - start) ≤ bestEndingHere)
    (invariant_inv_sofar_max : ∀ (start stop : ℕ), start < stop → stop ≤ i → Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) ≤ bestSoFar)
    (if_pos_1 : bestEndingHere ≤ OfNat.ofNat 0)
    (if_pos_2 : bestSoFar < nums[i]!)
    : ∀ (start stop : ℕ), start < stop → stop ≤ i + OfNat.ofNat 1 → Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) ≤ nums[i]! := by
  intro start stop hstartstop hstop
  by_cases hstop' : stop ≤ i
  · have hs :
        Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop)
            (OfNat.ofNat 0) (min stop nums.size - start) ≤
          bestSoFar :=
        invariant_inv_sofar_max start stop hstartstop hstop'
    exact le_trans hs (le_of_lt if_pos_2)
  · have hi_lt_stop : i < stop := Nat.lt_of_not_ge hstop'
    have hsucc_le : i + OfNat.ofNat 1 ≤ stop := Nat.succ_le_of_lt hi_lt_stop
    have hEq : stop = i + OfNat.ofNat 1 := Nat.le_antisymm hstop hsucc_le
    have h1 :
        ∀ start < i + OfNat.ofNat 1,
          Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0)
              (nums.extract start (i + OfNat.ofNat 1)) (OfNat.ofNat 0)
              (min (i + OfNat.ofNat 1) nums.size - start) ≤
            nums[i]! :=
      goal_1 nums bestEndingHere i a if_pos invariant_inv_ending_max if_pos_1
    have hstart : start < i + OfNat.ofNat 1 := by
      simpa [hEq] using hstartstop
    simpa [hEq] using h1 start hstart

theorem goal_4
    (nums : Array ℤ)
    (i : ℕ)
    (a : OfNat.ofNat 1 ≤ i)
    (if_pos : i < nums.size)
    : ∃ start < i + OfNat.ofNat 1, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start (i + OfNat.ofNat 1)) (OfNat.ofNat 0) (min (i + OfNat.ofNat 1) nums.size - start) = nums[i]! := by
    intros; expose_names; exact goal_0 nums i a if_pos

theorem goal_5
    (nums : Array ℤ)
    (bestEndingHere : ℤ)
    (i : ℕ)
    (a : OfNat.ofNat 1 ≤ i)
    (if_pos : i < nums.size)
    (invariant_inv_ending_max : ∀ start < i, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start i) (OfNat.ofNat 0) (min i nums.size - start) ≤ bestEndingHere)
    (if_pos_1 : bestEndingHere ≤ OfNat.ofNat 0)
    : ∀ start < i + OfNat.ofNat 1, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start (i + OfNat.ofNat 1)) (OfNat.ofNat 0) (min (i + OfNat.ofNat 1) nums.size - start) ≤ nums[i]! := by
    intros; expose_names; exact
        goal_1 nums bestEndingHere i a if_pos invariant_inv_ending_max if_pos_1 start h

theorem goal_6
    (nums : Array ℤ)
    (bestEndingHere : ℤ)
    (bestSoFar : ℤ)
    (i : ℕ)
    (a : OfNat.ofNat 1 ≤ i)
    (if_pos : i < nums.size)
    (invariant_inv_ending_max : ∀ start < i, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start i) (OfNat.ofNat 0) (min i nums.size - start) ≤ bestEndingHere)
    (invariant_inv_sofar_max : ∀ (start stop : ℕ), start < stop → stop ≤ i → Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) ≤ bestSoFar)
    (if_pos_1 : bestEndingHere ≤ OfNat.ofNat 0)
    (if_neg : nums[i]! ≤ bestSoFar)
    : ∀ (start stop : ℕ), start < stop → stop ≤ i + OfNat.ofNat 1 → Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) ≤ bestSoFar := by
  intro start stop hlt hstop
  by_cases hle : stop ≤ i
  · exact invariant_inv_sofar_max start stop hlt hle
  · have hi : i < stop := Nat.lt_of_not_ge hle
    have hsuc : i + 1 ≤ stop := by
      simpa [Nat.succ_eq_add_one] using (Nat.succ_le_of_lt hi)
    have hEq : stop = i + 1 := Nat.le_antisymm hstop hsuc
    subst hEq
    have hstart : start < i + 1 := by
      simpa using hlt
    have h_le_x :
        Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start (i + 1))
            (OfNat.ofNat 0) (min (i + 1) nums.size - start) ≤ nums[i]! := by
      simpa using (goal_5 nums bestEndingHere i a if_pos invariant_inv_ending_max if_pos_1 start hstart)
    exact le_trans h_le_x if_neg

theorem goal_7
    (nums : Array ℤ)
    (bestEndingHere : ℤ)
    (i : ℕ)
    (a : OfNat.ofNat 1 ≤ i)
    (a_1 : i ≤ nums.size)
    (if_pos : i < nums.size)
    (invariant_inv_ending_ex : ∃ start < i, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start i) (OfNat.ofNat 0) (min i nums.size - start) = bestEndingHere)
    : ∃ start < i + OfNat.ofNat 1, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start (i + OfNat.ofNat 1)) (OfNat.ofNat 0) (min (i + OfNat.ofNat 1) nums.size - start) = bestEndingHere + nums[i]! := by
  rcases invariant_inv_ending_ex with ⟨start, hstart_lt, hsum⟩
  refine ⟨start, Nat.lt_trans hstart_lt (Nat.lt_succ_self i), ?_⟩

  have hmin_i : min i nums.size = i := by
    exact Nat.min_eq_left a_1
  have hi1_le : i + 1 ≤ nums.size := by
    exact Nat.succ_le_of_lt if_pos
  have hmin_i1 : min (i + 1) nums.size = i + 1 := by
    exact Nat.min_eq_left hi1_le

  -- Convert the invariant sum to a full-array fold (stop = size of the extract).
  have hsum' : (nums.extract start i).foldl (fun acc x : ℤ => acc + x) 0 = bestEndingHere := by
    simpa [Array.size_extract] using hsum

  -- Decompose the next extract as appending `nums[i]!`.
  have hextract : nums.extract start (i + 1) = nums.extract start i ++ #[nums[i]!] := by
    have hpush : (nums.extract start i).push (nums[i]!) = nums.extract start (i + 1) := by
      simpa [Nat.min_eq_left (Nat.le_of_lt hstart_lt), (getElem!_pos nums i if_pos).symm] using
        (@Array.push_extract_getElem ℤ nums start i if_pos)
    calc
      nums.extract start (i + 1) = (nums.extract start i).push (nums[i]!) := by
        simpa using hpush.symm
      _ = nums.extract start i ++ #[nums[i]!] := by
        simpa using (@Array.push_eq_append_singleton ℤ (nums.extract start i) (nums[i]!))

  -- The stop for the fold is the full size of the appended array.
  have hstop : (min (i + 1) nums.size - start) = (nums.extract start i).size + (#[nums[i]!]).size := by
    have hle : start ≤ i := Nat.le_of_lt hstart_lt
    simpa [Array.size_extract, hmin_i, hmin_i1, Nat.succ_sub hle, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm]

  -- Compute the sum over the appended slice.
  calc
    Array.foldl (fun acc x : ℤ => acc + x) 0 (nums.extract start (i + 1)) 0 (min (i + 1) nums.size - start)
        = Array.foldl (fun acc x : ℤ => acc + x) 0 (nums.extract start i ++ #[nums[i]!]) 0 (min (i + 1) nums.size - start) := by
            simpa [hextract]
    _ = (#[nums[i]!]).foldl (fun acc x : ℤ => acc + x) ((nums.extract start i).foldl (fun acc x : ℤ => acc + x) 0) := by
          simpa using
            (Array.foldl_append' (f := fun acc x : ℤ => acc + x) (b := (0 : ℤ)) (xs := nums.extract start i)
              (ys := #[nums[i]!]) (stop := (min (i + 1) nums.size - start)) (w := hstop))
    _ = bestEndingHere + nums[i]! := by
          simpa [hsum']

theorem goal_8
    (nums : Array ℤ)
    (bestEndingHere : ℤ)
    (i : ℕ)
    (a : OfNat.ofNat 1 ≤ i)
    (if_pos : i < nums.size)
    (invariant_inv_ending_max : ∀ start < i, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start i) (OfNat.ofNat 0) (min i nums.size - start) ≤ bestEndingHere)
    (if_neg : OfNat.ofNat 0 < bestEndingHere)
    : ∀ start < i + OfNat.ofNat 1, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start (i + OfNat.ofNat 1)) (OfNat.ofNat 0) (min (i + OfNat.ofNat 1) nums.size - start) ≤ bestEndingHere + nums[i]! := by
  classical
  intro start hstart

  -- Rewrite the foldl over an extract as the usual `.foldl` over the whole extracted array.
  have foldl_extract_eq (s t : Nat) :
      Array.foldl (fun acc x : ℤ => acc + x) 0 (nums.extract s t) 0 (min t nums.size - s) =
        (nums.extract s t).foldl (fun acc x : ℤ => acc + x) 0 := by
    calc
      Array.foldl (fun acc x : ℤ => acc + x) 0 (nums.extract s t) 0 (min t nums.size - s)
          = Array.foldl (fun acc x : ℤ => acc + x) 0 (nums.extract s t) 0 (nums.extract s t).size := by
              simpa [Array.size_extract]
      _ = (nums.extract s t).foldl (fun acc x : ℤ => acc + x) 0 := rfl

  -- put the goal in `.foldl` form
  rw [foldl_extract_eq start (i + 1)]

  have inv_end_max (s : Nat) (hs : s < i) :
      (nums.extract s i).foldl (fun acc x : ℤ => acc + x) 0 ≤ bestEndingHere := by
    have h := invariant_inv_ending_max s hs
    simpa [foldl_extract_eq s i] using h

  -- size of the one-step extract is 1
  have hsize_i : (nums.extract i (i + 1)).size = 1 := by
    have hi1 : i + 1 ≤ nums.size := Nat.succ_le_of_lt if_pos
    have hmin : min (i + 1) nums.size = i + 1 := Nat.min_eq_left hi1
    calc
      (nums.extract i (i + 1)).size
          = min (i + 1) nums.size - i := by simp [Array.size_extract]
      _ = (i + 1) - i := by simp [hmin]
      _ = 1 := by simp

  -- `nums.extract i (i+1)` is a singleton
  have hextract_i : nums.extract i (i + 1) = #[nums[i]!] := by
    ext j hj
    ·
      simp [hsize_i]
    ·
      have hj' : j < 1 := by simpa [hsize_i] using hj
      have hj0 : j = 0 := Nat.lt_one_iff.mp hj'
      subst hj0

      have h0 : (0 : Nat) < (nums.extract i (i + 1)).size := by
        simpa [hsize_i]

      have hx := (Array.getElem_extract (xs := nums) (start := i) (stop := i + 1) (i := 0) h0)

      have hbang : nums[i]! = nums[i]'if_pos := by
        simp [Array.getElem!_eq_getD, Array.getD, getElem?_def, if_pos]

      have hp : (Array.getElem_extract_aux (xs := nums) (start := i) (stop := i + 1) h0) = if_pos :=
        Subsingleton.elim _ _

      calc
        (nums.extract i (i + 1))[0] = nums[i + 0]'(Array.getElem_extract_aux (xs := nums) (start := i) (stop := i + 1) h0) := by
          simpa using hx
        _ = nums[i]'(Array.getElem_extract_aux (xs := nums) (start := i) (stop := i + 1) h0) := by
          simp
        _ = nums[i]'if_pos := by
          cases hp
          rfl
        _ = nums[i]! := by
          simpa using hbang.symm

  -- fold over a singleton array
  have foldl_singleton (acc x : ℤ) :
      (#[x] : Array ℤ).foldl (fun acc x : ℤ => acc + x) acc = acc + x := by
    simpa using
      (by
        simpa using
          (List.foldl_toArray' (f := fun acc x : ℤ => acc + x) (init := acc) (l := [x])
            (stop := ([x] : List ℤ).toArray.size) (h := rfl)))

  have hfold_i (acc : ℤ) :
      (nums.extract i (i + 1)).foldl (fun acc x : ℤ => acc + x) acc = acc + nums[i]! := by
    simpa [hextract_i] using (foldl_singleton acc (nums[i]!))

  by_cases hsi : start < i
  ·
    have hsplit : nums.extract start i ++ nums.extract i (i + 1) = nums.extract start (i + 1) := by
      simpa [Nat.min_eq_left (Nat.le_of_lt hsi), Nat.max_eq_right (Nat.le_succ i)] using
        (@Array.extract_append_extract ℤ nums start i (i + 1))

    have h1 :
        (nums.extract start (i + 1)).foldl (fun acc x : ℤ => acc + x) 0 =
          (nums.extract start i ++ nums.extract i (i + 1)).foldl (fun acc x : ℤ => acc + x) 0 := by
      -- rewrite using the equality of arrays
      simpa using congrArg (fun arr => arr.foldl (fun acc x : ℤ => acc + x) 0) hsplit.symm

    have h2 :
        (nums.extract start i ++ nums.extract i (i + 1)).foldl (fun acc x : ℤ => acc + x) 0 =
          (nums.extract i (i + 1)).foldl (fun acc x : ℤ => acc + x)
            ((nums.extract start i).foldl (fun acc x : ℤ => acc + x) 0) := by
      -- direct use of `foldl_append`
      simpa using
        (Array.foldl_append (xs := nums.extract start i) (ys := nums.extract i (i + 1))
          (f := fun acc x : ℤ => acc + x) (b := (0 : ℤ)))

    have h3 :
        (nums.extract i (i + 1)).foldl (fun acc x : ℤ => acc + x)
            ((nums.extract start i).foldl (fun acc x : ℤ => acc + x) 0) =
          (nums.extract start i).foldl (fun acc x : ℤ => acc + x) 0 + nums[i]! := by
      -- apply the singleton fold computation
      simpa using hfold_i ((nums.extract start i).foldl (fun acc x : ℤ => acc + x) 0)

    have hsum :
        (nums.extract start (i + 1)).foldl (fun acc x : ℤ => acc + x) 0 =
          (nums.extract start i).foldl (fun acc x : ℤ => acc + x) 0 + nums[i]! := by
      -- chain the previous equalities
      calc
        (nums.extract start (i + 1)).foldl (fun acc x : ℤ => acc + x) 0
            = (nums.extract start i ++ nums.extract i (i + 1)).foldl (fun acc x : ℤ => acc + x) 0 := h1
        _ = (nums.extract i (i + 1)).foldl (fun acc x : ℤ => acc + x)
              ((nums.extract start i).foldl (fun acc x : ℤ => acc + x) 0) := h2
        _ = (nums.extract start i).foldl (fun acc x : ℤ => acc + x) 0 + nums[i]! := h3

    have hle :
        (nums.extract start i).foldl (fun acc x : ℤ => acc + x) 0 + nums[i]! ≤
          bestEndingHere + nums[i]! :=
      add_le_add_right (inv_end_max start hsi) (nums[i]!)

    -- conclude
    calc
      (nums.extract start (i + 1)).foldl (fun acc x : ℤ => acc + x) 0
          = (nums.extract start i).foldl (fun acc x : ℤ => acc + x) 0 + nums[i]! := hsum
      _ ≤ bestEndingHere + nums[i]! := hle

  ·
    have hEq : start = i := by
      have hle1 : start ≤ i := Nat.le_of_lt_succ hstart
      have hle2 : i ≤ start := Nat.le_of_not_gt hsi
      exact Nat.le_antisymm hle1 hle2

    -- rewrite `start` to `i`
    rw [hEq]

    have hsum : (nums.extract i (i + 1)).foldl (fun acc x : ℤ => acc + x) 0 = nums[i]! := by
      simpa [zero_add] using (hfold_i (0 : ℤ))

    have hnonneg : (0 : ℤ) ≤ bestEndingHere := le_of_lt if_neg
    have hle : nums[i]! ≤ bestEndingHere + nums[i]! := by
      simpa [zero_add] using (add_le_add_right hnonneg (nums[i]!))

    calc
      (nums.extract i (i + 1)).foldl (fun acc x : ℤ => acc + x) 0
          = nums[i]! := hsum
      _ ≤ bestEndingHere + nums[i]! := hle

theorem goal_9
    (nums : Array ℤ)
    (bestEndingHere : ℤ)
    (i : ℕ)
    (a : OfNat.ofNat 1 ≤ i)
    (if_pos : i < nums.size)
    (invariant_inv_ending_ex : ∃ start < i, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start i) (OfNat.ofNat 0) (min i nums.size - start) = bestEndingHere)
    : ∃ start stop, start < stop ∧ stop ≤ i + OfNat.ofNat 1 ∧ Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) = bestEndingHere + nums[i]! := by
  rcases invariant_inv_ending_ex with ⟨start, hstart, hsum⟩
  refine ⟨start, i + 1, ?_, ?_, ?_⟩
  · exact lt_trans hstart (Nat.lt_succ_self i)
  · simp
  ·
    -- convenient form of the invariant
    have hsum' : (nums.extract start i).foldl (fun acc x : ℤ => acc + x) (0:ℤ) = bestEndingHere := by
      simpa [Array.size_extract] using hsum

    -- relate `nums.extract start (i+1)` to pushing the next element
    have hextract : nums.extract start (i + 1) = (nums.extract start i).push nums[i] := by
      have h := (@Array.push_extract_getElem ℤ nums start i if_pos)
      simpa [Nat.min_eq_left (Nat.le_of_lt hstart)] using h.symm

    -- relate `getElem!` to `getElem` in the in-bounds case
    have hbang : nums[i]! = nums[i] := by
      simp [Array.getElem!_eq_getD, Array.getD, if_pos]

    -- prove the foldl equation in `.foldl` form, then convert back
    have hmain : (nums.extract start (i + 1)).foldl (fun acc x : ℤ => acc + x) (0:ℤ) = bestEndingHere + nums[i]! := by
      -- rewrite the segment as append of previous segment and a singleton
      -- and use foldl_append
      calc
        (nums.extract start (i + 1)).foldl (fun acc x : ℤ => acc + x) (0:ℤ)
            = ((nums.extract start i).push nums[i]).foldl (fun acc x : ℤ => acc + x) (0:ℤ) := by
                simpa [hextract]
        _ = ((nums.extract start i) ++ #[nums[i]]).foldl (fun acc x : ℤ => acc + x) (0:ℤ) := by
                rw [Array.push_eq_append_singleton]
        _ = (#[nums[i]] : Array ℤ).foldl (fun acc x : ℤ => acc + x)
              ((nums.extract start i).foldl (fun acc x : ℤ => acc + x) (0:ℤ)) := by
                -- foldl over append
                rw [Array.foldl_append]
        _ = bestEndingHere + nums[i]! := by
                -- fold over singleton and substitute
                simpa [hsum', hbang, add_assoc]

    -- switch back to the explicit-bounds foldl in the goal
    simpa [Array.size_extract] using hmain

theorem goal_10
    (nums : Array ℤ)
    (bestEndingHere : ℤ)
    (bestSoFar : ℤ)
    (i : ℕ)
    (a : OfNat.ofNat 1 ≤ i)
    (a_1 : i ≤ nums.size)
    (if_pos : i < nums.size)
    (require_1 : OfNat.ofNat 0 < nums.size)
    (invariant_inv_ending_ex : ∃ start < i, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start i) (OfNat.ofNat 0) (min i nums.size - start) = bestEndingHere)
    (invariant_inv_ending_max : ∀ start < i, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start i) (OfNat.ofNat 0) (min i nums.size - start) ≤ bestEndingHere)
    (invariant_inv_sofar_ex : ∃ start stop, start < stop ∧ stop ≤ i ∧ Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) = bestSoFar)
    (invariant_inv_sofar_max : ∀ (start stop : ℕ), start < stop → stop ≤ i → Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) ≤ bestSoFar)
    (if_neg : OfNat.ofNat 0 < bestEndingHere)
    (if_pos_1 : bestSoFar < bestEndingHere + nums[i]!)
    : ∀ (start stop : ℕ), start < stop → stop ≤ i + OfNat.ofNat 1 → Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) ≤ bestEndingHere + nums[i]! := by
    sorry

theorem goal_11
    (nums : Array ℤ)
    (bestEndingHere : ℤ)
    (bestSoFar : ℤ)
    (i : ℕ)
    (a_1 : i ≤ nums.size)
    (if_pos : i < nums.size)
    (invariant_inv_ending_ex : ∃ start < i, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start i) (OfNat.ofNat 0) (min i nums.size - start) = bestEndingHere)
    (invariant_inv_sofar_ex : ∃ start stop, start < stop ∧ stop ≤ i ∧ Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) = bestSoFar)
    : ∃ start < i + OfNat.ofNat 1, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start (i + OfNat.ofNat 1)) (OfNat.ofNat 0) (min (i + OfNat.ofNat 1) nums.size - start) = bestEndingHere + nums[i]! := by
  classical
  rcases invariant_inv_ending_ex with ⟨start, hstartLt, hsum⟩
  refine ⟨start, lt_trans hstartLt (Nat.lt_succ_self i), ?_⟩

  have hi1 : i + 1 ≤ nums.size := Nat.succ_le_of_lt if_pos
  have hmin_i : min i nums.size = i := Nat.min_eq_left a_1
  have hmin_ip1 : min (i + 1) nums.size = i + 1 := Nat.min_eq_left hi1

  have hsplit : nums.extract start (i + 1) = nums.extract start i ++ nums.extract i (i + 1) := by
    have h : nums.extract start i ++ nums.extract i (i + 1) = nums.extract (min start i) (max i (i + 1)) := by
      simpa using (@Array.extract_append_extract ℤ nums start i (i + 1))
    have h' : nums.extract start i ++ nums.extract i (i + 1) = nums.extract start (i + 1) := by
      simpa [Nat.min_eq_left (Nat.le_of_lt hstartLt), Nat.max_eq_right (Nat.le_succ i)] using h
    simpa using h'.symm

  have hsize_xs : (nums.extract start i).size = i - start := by
    simpa using (@Array.size_extract_of_le ℤ nums start i a_1)
  have hsize_ys : (nums.extract i (i + 1)).size = 1 := by
    simpa using (@Array.size_extract_of_le ℤ nums i (i + 1) hi1)

  have hstop : min (i + 1) nums.size - start = (nums.extract start i).size + (nums.extract i (i + 1)).size := by
    simp [hmin_ip1, hsize_xs, hsize_ys]
    omega

  have hgetElem! : nums[i]! = nums[i] := by
    calc
      nums[i]! = nums.getD i default := by simp [Array.getElem!_eq_getD]
      _ = (nums[i]?).getD default := by simp [Array.getD_eq_getD_getElem?]
      _ = nums[i] := by
        have hopt : nums[i]? = some nums[i] := by
          simpa using (Array.getElem?_eq_getElem (xs := nums) (i := i) if_pos)
        simpa [hopt]

  have hys_single : nums.extract i (i + 1) = #[nums[i]!] := by
    apply Array.ext_getElem?
    intro j
    by_cases hj : j = 0
    · subst hj
      have hopt : nums[i]? = some nums[i] := by
        simpa using (Array.getElem?_eq_getElem (xs := nums) (i := i) if_pos)
      -- compute both sides at index 0
      simp [Array.getElem?_extract, hmin_ip1, hopt, Array.getElem?_singleton, hgetElem!.symm]
    ·
      have hj1 : ¬ j < 1 := by
        intro hj'
        have : j = 0 := Nat.lt_one_iff.mp hj'
        exact hj this
      simp [Array.getElem?_extract, hmin_ip1, Array.getElem?_singleton, hj, hj1]

  have hfold :
      Array.foldl (fun acc x : ℤ => acc + x) 0 (nums.extract start (i + 1)) 0 (min (i + 1) nums.size - start)
        = (Array.foldl (fun acc x : ℤ => acc + x) 0 (nums.extract start i) 0 (min i nums.size - start)) + nums[i]! := by
    have h :=
      (Array.foldl_append' (f := fun acc x : ℤ => acc + x) (b := (0 : ℤ))
        (xs := nums.extract start i) (ys := nums.extract i (i + 1)) (stop := min (i + 1) nums.size - start) hstop)
    simpa [hsplit, hys_single, hmin_i, hmin_ip1] using h

  simpa [hfold, hsum]

theorem goal_12
    (nums : Array ℤ)
    (bestEndingHere : ℤ)
    (i : ℕ)
    (a : OfNat.ofNat 1 ≤ i)
    (if_pos : i < nums.size)
    (invariant_inv_ending_max : ∀ start < i, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start i) (OfNat.ofNat 0) (min i nums.size - start) ≤ bestEndingHere)
    (if_neg : OfNat.ofNat 0 < bestEndingHere)
    : ∀ start < i + OfNat.ofNat 1, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start (i + OfNat.ofNat 1)) (OfNat.ofNat 0) (min (i + OfNat.ofNat 1) nums.size - start) ≤ bestEndingHere + nums[i]! := by
    intros; expose_names; exact
        goal_8 nums bestEndingHere i a if_pos invariant_inv_ending_max if_neg start h

theorem goal_13
    (nums : Array ℤ)
    (bestEndingHere : ℤ)
    (bestSoFar : ℤ)
    (i : ℕ)
    (a : OfNat.ofNat 1 ≤ i)
    (a_1 : i ≤ nums.size)
    (if_pos : i < nums.size)
    (require_1 : OfNat.ofNat 0 < nums.size)
    (invariant_inv_ending_ex : ∃ start < i, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start i) (OfNat.ofNat 0) (min i nums.size - start) = bestEndingHere)
    (invariant_inv_ending_max : ∀ start < i, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start i) (OfNat.ofNat 0) (min i nums.size - start) ≤ bestEndingHere)
    (invariant_inv_sofar_ex : ∃ start stop, start < stop ∧ stop ≤ i ∧ Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) = bestSoFar)
    (invariant_inv_sofar_max : ∀ (start stop : ℕ), start < stop → stop ≤ i → Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) ≤ bestSoFar)
    (if_neg : OfNat.ofNat 0 < bestEndingHere)
    (if_neg_1 : bestEndingHere + nums[i]! ≤ bestSoFar)
    : ∀ (start stop : ℕ), start < stop → stop ≤ i + OfNat.ofNat 1 → Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) ≤ bestSoFar := by
    sorry

theorem goal_14
    (nums : Array ℤ)
    (require_1 : OfNat.ofNat 0 < nums.size)
    : Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract (OfNat.ofNat 0) (OfNat.ofNat 1)) (OfNat.ofNat 0) (min (OfNat.ofNat 1) nums.size) = nums[OfNat.ofNat 0]! := by
    sorry

theorem goal_15
    (nums : Array ℤ)
    (require_1 : OfNat.ofNat 0 < nums.size)
    : Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract (OfNat.ofNat 0) (OfNat.ofNat 1)) (OfNat.ofNat 0) (min (OfNat.ofNat 1) nums.size) ≤ nums[OfNat.ofNat 0]! := by
    sorry

theorem goal_16
    (nums : Array ℤ)
    (require_1 : OfNat.ofNat 0 < nums.size)
    : ∃ start stop, start < stop ∧ stop ≤ OfNat.ofNat 1 ∧ Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) = nums[OfNat.ofNat 0]! := by
    sorry

theorem goal_17
    (nums : Array ℤ)
    (require_1 : OfNat.ofNat 0 < nums.size)
    : ∀ (start stop : ℕ), start < stop → stop ≤ OfNat.ofNat 1 → Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) ≤ nums[OfNat.ofNat 0]! := by
    sorry

set_option maxHeartbeats 10000000


prove_correct MaximumSubarray by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at *); try (conv => congr <;> simp) ; try expose_names)
  exact (goal_0 nums i a if_pos)
  exact (goal_1 nums bestEndingHere i a if_pos invariant_inv_ending_max if_pos_1)
  exact (goal_2 nums i a if_pos)
  exact (goal_3 nums bestEndingHere bestSoFar i a if_pos invariant_inv_ending_max invariant_inv_sofar_max if_pos_1 if_pos_2)
  exact (goal_4 nums i a if_pos)
  exact (goal_5 nums bestEndingHere i a if_pos invariant_inv_ending_max if_pos_1)
  exact (goal_6 nums bestEndingHere bestSoFar i a if_pos invariant_inv_ending_max invariant_inv_sofar_max if_pos_1 if_neg)
  exact (goal_7 nums bestEndingHere i a a_1 if_pos invariant_inv_ending_ex)
  exact (goal_8 nums bestEndingHere i a if_pos invariant_inv_ending_max if_neg)
  exact (goal_9 nums bestEndingHere i a if_pos invariant_inv_ending_ex)
  exact (goal_10 nums bestEndingHere bestSoFar i a a_1 if_pos require_1 invariant_inv_ending_ex invariant_inv_ending_max invariant_inv_sofar_ex invariant_inv_sofar_max if_neg if_pos_1)
  exact (goal_11 nums bestEndingHere bestSoFar i a_1 if_pos invariant_inv_ending_ex invariant_inv_sofar_ex)
  exact (goal_12 nums bestEndingHere i a if_pos invariant_inv_ending_max if_neg)
  exact (goal_13 nums bestEndingHere bestSoFar i a a_1 if_pos require_1 invariant_inv_ending_ex invariant_inv_ending_max invariant_inv_sofar_ex invariant_inv_sofar_max if_neg if_neg_1)
  exact (goal_14 nums require_1)
  exact (goal_15 nums require_1)
  exact (goal_16 nums require_1)
  exact (goal_17 nums require_1)

end Proof
