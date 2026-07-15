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
    ContainerWithMostWater: given an array of line heights, return the maximum water area.
    Natural language breakdown:
    1. The input is an array `height` of nonnegative integers, interpreted as vertical lines at x-coordinates 0..n-1.
    2. For any two distinct indices i < j, a container can be formed with width (j - i).
    3. The container height is limited by the shorter line: min(height[i], height[j]).
    4. The area (water amount) for a pair (i, j) is (j - i) * min(height[i], height[j]).
    5. The desired result is the maximum area over all index pairs with i < j.
    6. If the array has fewer than 2 elements, no valid container exists; we therefore require size ≥ 2.
    Your algorithm should run in **O(n)** time and **O(1)** extra space (in-place).
-/

section Specs
-- Area contributed by a particular pair of indices (i,j).
-- Uses Nat throughout since heights and areas are nonnegative.
-- Defined as 0 if indices are out of range or not ordered; preconditions/postconditions will use it only with i<j<size.
def pairArea (height : Array Nat) (i : Nat) (j : Nat) : Nat :=
  (j - i) * Nat.min (height[i]!) (height[j]!)

-- Precondition: at least two lines exist.
def precondition (height : Array Nat) : Prop :=
  height.size ≥ 2

-- Postcondition: result is an achievable maximum area.
-- 1) There exists a pair i<j within bounds whose area equals result.
-- 2) For all pairs i<j within bounds, their area is ≤ result.
def postcondition (height : Array Nat) (result : Nat) : Prop :=
  (∃ (i : Nat) (j : Nat), i < j ∧ j < height.size ∧ pairArea height i j = result) ∧
  (∀ (i : Nat) (j : Nat), i < j → j < height.size → pairArea height i j ≤ result)
end Specs

section Impl
method ContainerWithMostWater (height : Array Nat)
  return (result : Nat)
  require precondition height
  ensures postcondition height result
  do
  -- Two-pointer O(n) scan.
  let mut left : Nat := 0
  let mut right : Nat := height.size - 1
  let mut best : Nat := 0

  while left < right
    -- Pointer bounds + ordering; implies both pointers are within array.
    invariant "cwmw_bounds" left ≤ right ∧ right < height.size
    -- best is always an achieved area (or 0 initially).
    invariant "cwmw_best_witness"
      best = 0 ∨ (∃ i j, i < j ∧ j < height.size ∧ pairArea height i j = best)
    -- All pairs that have been ruled out (outside the current [left,right] window)
    -- are proved to have area ≤ best.
    invariant "cwmw_ruled_out"
      ∀ i j, i < j → j < height.size → (i < left ∨ right < j) → pairArea height i j ≤ best
    -- Termination: distance between pointers strictly decreases each iteration.
    decreasing right - left
  do
    let hl : Nat := height[left]!
    let hr : Nat := height[right]!
    let width : Nat := right - left
    let hmin : Nat := Nat.min hl hr
    let area : Nat := width * hmin
    if best < area then
      best := area
    -- Move the pointer at the shorter line.
    if hl ≤ hr then
      left := left + 1
    else
      right := right - 1

  return best
end Impl

section TestCases
-- Test case 1: Example 1 from prompt
-- height = [1,8,6,2,5,4,8,3,7], expected max area = 49
-- (i=1,j=8) => width=7, min(8,7)=7, area=49

def test1_height : Array Nat := #[1, 8, 6, 2, 5, 4, 8, 3, 7]

def test1_Expected : Nat := 49

-- Test case 2: Example 2 from prompt
-- height = [1,1], only pair gives area 1

def test2_height : Array Nat := #[1, 1]

def test2_Expected : Nat := 1

-- Test case 3: Minimal size with a zero
-- height = [0,0] => area 0

def test3_height : Array Nat := #[0, 0]

def test3_Expected : Nat := 0

-- Test case 4: Strictly increasing
-- Best is (1,4): width 3, min(2,5)=2 => 6

def test4_height : Array Nat := #[1, 2, 3, 4, 5]

def test4_Expected : Nat := 6

-- Test case 5: Strictly decreasing
-- Best is (0,3): width 3, min(5,2)=2 => 6

def test5_height : Array Nat := #[5, 4, 3, 2, 1]

def test5_Expected : Nat := 6

-- Test case 6: All equal
-- height = [3,3,3,3] => best endpoints (0,3): width 3 * 3 = 9

def test6_height : Array Nat := #[3, 3, 3, 3]

def test6_Expected : Nat := 9

-- Test case 7: Zeros inside, tall endpoints
-- height = [5,0,0,0,5] => width 4 * min(5,5)=20

def test7_height : Array Nat := #[5, 0, 0, 0, 5]

def test7_Expected : Nat := 20

-- Test case 8: Multiple maxima possible
-- height = [2,4,2,4,2]
-- (0,4): width 4 * min(2,2)=8
-- (1,3): width 2 * min(4,4)=8

def test8_height : Array Nat := #[2, 4, 2, 4, 2]

def test8_Expected : Nat := 8

-- Test case 9: Classic mixed small array
-- height = [1,2,1] => best (0,2): width 2 * min(1,1)=2

def test9_height : Array Nat := #[1, 2, 1]

def test9_Expected : Nat := 2
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((ContainerWithMostWater test1_height).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((ContainerWithMostWater test2_height).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((ContainerWithMostWater test3_height).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((ContainerWithMostWater test4_height).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((ContainerWithMostWater test5_height).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((ContainerWithMostWater test6_height).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((ContainerWithMostWater test7_height).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((ContainerWithMostWater test8_height).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((ContainerWithMostWater test9_height).run), DivM.res test9_Expected ]
end Assertions

section Pbt
velvet_plausible_test ContainerWithMostWater (config := { maxMs := some 20000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000

theorem goal_0
    (height : Array ℕ)
    (best : ℕ)
    (left : ℕ)
    (right : ℕ)
    (invariant_cwmw_ruled_out : ∀ (i j : ℕ), i < j → j < height.size → i < left ∨ right < j → pairArea height i j ≤ best)
    (if_pos_1 : best < (right - left) * height[left]!.min height[right]!)
    (if_pos_2 : height[left]! ≤ height[right]!)
    : ∀ (i j : ℕ), i < j → j < height.size → i < left + OfNat.ofNat 1 ∨ right < j → pairArea height i j ≤ (right - left) * height[left]!.min height[right]! := by
  intro i j hij hj hOut
  have best_le_area : best ≤ (right - left) * height[left]!.min height[right]! :=
    Nat.le_of_lt if_pos_1

  by_cases hR : right < j
  · have hpa_le_best : pairArea height i j ≤ best :=
      invariant_cwmw_ruled_out i j hij hj (Or.inr hR)
    exact le_trans hpa_le_best best_le_area
  · have hjle : j ≤ right := by
      apply le_of_not_gt
      simpa [gt_iff_lt] using hR

    have hiSucc : i < left + 1 := by
      rcases hOut with hiSucc | hR'
      · exact hiSucc
      · exact False.elim (hR hR')

    by_cases hL : i < left
    · have hpa_le_best : pairArea height i j ≤ best :=
        invariant_cwmw_ruled_out i j hij hj (Or.inl hL)
      exact le_trans hpa_le_best best_le_area
    · have hleftle : left ≤ i := by
        apply le_of_not_gt
        simpa [gt_iff_lt] using hL

      have hi_le : i ≤ left := by
        have : i < left.succ := by
          simpa [Nat.succ_eq_add_one] using hiSucc
        exact (Nat.lt_succ_iff.mp this)

      have hiEq : i = left := le_antisymm hi_le hleftle
      subst i

      have hwidth_le : j - left ≤ right - left := by
        exact Nat.sub_le_sub_right hjle left

      have hmin_le : Nat.min (height[left]!) (height[j]!) ≤ height[left]! :=
        Nat.min_le_left _ _

      have hmul1 : (j - left) * Nat.min (height[left]!) (height[j]!) ≤ (j - left) * height[left]! := by
        exact Nat.mul_le_mul_left (j - left) hmin_le

      have hmul2 : (j - left) * height[left]! ≤ (right - left) * height[left]! := by
        exact Nat.mul_le_mul_right (height[left]!) hwidth_le

      have hpa_le : pairArea height left j ≤ (right - left) * height[left]! := by
        simpa [pairArea] using le_trans hmul1 hmul2

      simpa [min_eq_left if_pos_2] using hpa_le

theorem goal_1
    (height : Array ℕ)
    (best : ℕ)
    (left : ℕ)
    (right : ℕ)
    (invariant_cwmw_ruled_out : ∀ (i j : ℕ), i < j → j < height.size → i < left ∨ right < j → pairArea height i j ≤ best)
    (if_pos : left < right)
    (if_pos_1 : best < (right - left) * height[left]!.min height[right]!)
    (if_neg : ¬height[left]! ≤ height[right]!)
    : ∀ (i j : ℕ), i < j → j < height.size → i < left ∨ right - OfNat.ofNat 1 < j → pairArea height i j ≤ (right - left) * height[left]!.min height[right]! := by
  intro i j hij hjSize hOutside

  have hbest_le_area : best ≤ (right - left) * height[left]!.min height[right]! :=
    Nat.le_of_lt if_pos_1

  cases hOutside with
  | inl hil =>
      have hruled : pairArea height i j ≤ best :=
        invariant_cwmw_ruled_out i j hij hjSize (Or.inl hil)
      exact le_trans hruled hbest_le_area

  | inr hnew =>
      -- From left < right we know right > 0, hence (right-1)+1 = right.
      have hrpos : 0 < right := lt_of_le_of_lt (Nat.zero_le left) if_pos
      have h1le : 1 ≤ right := by
        simpa using (Nat.succ_le_iff.2 hrpos)

      have hrle : right ≤ j := by
        have : right - 1 + 1 ≤ j := by
          -- succ (right - 1) ≤ j
          simpa [Nat.succ_eq_add_one] using (Nat.succ_le_of_lt (by simpa using hnew))
        simpa [Nat.sub_add_cancel h1le] using this

      by_cases hjr : j = right
      · -- j = right is the new case introduced by decrementing right.
        subst j
        -- Now show pairArea height i right ≤ area.
        by_cases hil : i < left
        · have hruled : pairArea height i right ≤ best :=
            invariant_cwmw_ruled_out i right hij hjSize (Or.inl hil)
          exact le_trans hruled hbest_le_area
        · have hile : left ≤ i := Nat.le_of_not_gt hil
          have hwidth : right - i ≤ right - left := Nat.sub_le_sub_left hile right

          have hhrlt : height[right]! < height[left]! := by
            exact lt_of_not_ge if_neg
          have hmin_lr : Nat.min (height[left]!) (height[right]!) = height[right]! :=
            Nat.min_eq_right (le_of_lt hhrlt)

          have hmin_le : Nat.min (height[i]!) (height[right]!) ≤ height[right]! :=
            Nat.min_le_right _ _
          have hstep1 : (right - i) * Nat.min (height[i]!) (height[right]!) ≤ (right - i) * height[right]! :=
            Nat.mul_le_mul_left (right - i) hmin_le
          have hstep2 : (right - i) * height[right]! ≤ (right - left) * height[right]! :=
            Nat.mul_le_mul_right (height[right]!) hwidth

          calc
            pairArea height i right
                = (right - i) * Nat.min (height[i]!) (height[right]!) := by
                    simp [pairArea]
            _ ≤ (right - i) * height[right]! := hstep1
            _ ≤ (right - left) * height[right]! := hstep2
            _ = (right - left) * height[left]!.min height[right]! := by
                    -- min(height[left],height[right]) = height[right] because height[right] < height[left]
                    simpa [hmin_lr, Nat.min_eq_right (le_of_lt hhrlt)]

      · -- If j ≠ right, then right < j, so we can use the old ruled-out invariant.
        have hne : right ≠ j := by
          intro h
          exact hjr (h.symm)
        have hlt : right < j := Ne.lt_of_le hne hrle
        have hruled : pairArea height i j ≤ best :=
          invariant_cwmw_ruled_out i j hij hjSize (Or.inr hlt)
        exact le_trans hruled hbest_le_area

theorem goal_2
    (height : Array ℕ)
    (best : ℕ)
    (left : ℕ)
    (right : ℕ)
    (invariant_cwmw_ruled_out : ∀ (i j : ℕ), i < j → j < height.size → i < left ∨ right < j → pairArea height i j ≤ best)
    (if_neg : ¬best < (right - left) * height[left]!.min height[right]!)
    (if_pos_1 : height[left]! ≤ height[right]!)
    : ∀ (i j : ℕ), i < j → j < height.size → i < left + OfNat.ofNat 1 ∨ right < j → pairArea height i j ≤ best := by
  intro i j hij hj h_out
  rcases h_out with h_i | h_r
  · -- case: i < left + 1
    have h_i' : i < left + 1 := by simpa using h_i
    have hle : i ≤ left := by
      apply Nat.le_of_lt_succ
      simpa [Nat.succ_eq_add_one] using h_i'
    rcases Nat.eq_or_lt_of_le hle with hi_eq | hlt
    · -- subcase i = left
      subst i
      by_cases hjr : right < j
      · exact invariant_cwmw_ruled_out left j hij hj (Or.inr hjr)
      · have hjle : j ≤ right := le_of_not_lt hjr
        have hA : (right - left) * height[left]!.min height[right]! ≤ best :=
          le_of_not_lt if_neg
        have hA' : (right - left) * height[left]! ≤ best := by
          simpa [Nat.min_eq_left if_pos_1] using hA
        have hwidth : j - left ≤ right - left := Nat.sub_le_sub_right hjle left
        have hpair : pairArea height left j ≤ (right - left) * height[left]! := by
          dsimp [pairArea]
          have hmin : Nat.min (height[left]!) (height[j]!) ≤ height[left]! :=
            Nat.min_le_left _ _
          have h1 : (j - left) * Nat.min (height[left]!) (height[j]!) ≤ (j - left) * height[left]! :=
            Nat.mul_le_mul_left (j - left) hmin
          have h2 : (j - left) * height[left]! ≤ (right - left) * height[left]! :=
            Nat.mul_le_mul_right (height[left]!) hwidth
          exact le_trans h1 h2
        exact le_trans hpair hA'
    · -- subcase i < left
      exact invariant_cwmw_ruled_out i j hij hj (Or.inl hlt)
  · -- case: right < j
    exact invariant_cwmw_ruled_out i j hij hj (Or.inr h_r)

theorem goal_3
    (height : Array ℕ)
    (best : ℕ)
    (left : ℕ)
    (right : ℕ)
    (invariant_cwmw_ruled_out : ∀ (i j : ℕ), i < j → j < height.size → i < left ∨ right < j → pairArea height i j ≤ best)
    (if_pos : left < right)
    (if_neg : ¬best < (right - left) * height[left]!.min height[right]!)
    (if_neg_1 : ¬height[left]! ≤ height[right]!)
    : ∀ (i j : ℕ), i < j → j < height.size → i < left ∨ right - OfNat.ofNat 1 < j → pairArea height i j ≤ best := by
  intro i j hij hjsize hcond
  cases hcond with
  | inl hi =>
      exact invariant_cwmw_ruled_out i j hij hjsize (Or.inl hi)
  | inr hjpred =>
      by_cases hi : i < left
      · exact invariant_cwmw_ruled_out i j hij hjsize (Or.inl hi)
      · have hile : left ≤ i := Nat.le_of_not_lt hi
        have h0 : 0 < right := Nat.lt_of_le_of_lt (Nat.zero_le left) if_pos
        have hrpos : 1 ≤ right := Nat.succ_le_of_lt h0
        have hjle : right ≤ j := by
          have : right - 1 + 1 ≤ j := Nat.succ_le_of_lt hjpred
          simpa [Nat.sub_add_cancel hrpos] using this
        have hjcases : right = j ∨ right < j := eq_or_lt_of_le hjle
        cases hjcases with
        | inr hjlt =>
            exact invariant_cwmw_ruled_out i j hij hjsize (Or.inr hjlt)
        | inl hEq =>
            subst hEq
            have harea_le_best : (right - left) * Nat.min (height[left]!) (height[right]!) ≤ best := by
              exact Nat.le_of_not_gt (by simpa using if_neg)
            have hhr_lt_hl : height[right]! < height[left]! := by
              exact lt_of_not_ge (by simpa using if_neg_1)
            have hmin_lr : Nat.min (height[left]!) (height[right]!) = height[right]! := by
              exact min_eq_right (le_of_lt hhr_lt_hl)
            have harea2 : (right - left) * height[right]! ≤ best := by
              simpa [hmin_lr] using harea_le_best
            have hsub : right - i ≤ right - left := by
              exact Nat.sub_le_sub_left hile right
            have hpair : pairArea height i right ≤ (right - left) * height[right]! := by
              -- bound by shrinking width and height
              have hmin : Nat.min (height[i]!) (height[right]!) ≤ height[right]! := by
                exact Nat.min_le_right _ _
              have h1 : (right - i) * Nat.min (height[i]!) (height[right]!) ≤ (right - i) * height[right]! := by
                exact Nat.mul_le_mul_left (right - i) hmin
              have h2 : (right - i) * height[right]! ≤ (right - left) * height[right]! := by
                exact Nat.mul_le_mul_right (height[right]!) hsub
              simpa [pairArea] using (le_trans h1 h2)
            exact le_trans hpair harea2


prove_correct ContainerWithMostWater by
  loom_solve <;> (try injections; try subst_vars; try (conv => congr <;> simp) ; try expose_names)
  exact (goal_0 height best left right invariant_cwmw_ruled_out if_pos_1 if_pos_2)
  exact (goal_1 height best left right invariant_cwmw_ruled_out if_pos if_pos_1 if_neg)
  exact (goal_2 height best left right invariant_cwmw_ruled_out if_neg if_pos_1)
  exact (goal_3 height best left right invariant_cwmw_ruled_out if_pos if_neg if_neg_1)
end Proof
