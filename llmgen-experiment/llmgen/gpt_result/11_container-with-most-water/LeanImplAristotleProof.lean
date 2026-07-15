/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 0805d295-aade-418f-bd9c-ed8217dfec7d

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem correctness_goal_0 (height : Array ℕ) (h_precond : precondition height) (hn2 : ¬height.size < 2) (himpl : implementation height = implementation.go height 0 (height.size - 1) 0) : postcondition height (implementation.go height 0 (height.size - 1) 0)
-/

import Lean

import Mathlib.Tactic


set_option maxHeartbeats 10000000

section Specs

-- Never add new imports here

set_option maxHeartbeats 10000000

set_option pp.coercions false

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

def implementation (height : Array Nat) : Nat :=
  let n := height.size
  if h : n < 2 then
    0
  else
    let rec go (l r best : Nat) : Nat :=
      if hlt : l < r then
        let hl := height[l]!
        let hr := height[r]!
        let area := (r - l) * Nat.min hl hr
        let best' := Nat.max best area
        if hl ≤ hr then
          go (l + 1) r best'
        else
          go l (r - 1) best'
      else
        best
    termination_by r - l
    go 0 (n - 1) 0

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

section Proof

noncomputable section AristotleLemmas

/-
If height[l] <= height[r], then for any j in (l, r], the area of (l, j) is at most the area of (l, r).
Symmetrically, if height[r] < height[l], then for any i in [l, r), the area of (i, r) is at most the area of (l, r).
-/
lemma lemma_step_bound (height : Array Nat) (l r : Nat) (h_lr : l < r) :
  (height[l]! ≤ height[r]! → ∀ j, l < j → j ≤ r → pairArea height l j ≤ pairArea height l r) ∧
  (height[r]! < height[l]! → ∀ i, l ≤ i → i < r → pairArea height i r ≤ pairArea height l r) := by
  unfold pairArea;
  constructor <;> intros <;> gcongr;
  · grind +ring;
  · grind

lemma lemma_reduction (height : Array Nat) (l r : Nat) (h_lr : l < r) :
  (height[l]! ≤ height[r]! → ∀ i j, l ≤ i → i < j → j ≤ r → pairArea height i j ≤ pairArea height l r ∨ (l + 1 ≤ i ∧ i < j ∧ j ≤ r)) ∧
  (height[r]! < height[l]! → ∀ i j, l ≤ i → i < j → j ≤ r → pairArea height i j ≤ pairArea height l r ∨ (l ≤ i ∧ i < j ∧ j ≤ r - 1)) := by
  constructor;
  · intro h_le i j hi hj hr
    by_cases h_cases : i = l;
    · exact Or.inl ( by simpa [ h_cases ] using lemma_step_bound height l r h_lr |>.1 h_le j ( by linarith ) ( by linarith ) );
    · exact Or.inr ⟨ Nat.succ_le_of_lt ( lt_of_le_of_ne hi ( Ne.symm h_cases ) ), hj, hr ⟩;
  · intro h_lt i j hi hj hr
    by_cases hj_r : j = r;
    · -- Apply the lemma_step_bound with the given conditions.
      have := lemma_step_bound height l r h_lr; aesop;
    · exact Or.inr ⟨ hi, hj, Nat.le_sub_one_of_lt ( lt_of_le_of_ne hr hj_r ) ⟩

lemma go_correctness (height : Array Nat) (l r best : Nat) (h_lr : l ≤ r) :
  (implementation.go height l r best ≥ best) ∧
  (∀ i j, l ≤ i → i < j → j ≤ r → implementation.go height l r best ≥ pairArea height i j) ∧
  (implementation.go height l r best = best ∨ ∃ i j, l ≤ i ∧ i < j ∧ j ≤ r ∧ implementation.go height l r best = pairArea height i j) := by
  revert l r best h_lr;
  intros l r best hlr; induction' h : r - l using Nat.strong_induction_on with k ih generalizing l r best; rcases k with ( _ | k ) <;> simp_all +decide [ Nat.sub_succ ] ;
  · unfold implementation.go;
    grind;
  · unfold implementation.go; split_ifs <;> simp_all +decide [ Nat.sub_eq_iff_eq_add' hlr ] ;
    split_ifs;
    · specialize ih k ( Nat.lt_succ_self k ) ( l + 1 ) ( l + ( k + 1 ) ) ( Nat.max best ( ( k + 1 ) * height[l]! ) ) ; simp_all +decide [ Nat.add_sub_add_left ];
      constructor;
      · intro i j hi hj hj'; by_cases hi' : i = l <;> by_cases hj' : j = l + ( k + 1 ) <;> simp_all +decide [ pairArea ] ;
        · refine' le_trans _ ( ih.1.2 );
          exact Nat.mul_le_mul ( Nat.sub_le_of_le_add <| by linarith ) ( Nat.min_le_left _ _ ) |> le_trans <| Nat.mul_le_mul_left _ <| by omega;
        · exact ih.2.1 i ( l + ( k + 1 ) ) ( by omega ) ( by omega ) ( by omega );
        · exact ih.2.1 i j ( lt_of_le_of_ne hi ( Ne.symm hi' ) ) hj ( by omega );
      · rcases ih.2.2 with h | ⟨ i, hi, j, hj, hj', h ⟩ <;> simp_all +decide [ Nat.max_def ];
        · split_ifs <;> simp_all +decide [ Nat.add_comm, Nat.add_left_comm ];
          exact Or.inr ⟨ l, by linarith, l + ( k + 1 ), by linarith, by linarith, by unfold pairArea; aesop ⟩;
        · grind;
    · specialize ih k ( Nat.lt_succ_self k ) l ( l + k ) ( best.max ( ( k + 1 ) * height[l]!.min height[l + ( k + 1 ) ]! ) ) ; simp_all +decide [ Nat.sub_eq_iff_eq_add' ] ;
      refine' ⟨ _, _ ⟩;
      · intro i j hi hj hj'; rcases hj' with ( _ | hj' ) <;> simp_all +arith +decide;
        -- By the properties of the algorithm, we know that the area of the pair (i, l + k + 1) is less than or equal to the area of the pair (l, l + k + 1).
        have h_area_le : pairArea height i (l + k + 1) ≤ (k + 1) * height[l]!.min height[l + k + 1]! := by
          unfold pairArea; simp +arith +decide [ *, Nat.min_def ] ;
          split_ifs <;> nlinarith [ Nat.sub_add_cancel ( by linarith : i ≤ l + k + 1 ) ] ;
        grind;
      · rcases ih.2.2 with h | ⟨ i, hi, j, hj, hj', h ⟩ <;> simp_all +decide [ Nat.add_assoc ];
        · refine' Classical.or_iff_not_imp_left.2 fun h => ⟨ l, by linarith, l + ( k + 1 ), by linarith, by linarith, _ ⟩ ; simp_all +decide [ pairArea ];
          linarith;
        · exact Or.inr ⟨ i, hi, j, hj, by linarith, rfl ⟩

end AristotleLemmas

theorem correctness_goal_0 (height : Array ℕ) (h_precond : precondition height) (hn2 : ¬height.size < 2) (himpl : implementation height = implementation.go height 0 (height.size - 1) 0) : postcondition height (implementation.go height 0 (height.size - 1) 0) := by
    -- Apply the go_correctness lemma to conclude the proof.
    apply And.intro;
    · have := go_correctness height 0 ( height.size - 1 ) 0 ( Nat.zero_le _ );
      rcases this.2.2 with h | ⟨ i, j, hi, hj, hj', h ⟩ <;> [ refine' ⟨ 0, 1, _, _, _ ⟩ ; refine' ⟨ i, j, _, _, _ ⟩ ] <;> try omega;
      grind;
    · exact fun i j hij hj => go_correctness height 0 ( height.size - 1 ) 0 ( Nat.zero_le _ ) |>.2.1 i j ( Nat.zero_le _ ) hij ( Nat.le_pred_of_lt hj )

end Proof