/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: ea4d03e1-cd45-466e-9d77-1bd7e49a1ef1

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (heights : List (Int)) : VerinaSpec.rain_precond heights ↔ LLMSpec.precondition heights

- theorem postcondition_equiv (heights : List (Int)) (result : Int) : LLMSpec.precondition heights →
  (VerinaSpec.rain_postcond heights result ↔ LLMSpec.postcondition heights result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def rain_precond (heights : List (Int)) : Prop :=
  heights.all (fun h => h >= 0)

def rain_postcond (heights : List (Int)) (result: Int) : Prop :=
  result >= 0 ∧
  if heights.length < 3 then result = 0 else
    result =
      let max_left_at := λ i =>
        let rec ml (j : Nat) (max_so_far : Int) : Int :=
          if j > i then max_so_far
          else ml (j+1) (max max_so_far (heights[j]!))
          termination_by i + 1 - j
        ml 0 0
      let max_right_at := λ i =>
        let rec mr (j : Nat) (max_so_far : Int) : Int :=
          if j >= heights.length then max_so_far
          else mr (j+1) (max max_so_far (heights[j]!))
          termination_by heights.length - j
        mr i 0
      let water_at := λ i =>
        max 0 (min (max_left_at i) (max_right_at i) - heights[i]!)
      let rec sum_water (i : Nat) (acc : Int) : Int :=
        if i >= heights.length then acc
        else sum_water (i+1) (acc + water_at i)
        termination_by heights.length - i
      sum_water 0 0

end VerinaSpec

namespace LLMSpec

-- Helper: maximum height seen from the left up to (and including) index i.
-- Defined using take and foldl; for i out of range, it still yields a well-defined value.
def leftMaxUpTo (heights : List Int) (i : Nat) : Int :=
  (heights.take (i + 1)).foldl (init := (0 : Int)) max

-- Helper: maximum height seen from the right starting at index i.
def rightMaxFrom (heights : List Int) (i : Nat) : Int :=
  (heights.drop i).foldl (init := (0 : Int)) max

-- Helper: expected trapped water at index i, defaulting to 0 when i is out of range.
def expectedWaterAt (heights : List Int) (i : Nat) : Int :=
  match heights.get? i with
  | none => 0
  | some h =>
      max 0 (min (leftMaxUpTo heights i) (rightMaxFrom heights i) - h)

-- Preconditions: all heights are non-negative.
def precondition (heights : List Int) : Prop :=
  ∀ (i : Nat), i < heights.length → 0 ≤ (heights.get? i).getD 0

-- Postcondition: there exists a per-index water list whose elements match expectedWaterAt,
-- and result is the sum of these elements.
def postcondition (heights : List Int) (result : Int) : Prop :=
  (0 ≤ result) ∧
  (∃ (water : List Int),
    water.length = heights.length ∧
    water.sum = result ∧
    (∀ (i : Nat), i < heights.length → water.get? i = some (expectedWaterAt heights i)))

end LLMSpec

section Proof

theorem precondition_equiv (heights : List (Int)) : VerinaSpec.rain_precond heights ↔ LLMSpec.precondition heights := by
  -- To prove the equivalence, we can split it into two implications.
  apply Iff.intro;
  · -- If all elements in the list are non-negative, then the list is non-negative.
    intro h_nonneg
    simp [VerinaSpec.rain_precond, LLMSpec.precondition] at h_nonneg ⊢
    aesop;
  · -- If the LLMSpec precondition holds, then for every index i, the height at that index is non-negative. This directly implies that the VerinaSpec rain_precond holds.
    intro h_precond
    simp [VerinaSpec.rain_precond, h_precond];
    -- By definition of `precondition`, if `precondition heights` holds, then for every index `i` in the list, the height at `i` is non-negative.
    intro x hx
    obtain ⟨i, hi⟩ : ∃ i, i < heights.length ∧ heights.get! i = x := by
      obtain ⟨ i, hi ⟩ := List.mem_iff_get.mp hx; use i; aesop;
    have := h_precond i hi.1; aesop;

theorem postcondition_equiv (heights : List (Int)) (result : Int) : LLMSpec.precondition heights →
  (VerinaSpec.rain_postcond heights result ↔ LLMSpec.postcondition heights result) := by
  -- By definition of `rain_postcond` and `postcondition`, we can split the implication into two parts: the sum of water is non-negative and the sum of water equals the result.
  intro h_pre
  simp [VerinaSpec.rain_postcond, LLMSpec.postcondition];
  -- By definition of `sum_water`, we know that it is equal to the sum of the water at each index.
  have h_sum_water : VerinaSpec.rain_postcond.sum_water heights (fun i => max 0 (min (VerinaSpec.rain_postcond.ml heights i 0 0) (VerinaSpec.rain_postcond.mr heights i 0) - heights[i]?.getD 0)) 0 0 = List.sum (List.map (fun i => max 0 (min (VerinaSpec.rain_postcond.ml heights i 0 0) (VerinaSpec.rain_postcond.mr heights i 0) - heights[i]?.getD 0)) (List.range heights.length)) := by
    have h_sum_water : ∀ (i : Nat) (acc : Int), VerinaSpec.rain_postcond.sum_water heights (fun i => max 0 (min (VerinaSpec.rain_postcond.ml heights i 0 0) (VerinaSpec.rain_postcond.mr heights i 0) - heights[i]?.getD 0)) i acc = List.sum (List.map (fun j => max 0 (min (VerinaSpec.rain_postcond.ml heights j 0 0) (VerinaSpec.rain_postcond.mr heights j 0) - heights[j]?.getD 0)) (List.range (heights.length) |>.drop i)) + acc := by
      intro i acc; induction' h : heights.length - i with k hk generalizing i acc <;> simp_all +decide [ Nat.sub_succ ] ;
      · -- Since `heights.length - i = 0`, we have `i ≥ heights.length`, which means `sum_water` returns `acc`.
        have h_sum_zero : VerinaSpec.rain_postcond.sum_water heights (fun i => max 0 (min (VerinaSpec.rain_postcond.ml heights i 0 0) (VerinaSpec.rain_postcond.mr heights i 0) - heights[i]?.getD 0)) i acc = acc := by
          -- Since `i ≥ heights.length`, the sum_water function returns `acc` by definition.
          have h_sum_zero : i ≥ heights.length := by
            omega;
          unfold VerinaSpec.rain_postcond.sum_water; aesop;
        rw [ h_sum_zero, List.drop_eq_nil_of_le ] <;> norm_num ; omega;
      · unfold VerinaSpec.rain_postcond.sum_water; simp +decide [ h, hk ] ;
        split_ifs <;> simp_all +decide [ Nat.sub_succ ];
        ring;
    aesop;
  -- By definition of `expectedWaterAt`, we know that it is equal to the water at each index.
  have h_expected_water : ∀ i < heights.length, max 0 (min (VerinaSpec.rain_postcond.ml heights i 0 0) (VerinaSpec.rain_postcond.mr heights i 0) - heights[i]?.getD 0) = LLMSpec.expectedWaterAt heights i := by
    -- By definition of `ml` and `mr`, we know that they compute the same values as `leftMaxUpTo` and `rightMaxFrom`.
    have h_ml_mr : ∀ i < heights.length, VerinaSpec.rain_postcond.ml heights i 0 0 = LLMSpec.leftMaxUpTo heights i ∧ VerinaSpec.rain_postcond.mr heights i 0 = LLMSpec.rightMaxFrom heights i := by
      intro i hi
      constructor
      ·
        -- By definition of `ml`, we know that it computes the maximum height seen from the left up to index `i`.
        have h_ml_eq : ∀ (j : ℕ) (max_so_far : ℤ), j ≤ i → VerinaSpec.rain_postcond.ml heights i j max_so_far = List.foldl max max_so_far (List.take (i + 1) heights |>.drop j) := by
          intros j max_so_far hj
          induction' h : i - j with k hk generalizing j max_so_far;
          · -- Since $j = i$, we have $i + 1 = j + 1$, so the drop of $j$ from the take of $(j + 1)$ heights is just the list up to $j$.
            have h_drop_take : List.drop j (List.take (j + 1) heights) = List.take 1 (List.drop j heights) := by
              exact?;
            simp_all +decide [ Nat.sub_eq_iff_eq_add hj ];
            -- Since $j = i$, the drop of $j$ from the take of $(j + 1)$ heights is just the list up to $j$, and the foldl of max over this list is the maximum of the elements up to $j$.
            simp [VerinaSpec.rain_postcond.ml];
            rw [ List.take_succ ] ; aesop;
          · unfold VerinaSpec.rain_postcond.ml;
            rw [ List.drop_eq_getElem_cons ];
            grind;
            rw [ List.length_take ] ; omega;
        unfold LLMSpec.leftMaxUpTo; aesop;
      ·
        -- By definition of `mr`, we know that it is equal to `rightMaxFrom`.
        have h_mr_eq : ∀ (j : ℕ) (max_so_far : ℤ), j ≤ heights.length → VerinaSpec.rain_postcond.mr heights j max_so_far = List.foldl max max_so_far (heights.drop j) := by
          intros j max_so_far hj
          induction' h : heights.length - j with k ih generalizing j max_so_far;
          · -- Since $j = \text{length}(heights)$, we have $j \geq \text{length}(heights)$, and thus $\text{mr}(heights, j, max_so_far) = max_so_far$.
            have h_mr_eq : j = heights.length := by
              omega;
            unfold VerinaSpec.rain_postcond.mr; aesop;
          · unfold VerinaSpec.rain_postcond.mr;
            rw [ List.drop_eq_getElem_cons ];
            grind;
            omega;
        exact h_mr_eq i 0 hi.le;
    unfold LLMSpec.expectedWaterAt; aesop;
  split_ifs <;> simp_all +decide [ List.sum_eq_zero_iff ];
  · rcases heights with ( _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | heights ⟩ ⟩ ⟩ ) <;> simp_all +decide;
    · exact fun _ => eq_comm.symm;
    · -- Since the list [a] has only one element, the expectedWaterAt is 0.
      have h_expected_water_zero : LLMSpec.expectedWaterAt [a] 0 = 0 := by
        unfold LLMSpec.expectedWaterAt; simp +decide ;
        unfold LLMSpec.leftMaxUpTo LLMSpec.rightMaxFrom; simp +decide ;
        exact h_pre 0 ( by simp +decide ) |> fun h => by simpa using h;
      -- If result is zero, then the water list must be [0], which satisfies the conditions.
      intro h_nonneg
      constructor
      intro h_eq_zero
      use [0]
      simp [h_eq_zero, h_expected_water_zero];
      rintro ⟨ water, hw₁, hw₂, hw₃ ⟩ ; rcases water with ( _ | ⟨ x, _ | ⟨ y, _ | water ⟩ ⟩ ) <;> aesop;
    · -- If result is 0, then the water list must be [0, 0] because the sum is 0 and each element is non-negative.
      intro h_nonneg
      constructor
      intro h_eq_zero
      use [0, 0]
      simp [h_eq_zero];
      · intro i hi; interval_cases i <;> simp +decide [ LLMSpec.expectedWaterAt ] ;
        · unfold LLMSpec.leftMaxUpTo LLMSpec.rightMaxFrom; simp +decide ;
          exact Or.inl ( h_pre 0 ( by norm_num ) );
        · unfold LLMSpec.leftMaxUpTo LLMSpec.rightMaxFrom; simp +decide ;
          exact Or.inr ( h_pre 1 ( by simp +decide ) );
      · rintro ⟨ water, hw₁, hw₂, hw₃ ⟩ ; rcases water with ( _ | ⟨ x, _ | ⟨ y, _ | water ⟩ ⟩ ) <;> simp_all +decide ;
        -- Since $x$ and $y$ are both zero, their sum $x + y$ is also zero.
        have hx_zero : x = 0 := by
          -- Since $ LLMSpec.expectedWaterAt [a, b] 0 $ is defined as $ max 0 (min (leftMaxUpTo [a, b] 0) (rightMaxFrom [a, b] 0) - a) $, and given that $ leftMaxUpTo [a, b] 0 = a $ and $ rightMaxFrom [a, b] 0 = max(a, b) $, we have:
          have hx_zero : LLMSpec.expectedWaterAt [a, b] 0 = max 0 (min a (max a b) - a) := by
            unfold LLMSpec.expectedWaterAt; simp +decide [ List.take, List.drop ] ;
            unfold LLMSpec.leftMaxUpTo LLMSpec.rightMaxFrom; simp +decide ;
            exact Or.inl ( h_pre 0 ( by norm_num ) );
          specialize hw₃ 0 ; aesop
        have hy_zero : y = 0 := by
          specialize hw₃ 1 ; simp_all +decide [ LLMSpec.expectedWaterAt ];
          unfold LLMSpec.leftMaxUpTo LLMSpec.rightMaxFrom; simp +decide ;
          exact Or.inr ( h_pre 1 ( by simp +decide ) )
        rw [hx_zero, hy_zero] at hw₂
        simp at hw₂
        exact hw₂.symm;
    · linarith;
  · intro h_nonneg
    constructor
    intro h_eq
    use List.map (fun i => max 0 (min (VerinaSpec.rain_postcond.ml heights i 0 0) (VerinaSpec.rain_postcond.mr heights i 0) - heights[i]?.getD 0)) (List.range heights.length);
    · grind;
    · rintro ⟨ water, hw₁, hw₂, hw₃ ⟩;
      rw [ ← hw₂, ← hw₁ ];
      refine' congr_arg _ ( List.ext_get _ _ ) <;> aesop

end Proof