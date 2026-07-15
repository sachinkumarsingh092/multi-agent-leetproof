import Lean
import Mathlib.Tactic
import Velvet.Std
import Extensions.VelvetPBT

set_option maxHeartbeats 10000000

section Specs
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false
set_option pp.funBinderTypes true

/- Problem Description
    2149. Rearrange Array Elements by Sign: Rearrange an even-length integer array with equal numbers of positive and negative elements so that signs alternate starting with a positive, while preserving relative order within each sign.
    **Important: complexity should be O(n) time and O(n) space**
    Natural language breakdown:
    1. The input is a 0-indexed array of integers of even length.
    2. Every element is either strictly positive or strictly negative (no zeros).
    3. The number of positive elements equals the number of negative elements.
    4. The output is an array of the same length that is a rearrangement (permutation) of the input.
    5. The output starts with a positive element when the array is nonempty.
    6. Consecutive elements in the output have opposite signs (equivalently, indices with even parity are positive and odd parity are negative).
    7. Among all positives (respectively negatives), their relative order in the output is the same as in the input (stable with respect to sign).
-/

-- Helper predicates as Bool for use with Array.filter/countP.
def isPosB (x : Int) : Bool := decide (x > 0)
def isNegB (x : Int) : Bool := decide (x < 0)

def countPos (nums : Array Int) : Nat := nums.countP isPosB

def countNeg (nums : Array Int) : Nat := nums.countP isNegB

def allNonZero (nums : Array Int) : Prop :=
  ∀ (i : Nat), i < nums.size → nums[i]! ≠ 0

-- Parity-based sign pattern for the desired result.
def alternatesStartingPos (arr : Array Int) : Prop :=
  ∀ (i : Nat), i < arr.size →
    ((i % 2 = 0) → arr[i]! > 0) ∧
    ((i % 2 = 1) → arr[i]! < 0)

-- Stable order within sign can be characterized by equality of the sign-filtered subsequences.
def stableBySign (nums : Array Int) (result : Array Int) : Prop :=
  result.filter isPosB = nums.filter isPosB ∧
  result.filter isNegB = nums.filter isNegB

-- Preconditions: even length, no zeros, equal number of positives and negatives.
def precondition (nums : Array Int) : Prop :=
  nums.size % 2 = 0 ∧
  allNonZero nums ∧
  countPos nums = nums.size / 2 ∧
  countNeg nums = nums.size / 2

-- Postconditions: permutation, correct alternating sign pattern, starts with positive if nonempty,
-- and stability of relative order within each sign.
def postcondition (nums : Array Int) (result : Array Int) : Prop :=
  result.size = nums.size ∧
  result.Perm nums ∧
  alternatesStartingPos result ∧
  (result.size > 0 → result[0]! > 0) ∧
  stableBySign nums result
end Specs

section Impl
def implementation (nums : Array Int) : Array Int :=
  let pos := nums.filter (fun x => decide (x > 0))
  let neg := nums.filter (fun x => decide (x < 0))
  let n := pos.size
  let rec go (i : Nat) (acc : Array Int) (fuel : Nat) : Array Int :=
    match fuel with
    | 0 => acc
    | fuel' + 1 =>
      if i < n then
        let acc := acc.push pos[i]!
        let acc := acc.push neg[i]!
        go (i + 1) acc fuel'
      else
        acc
  go 0 (Array.mkEmpty (nums.size)) n
end Impl

section TestCases
-- Test case 1: Example 1
-- Input: [3,1,-2,-5,2,-4]
-- Output: [3,-2,1,-5,2,-4]
def test1_nums : Array Int := #[3, 1, -2, -5, 2, -4]
def test1_Expected : Array Int := #[3, -2, 1, -5, 2, -4]

-- Test case 2: Example 2 (starts with a negative in input)
def test2_nums : Array Int := #[-1, 1]
def test2_Expected : Array Int := #[1, -1]

-- Test case 3: Empty array (degenerate but satisfies even length and equal counts)
def test3_nums : Array Int := #[]
def test3_Expected : Array Int := #[]

-- Test case 4: Smallest nontrivial already-correct alternating order
def test4_nums : Array Int := #[1, -1]
def test4_Expected : Array Int := #[1, -1]

-- Test case 5: Larger array where positives/negatives are grouped
-- Positives: [1,2,3], Negatives: [-1,-2,-3]
def test5_nums : Array Int := #[1, 2, 3, -1, -2, -3]
def test5_Expected : Array Int := #[1, -1, 2, -2, 3, -3]

-- Test case 6: Alternating input but begins with negative; must start with positive in output
-- Positives: [5,6], Negatives: [-5,-6]
def test6_nums : Array Int := #[-5, 5, -6, 6]
def test6_Expected : Array Int := #[5, -5, 6, -6]

-- Test case 7: Mixed order; checks stability within each sign
-- Positives in input: [2,4,6,8], Negatives: [-1,-3,-5,-7]
def test7_nums : Array Int := #[2, -1, 4, -3, 6, -5, 8, -7]
def test7_Expected : Array Int := #[2, -1, 4, -3, 6, -5, 8, -7]

-- Test case 8: All positives first but with different magnitudes; confirms stable order
-- Positives: [10,1,7], Negatives: [-2,-9,-3]
def test8_nums : Array Int := #[10, 1, 7, -2, -9, -3]
def test8_Expected : Array Int := #[10, -2, 1, -9, 7, -3]
end TestCases

section Assertions
-- Test case 1
#assert_same_evaluation #[(implementation test1_nums), test1_Expected]

-- Test case 2
#assert_same_evaluation #[(implementation test2_nums), test2_Expected]

-- Test case 3
#assert_same_evaluation #[(implementation test3_nums), test3_Expected]

-- Test case 4
#assert_same_evaluation #[(implementation test4_nums), test4_Expected]

-- Test case 5
#assert_same_evaluation #[(implementation test5_nums), test5_Expected]

-- Test case 6
#assert_same_evaluation #[(implementation test6_nums), test6_Expected]

-- Test case 7
#assert_same_evaluation #[(implementation test7_nums), test7_Expected]

-- Test case 8
#assert_same_evaluation #[(implementation test8_nums), test8_Expected]
end Assertions

section Pbt
method implementationPbt (nums : Array Int)
  return (result : Array Int)
  require precondition nums
  ensures postcondition nums result
  do
  return (implementation nums)

velvet_plausible_test implementationPbt (config := { maxMs := some 20000 })
end Pbt

section Proof
theorem correctness_goal_0_0 : ∀ (pos neg : Array ℤ) (i : ℕ) (acc : Array ℤ) (fuel : ℕ),
  fuel = pos.size - i →
    i ≤ pos.size →
      pos.size = neg.size →
        (implementation.go pos neg pos.size i acc fuel).toList =
          acc.toList ++ List.flatMap (fun p => [p.1, p.2]) ((List.drop i pos.toList).zip (List.drop i neg.toList)) := by
    intro pos neg i acc fuel
    induction fuel generalizing i acc with
    | zero =>
      intro hfuel hi hsz
      unfold implementation.go
      have heq : i = pos.size := by omega
      subst heq
      have h1 : List.drop pos.size pos.toList = [] := by
        rw [List.drop_of_length_le]; simp [Array.length_toList]
      rw [h1, List.zip_nil_left, List.flatMap_nil, List.append_nil]
    | succ fuel' ih =>
      intro hfuel hi hsz
      unfold implementation.go
      split
      · rename_i hlt
        have hip : i < pos.toList.length := by rw [Array.length_toList]; exact hlt
        have hin : i < neg.toList.length := by rw [Array.length_toList]; omega
        have hlt' : i < neg.size := by omega
        have hrec := ih (i + 1) ((acc.push pos[i]!).push neg[i]!) (by omega) (by omega) hsz
        rw [hrec]
        rw [Array.push_toList, Array.push_toList]
        have hpi : pos[i]! = pos.toList[i] := by
          rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
              Array.getElem?_eq_getElem hlt, Option.getD_some,
              ← Array.getElem_toList hlt]
        have hni : neg[i]! = neg.toList[i] := by
          rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
              Array.getElem?_eq_getElem hlt', Option.getD_some,
              ← Array.getElem_toList hlt']
        rw [hpi, hni]
        rw [List.drop_eq_getElem_cons hip, List.drop_eq_getElem_cons hin]
        simp only [List.zip_cons_cons, List.flatMap_cons]
        simp only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append]
      · rename_i hlt
        have heq : i = pos.size := by omega
        subst heq
        have h1 : List.drop pos.size pos.toList = [] := by
          rw [List.drop_of_length_le]; simp [Array.length_toList]
        rw [h1, List.zip_nil_left, List.flatMap_nil, List.append_nil]

theorem correctness_goal_0
    (nums : Array ℤ)
    (h_even : nums.size % 2 = 0)
    (h_countpos : countPos nums = nums.size / 2)
    (h_countneg : countNeg nums = nums.size / 2)
    (h_pos_isPosB : (fun x => decide (x > 0)) = isPosB)
    (h_neg_isNegB : (fun x => decide (x < 0)) = isNegB)
    (h_pos_size : (Array.filter isPosB nums).size = nums.size / 2)
    (h_neg_size : (Array.filter isNegB nums).size = nums.size / 2)
    (h_pos_neg_size : (Array.filter isPosB nums).size = (Array.filter isNegB nums).size)
    : (implementation nums).toList =
  List.flatMap (fun p => [p.1, p.2]) ((Array.filter isPosB nums).toList.zip (Array.filter isNegB nums).toList) := by
    have h_go : ∀ (pos neg : Array ℤ) (i : Nat) (acc : Array ℤ) (fuel : Nat),
      fuel = pos.size - i → i ≤ pos.size → pos.size = neg.size →
      (implementation.go pos neg pos.size i acc fuel).toList =
      acc.toList ++ List.flatMap (fun p => [p.1, p.2]) ((pos.toList.drop i).zip (neg.toList.drop i)) := by
      expose_names; exact (correctness_goal_0_0)
    unfold implementation
    simp only [h_pos_isPosB, h_neg_isNegB]
    have hps : (Array.filter isPosB nums).size = (Array.filter isNegB nums).size := h_pos_neg_size
    rw [h_go (Array.filter isPosB nums) (Array.filter isNegB nums) 0 (Array.mkEmpty nums.size) (Array.filter isPosB nums).size (by omega) (by omega) hps]
    simp [Array.mkEmpty_eq, Array.toList_empty, List.drop]

theorem correctness_goal_1
    (nums : Array ℤ)
    (h_even : nums.size % 2 = 0)
    (h_countpos : countPos nums = nums.size / 2)
    (h_countneg : countNeg nums = nums.size / 2)
    (h_pos_size : (Array.filter isPosB nums).size = nums.size / 2)
    (h_neg_size : (Array.filter isNegB nums).size = nums.size / 2)
    (h_pos_neg_size : (Array.filter isPosB nums).size = (Array.filter isNegB nums).size)
    (h_go_toList : (implementation nums).toList =
  List.flatMap (fun p => [p.1, p.2]) ((Array.filter isPosB nums).toList.zip (Array.filter isNegB nums).toList))
    : (implementation nums).size = nums.size := by
    have h1 : (implementation nums).toList.length = nums.size := by
      rw [h_go_toList, List.length_flatMap]
      have hmapeq : (List.map (fun a => [a.1, a.2].length)
            ((Array.filter isPosB nums).toList.zip (Array.filter isNegB nums).toList))
          = List.replicate ((Array.filter isPosB nums).toList.zip (Array.filter isNegB nums).toList).length 2 := by
        apply List.ext_getElem
        · simp [List.length_replicate]
        · intro n h1 h2
          simp [List.getElem_replicate]
      rw [hmapeq, List.sum_replicate, smul_eq_mul, List.length_zip,
          Array.length_toList, Array.length_toList, h_pos_neg_size, Nat.min_self]
      omega
    rw [Array.size_eq_length_toList]
    exact h1

theorem correctness_goal_2_0 : ∀ (l1 l2 : List ℤ), l1.length = l2.length → (List.flatMap (fun p => [p.1, p.2]) (l1.zip l2)).Perm (l1 ++ l2) := by
    intro l1
    induction l1 with
    | nil =>
      intro l2 h
      simp at h
      have : l2 = [] := List.length_eq_zero.mp (h.symm)
      subst this
      simp
    | cons a l1' ih =>
      intro l2 h
      cases l2 with
      | nil => simp at h
      | cons b l2' =>
        simp [List.length_cons] at h
        simp only [List.zip_cons_cons, List.flatMap_cons, List.cons_append]
        have ih' := ih l2' h
        apply List.Perm.cons
        exact (ih'.cons b).trans (List.perm_cons_append_cons b (List.Perm.refl _))

theorem correctness_goal_2_1
    (nums : Array ℤ)
    (h_nonzero : allNonZero nums)
    : List.filter isNegB nums.toList = List.filter (fun x => !isPosB x) nums.toList := by
    apply List.filter_congr
    intro x hx
    rw [List.mem_iff_getElem] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    have hi' : i < nums.size := by rwa [Array.size_eq_length_toList]
    rw [Array.getElem_toList hi']
    have hne : nums[i] ≠ 0 := by
      have := h_nonzero i hi'
      rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi'] at this
      simpa using this
    simp only [isNegB, isPosB]
    by_cases hpos : nums[i] > 0
    · simp [hpos, Int.not_lt.mpr (Int.le_of_lt hpos)]
    · have hlt : nums[i] < 0 := by omega
      simp [hpos, hlt]

theorem correctness_goal_2
    (nums : Array ℤ)
    (h_nonzero : allNonZero nums)
    (h_pos_neg_size : (Array.filter isPosB nums).size = (Array.filter isNegB nums).size)
    (h_go_toList : (implementation nums).toList =
  List.flatMap (fun p => [p.1, p.2]) ((Array.filter isPosB nums).toList.zip (Array.filter isNegB nums).toList))
    : (implementation nums).Perm nums := by
    rw [Array.perm_iff_toList_perm]
    rw [h_go_toList]
    -- Step 1: flatMap over zip is perm of pos ++ neg (for equal length lists)
    have h_zip_perm : ∀ (l1 l2 : List ℤ), l1.length = l2.length →
      List.Perm (List.flatMap (fun p => [p.1, p.2]) (l1.zip l2)) (l1 ++ l2) := by expose_names; exact (correctness_goal_2_0)
    -- Step 2: isNegB = (fun x => !isPosB x) for nonzero elements, leading to filter equality
    have h_filter_neg_eq : nums.toList.filter isNegB = nums.toList.filter (fun x => !isPosB x) := by expose_names; exact (correctness_goal_2_1 nums h_nonzero)
    -- Now combine
    have h_len_eq : (Array.filter isPosB nums).toList.length = (Array.filter isNegB nums).toList.length := by
      rw [Array.length_toList, Array.length_toList]
      exact h_pos_neg_size
    have h1 := h_zip_perm _ _ h_len_eq
    apply List.Perm.trans h1
    rw [Array.toList_filter, Array.toList_filter]
    rw [h_filter_neg_eq]
    exact List.filter_append_perm isPosB nums.toList

theorem correctness_goal_3_0 : ∀ (l1 l2 : List ℤ) (k : ℕ),
  l1.length = l2.length → k < l1.length → (List.flatMap (fun p => [p.1, p.2]) (l1.zip l2))[2 * k]! = l1[k]! := by
    intro l1
    induction l1 with
    | nil =>
      intro l2 k hlen hk
      simp at hk
    | cons a l1' ih =>
      intro l2 k hlen hk
      cases l2 with
      | nil => simp at hlen
      | cons b l2' =>
        simp only [List.zip_cons_cons, List.flatMap_cons]
        simp only [List.length_cons] at hlen hk
        have hlen' : l1'.length = l2'.length := by omega
        cases k with
        | zero =>
          simp
        | succ k' =>
          have hk' : k' < l1'.length := by omega
          have ih' := ih l2' k' hlen' hk'
          rw [List.getElem!_cons_succ]
          -- Goal: ([a, b] ++ flatMap ...)[2 * (k' + 1)]! = l1'[k']!
          simp only [List.getElem!_eq_getElem?_getD] at ih' ⊢
          simp only [List.getElem?_append, show 2 * (k' + 1) = 2 + 2 * k' from by omega]
          have : ¬ (2 + 2 * k' < 1 + 1) := by omega
          simp [this]
          exact ih'

theorem correctness_goal_3_1
    (nums : Array ℤ)
    (h_even : nums.size % 2 = 0)
    (h_nonzero : allNonZero nums)
    (h_countpos : countPos nums = nums.size / 2)
    (h_countneg : countNeg nums = nums.size / 2)
    (h_pos_isPosB : (fun x => decide (x > 0)) = isPosB)
    (h_neg_isNegB : (fun x => decide (x < 0)) = isNegB)
    (h_pos_size : (Array.filter isPosB nums).size = nums.size / 2)
    (h_neg_size : (Array.filter isNegB nums).size = nums.size / 2)
    (h_pos_neg_size : (Array.filter isPosB nums).size = (Array.filter isNegB nums).size)
    (h_nums_size_eq : nums.size = 2 * (Array.filter isPosB nums).size)
    (h_go_toList : (implementation nums).toList =
  List.flatMap (fun p => [p.1, p.2]) ((Array.filter isPosB nums).toList.zip (Array.filter isNegB nums).toList))
    (h_size : (implementation nums).size = nums.size)
    (h_perm : (implementation nums).Perm nums)
    (h_interleave_even : ∀ (l1 l2 : List ℤ) (k : ℕ),
  l1.length = l2.length → k < l1.length → (List.flatMap (fun p => [p.1, p.2]) (l1.zip l2))[2 * k]! = l1[k]!)
    : ∀ (l1 l2 : List ℤ) (k : ℕ),
  l1.length = l2.length → k < l2.length → (List.flatMap (fun p => [p.1, p.2]) (l1.zip l2))[2 * k + 1]! = l2[k]! := by
    sorry

theorem correctness_goal_3
    (nums : Array ℤ)
    (h_even : nums.size % 2 = 0)
    (h_nonzero : allNonZero nums)
    (h_countpos : countPos nums = nums.size / 2)
    (h_countneg : countNeg nums = nums.size / 2)
    (h_pos_isPosB : (fun x => decide (x > 0)) = isPosB)
    (h_neg_isNegB : (fun x => decide (x < 0)) = isNegB)
    (h_pos_size : (Array.filter isPosB nums).size = nums.size / 2)
    (h_neg_size : (Array.filter isNegB nums).size = nums.size / 2)
    (h_pos_neg_size : (Array.filter isPosB nums).size = (Array.filter isNegB nums).size)
    (h_nums_size_eq : nums.size = 2 * (Array.filter isPosB nums).size)
    (h_go_toList : (implementation nums).toList =
  List.flatMap (fun p => [p.1, p.2]) ((Array.filter isPosB nums).toList.zip (Array.filter isNegB nums).toList))
    (h_size : (implementation nums).size = nums.size)
    (h_perm : (implementation nums).Perm nums)
    : alternatesStartingPos (implementation nums) := by
    have h_interleave_even : ∀ (l1 l2 : List ℤ) (k : Nat), l1.length = l2.length → k < l1.length →
      (List.flatMap (fun p => [p.1, p.2]) (l1.zip l2))[2 * k]! = l1[k]! := by expose_names; exact (correctness_goal_3_0)
    have h_interleave_odd : ∀ (l1 l2 : List ℤ) (k : Nat), l1.length = l2.length → k < l2.length →
      (List.flatMap (fun p => [p.1, p.2]) (l1.zip l2))[2 * k + 1]! = l2[k]! := by expose_names; exact (correctness_goal_3_1 nums h_even h_nonzero h_countpos h_countneg h_pos_isPosB h_neg_isNegB h_pos_size h_neg_size h_pos_neg_size h_nums_size_eq h_go_toList h_size h_perm h_interleave_even)
    have h_pos_all : ∀ (k : Nat), k < (Array.filter isPosB nums).toList.length → (Array.filter isPosB nums).toList[k]! > 0 := by expose_names; intros; expose_names; try ( simp at * ); try grind
    have h_neg_all : ∀ (k : Nat), k < (Array.filter isNegB nums).toList.length → (Array.filter isNegB nums).toList[k]! < 0 := by expose_names; intros; expose_names; try ( simp at * ); try grind
    have h_arr_list_getElem : ∀ (arr : Array ℤ) (j : Nat), arr[j]! = arr.toList[j]! := by expose_names; intros; expose_names; grind
    unfold alternatesStartingPos
    intro i hi
    have hlen_eq : (Array.filter isPosB nums).toList.length = (Array.filter isNegB nums).toList.length := by
      rw [Array.length_toList, Array.length_toList]; exact h_pos_neg_size
    have h_pos_len_eq : (Array.filter isPosB nums).toList.length = nums.size / 2 := by
      rw [Array.length_toList]; exact h_pos_size
    have h_neg_len_eq : (Array.filter isNegB nums).toList.length = nums.size / 2 := by
      rw [Array.length_toList]; exact h_neg_size
    constructor
    · intro heven
      have hk_eq : i = 2 * (i / 2) := by omega
      have hk_lt : i / 2 < (Array.filter isPosB nums).toList.length := by
        rw [h_pos_len_eq]; omega
      rw [h_arr_list_getElem, h_go_toList, hk_eq,
          h_interleave_even _ _ (i / 2) hlen_eq hk_lt]
      exact h_pos_all (i / 2) hk_lt
    · intro hodd
      have hk_eq : i = 2 * (i / 2) + 1 := by omega
      have hk_lt : i / 2 < (Array.filter isNegB nums).toList.length := by
        rw [h_neg_len_eq]; omega
      rw [h_arr_list_getElem, h_go_toList, hk_eq,
          h_interleave_odd _ _ (i / 2) hlen_eq hk_lt]
      exact h_neg_all (i / 2) hk_lt

theorem correctness_goal_4
    (nums : Array ℤ)
    (h_even : nums.size % 2 = 0)
    (h_nonzero : allNonZero nums)
    (h_countpos : countPos nums = nums.size / 2)
    (h_countneg : countNeg nums = nums.size / 2)
    (h_pos_isPosB : (fun x => decide (x > 0)) = isPosB)
    (h_neg_isNegB : (fun x => decide (x < 0)) = isNegB)
    (h_pos_size : (Array.filter isPosB nums).size = nums.size / 2)
    (h_neg_size : (Array.filter isNegB nums).size = nums.size / 2)
    (h_pos_neg_size : (Array.filter isPosB nums).size = (Array.filter isNegB nums).size)
    (h_nums_size_eq : nums.size = 2 * (Array.filter isPosB nums).size)
    (h_go_toList : (implementation nums).toList =
  List.flatMap (fun p => [p.1, p.2]) ((Array.filter isPosB nums).toList.zip (Array.filter isNegB nums).toList))
    (h_size : (implementation nums).size = nums.size)
    (h_perm : (implementation nums).Perm nums)
    (h_alt : alternatesStartingPos (implementation nums))
    : (implementation nums).size > 0 → (implementation nums)[0]! > 0 := by
    sorry


theorem correctness_goal_5
    (nums : Array ℤ)
    (h_even : nums.size % 2 = 0)
    (h_nonzero : allNonZero nums)
    (h_countpos : countPos nums = nums.size / 2)
    (h_countneg : countNeg nums = nums.size / 2)
    (h_pos_isPosB : (fun x => decide (x > 0)) = isPosB)
    (h_neg_isNegB : (fun x => decide (x < 0)) = isNegB)
    (h_pos_size : (Array.filter isPosB nums).size = nums.size / 2)
    (h_neg_size : (Array.filter isNegB nums).size = nums.size / 2)
    (h_pos_neg_size : (Array.filter isPosB nums).size = (Array.filter isNegB nums).size)
    (h_nums_size_eq : nums.size = 2 * (Array.filter isPosB nums).size)
    (h_go_toList : (implementation nums).toList =
  List.flatMap (fun p => [p.1, p.2]) ((Array.filter isPosB nums).toList.zip (Array.filter isNegB nums).toList))
    (h_size : (implementation nums).size = nums.size)
    (h_perm : (implementation nums).Perm nums)
    (h_alt : alternatesStartingPos (implementation nums))
    (h_start : (implementation nums).size > 0 → (implementation nums)[0]! > 0)
    : stableBySign nums (implementation nums) := by
    sorry


theorem correctness_goal
    (nums : Array Int)
    (h_precond : precondition nums)
    : postcondition nums (implementation nums) := by
    unfold precondition at h_precond
    obtain ⟨h_even, h_nonzero, h_countpos, h_countneg⟩ := h_precond
    have h_pos_isPosB : (fun x : Int => decide (x > 0)) = isPosB := by
      ext x; simp [isPosB]
    have h_neg_isNegB : (fun x : Int => decide (x < 0)) = isNegB := by
      ext x; simp [isNegB]
    have h_pos_size : (nums.filter isPosB).size = nums.size / 2 := by
      rw [← h_countpos]; unfold countPos; rw [Array.countP_eq_size_filter]
    have h_neg_size : (nums.filter isNegB).size = nums.size / 2 := by
      rw [← h_countneg]; unfold countNeg; rw [Array.countP_eq_size_filter]
    have h_pos_neg_size : (nums.filter isPosB).size = (nums.filter isNegB).size := by omega
    have h_nums_size_eq : nums.size = 2 * (nums.filter isPosB).size := by omega
    -- The result list characterization
    have h_go_toList : (implementation nums).toList =
      (List.zip (nums.filter isPosB).toList (nums.filter isNegB).toList).flatMap (fun p => [p.1, p.2]) := by expose_names; exact (correctness_goal_0 nums h_even h_countpos h_countneg h_pos_isPosB h_neg_isNegB h_pos_size h_neg_size h_pos_neg_size)
    -- Part 1: size
    have h_size : (implementation nums).size = nums.size := by expose_names; exact (correctness_goal_1 nums h_even h_countpos h_countneg h_pos_size h_neg_size h_pos_neg_size h_go_toList)
    -- Part 2: permutation
    have h_perm : (implementation nums).Perm nums := by expose_names; exact (correctness_goal_2 nums h_nonzero h_pos_neg_size h_go_toList)
    -- Part 3: alternating signs
    have h_alt : alternatesStartingPos (implementation nums) := by expose_names; exact (correctness_goal_3 nums h_even h_nonzero h_countpos h_countneg h_pos_isPosB h_neg_isNegB h_pos_size h_neg_size h_pos_neg_size h_nums_size_eq h_go_toList h_size h_perm)
    -- Part 4: starts positive
    have h_start : (implementation nums).size > 0 → (implementation nums)[0]! > 0 := by expose_names; exact (correctness_goal_4 nums h_even h_nonzero h_countpos h_countneg h_pos_isPosB h_neg_isNegB h_pos_size h_neg_size h_pos_neg_size h_nums_size_eq h_go_toList h_size h_perm h_alt)
    -- Part 5: stable by sign
    have h_stable : stableBySign nums (implementation nums) := by expose_names; exact (correctness_goal_5 nums h_even h_nonzero h_countpos h_countneg h_pos_isPosB h_neg_isNegB h_pos_size h_neg_size h_pos_neg_size h_nums_size_eq h_go_toList h_size h_perm h_alt h_start)
    unfold postcondition
    exact ⟨h_size, h_perm, h_alt, h_start, h_stable⟩
end Proof
