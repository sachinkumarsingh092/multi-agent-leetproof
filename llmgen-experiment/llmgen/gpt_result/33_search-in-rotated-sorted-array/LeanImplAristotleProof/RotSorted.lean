import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1600000

def sa_sortedR (arr : Array ℤ) (lo hi : Nat) : Prop :=
  ∀ i j, lo ≤ i → i < j → j < hi → arr[i]! < arr[j]!

def sa_rot_sortedR (arr : Array ℤ) (lo hi : Nat) : Prop :=
  sa_sortedR arr lo hi ∨
  (∃ q, lo < q ∧ q < hi ∧ sa_sortedR arr lo q ∧ sa_sortedR arr q hi ∧ arr[hi-1]! < arr[lo]!)

private lemma arr_eq (nums : List ℤ) (i : Nat) (hi : i < nums.length) :
    nums.toArray[i]! = nums[i] := by
  simp [getElem!_def, List.getElem?_eq_getElem hi]

lemma sorted_list_sa_sorted (nums : List ℤ) (h : nums.Sorted (· < ·)) :
    sa_sortedR nums.toArray 0 nums.toArray.size := by
  intro i j _ hij hjn; simp at hjn
  rw [arr_eq nums i (by omega), arr_eq nums j hjn]
  exact h.rel_get_of_lt hij

-- Key helper: drop k of sorted list is sorted
-- take k of sorted list is sorted
-- These should be in Mathlib

-- The main lemma: rotation of sorted → sa_rot_sortedR
-- We prove: if nums = base.drop k' ++ base.take k' where base is sorted,
-- then nums.toArray is sa_rot_sortedR.
lemma drop_take_sorted_to_rot (base : List ℤ) (k' : Nat)
    (h_sorted : base.Sorted (· < ·))
    (hk' : 0 < k') (hk'_lt : k' < base.length)
    (h_pos : base.length > 0) :
    let nums := base.drop k' ++ base.take k'
    sa_rot_sortedR nums.toArray 0 nums.toArray.size := by
  set nums := base.drop k' ++ base.take k'
  set n := base.length
  set q := n - k'
  have h_nums_len : nums.length = n := by simp
  right
  refine ⟨q, ?_, ?_, ?_, ?_, ?_⟩
  · -- 0 < q
    omega
  · -- q < nums.toArray.size
    simp [h_nums_len]; omega
  · -- sa_sortedR [0, q): these are base.drop k' = base[k'..n)
    intro i j _ hij hjq
    simp [h_nums_len] at hjq
    rw [arr_eq nums i (by omega), arr_eq nums j (by omega)]
    have hdrop_len : (base.drop k').length = q := by simp; omega
    have hi_lt : i < (base.drop k').length := by omega
    have hj_lt : j < (base.drop k').length := by omega
    show nums[i] < nums[j]
    -- nums[i] = (base.drop k' ++ base.take k')[i] = (base.drop k')[i] since i < drop length
    have : nums[i] = (base.drop k')[i] := by
      show (base.drop k' ++ base.take k')[i] = _
      exact List.getElem_append_left hi_lt
    have : nums[j] = (base.drop k')[j] := by
      show (base.drop k' ++ base.take k')[j] = _
      exact List.getElem_append_left hj_lt
    rw [‹nums[i] = _›, ‹nums[j] = _›]
    simp [List.getElem_drop']
    exact h_sorted.rel_get_of_lt (by omega)
  · -- sa_sortedR [q, n): these are base.take k' = base[0..k')
    intro i j hiq hij hjn
    simp [h_nums_len] at hjn hiq
    rw [arr_eq nums i (by omega), arr_eq nums j (by omega)]
    have hdrop_len : (base.drop k').length = q := by simp; omega
    have hi_ge : i ≥ (base.drop k').length := by omega
    have hj_ge : j ≥ (base.drop k').length := by omega
    show nums[i] < nums[j]
    have : nums[i] = (base.take k')[i - q] := by
      show (base.drop k' ++ base.take k')[i] = _
      rw [List.getElem_append_right hi_ge]; simp [hdrop_len]
    have : nums[j] = (base.take k')[j - q] := by
      show (base.drop k' ++ base.take k')[j] = _
      rw [List.getElem_append_right hj_ge]; simp [hdrop_len]
    rw [‹nums[i] = _›, ‹nums[j] = _›]
    simp [List.getElem_take']
    exact h_sorted.rel_get_of_lt (by omega)
  · -- arr[n-1] < arr[0]
    show nums.toArray[nums.toArray.size - 1]! < nums.toArray[0]!
    simp [h_nums_len]
    rw [arr_eq nums (n - 1) (by omega), arr_eq nums 0 (by omega)]
    show nums[n - 1] < nums[0]
    -- nums[0] = (base.drop k')[0] = base[k']
    have h0 : nums[0] = base[k'] := by
      show (base.drop k' ++ base.take k')[0] = _
      rw [List.getElem_append_left (by simp; omega)]
      simp [List.getElem_drop']
    -- nums[n-1] = (base.take k')[k'-1] = base[k'-1]
    have hlast : nums[n - 1] = base[k' - 1] := by
      show (base.drop k' ++ base.take k')[n - 1] = _
      rw [List.getElem_append_right (by simp; omega)]
      simp [List.length_drop]
      show (base.take k')[n - 1 - (n - k')] = _
      rw [show n - 1 - (n - k') = k' - 1 from by omega]
      simp [List.getElem_take']
    rw [h0, hlast]
    exact h_sorted.rel_get_of_lt (by omega)

-- Full rotation lemma
lemma rot_sorted_list_to_sa (nums : List ℤ) (base : List ℤ) (k : Nat)
    (h_sorted : base.Sorted (· < ·)) (h_rot : base.rotate k = nums)
    (h_len_pos : nums.length > 0) :
    sa_rot_sortedR nums.toArray 0 nums.toArray.size := by
  have hn : base.length = nums.length := by rw [← h_rot]; simp
  have hbase_pos : base.length > 0 := by omega
  set k' := k % base.length
  have hk'_lt : k' < base.length := Nat.mod_lt k hbase_pos
  have h_rot' : base.rotate k' = nums := by rw [← List.rotate_mod]; exact h_rot
  by_cases hk' : k' = 0
  · -- trivial rotation
    have : base = nums := by rw [← h_rot']; simp [hk']
    subst this; left; exact sorted_list_sa_sorted base h_sorted
  · -- non-trivial rotation
    have h_eq : nums = base.drop k' ++ base.take k' := by
      rw [← h_rot']; exact List.rotate_eq_drop_append_take (le_of_lt hk'_lt)
    rw [h_eq]
    exact drop_take_sorted_to_rot base k' h_sorted (by omega) hk'_lt hbase_pos
