import Lean
import Mathlib.Tactic
import Proof2

set_option maxHeartbeats 400000

-- Same as implementation from main file
def origImpl (nums : List Int) (target : Int) : Int :=
  let arr : Array Int := nums.toArray
  let n : Nat := arr.size
  let rec bs (lo hi : Nat) : Int :=
    if h : lo < hi then
      let mid : Nat := lo + (hi - lo) / 2
      let midVal : Int := arr[mid]!
      if midVal = target then
        Int.ofNat mid
      else
        let loVal : Int := arr[lo]!
        if loVal ≤ midVal then
          if loVal ≤ target ∧ target < midVal then
            bs lo mid
          else
            bs (mid + 1) hi
        else
          let hiVal : Int := arr[hi - 1]!
          if midVal < target ∧ target ≤ hiVal then
            bs (mid + 1) hi
          else
            bs lo mid
    else
      (-1)
  bs 0 n

-- Top-level version for reasoning
def myBs (target : ℤ) (arr : Array ℤ) (lo hi : Nat) : ℤ :=
  if h : lo < hi then
    let mid : Nat := lo + (hi - lo) / 2
    let midVal : ℤ := arr[mid]!
    if midVal = target then
      Int.ofNat mid
    else
      let loVal : ℤ := arr[lo]!
      if loVal ≤ midVal then
        if loVal ≤ target ∧ target < midVal then
          myBs target arr lo mid
        else
          myBs target arr (mid + 1) hi
      else
        let hiVal : ℤ := arr[hi - 1]!
        if midVal < target ∧ target ≤ hiVal then
          myBs target arr (mid + 1) hi
        else
          myBs target arr lo mid
  else
    (-1)
termination_by hi - lo

lemma myBs_finds_target (target : ℤ) (arr : Array ℤ) (lo hi : Nat) (k : Nat) :
    myBs target arr lo hi = Int.ofNat k → arr[k]! = target := by
  revert k; intro k hk
  induction' n : hi - lo using Nat.strong_induction_on with n ih generalizing lo hi k
  unfold myBs at hk; grind

set_option maxHeartbeats 1600000 in
lemma myBs_range (target : ℤ) (arr : Array ℤ) (lo hi : Nat) (k : Nat) :
    myBs target arr lo hi = Int.ofNat k → lo ≤ k ∧ k < hi := by
  intro h_eq_k
  induction' n : hi - lo using Nat.strong_induction_on with n ih generalizing lo hi k
  unfold myBs at h_eq_k
  split_ifs at h_eq_k ; norm_num at h_eq_k
  split_ifs at h_eq_k <;> norm_cast at *
  · omega
  · specialize ih (lo + (hi - lo) / 2 - lo) ?_ lo (lo + (hi - lo) / 2) k h_eq_k ?_ <;> norm_num at * <;> omega
  · specialize ih (hi - (lo + (hi - lo) / 2 + 1)) ?_ (lo + (hi - lo) / 2 + 1) hi k h_eq_k ?_ <;> omega
  · grind
  · specialize ih (lo + (hi - lo) / 2 - lo) ?_ lo (lo + (hi - lo) / 2) k h_eq_k rfl <;> norm_num at * <;> first | grind | omega

set_option maxHeartbeats 800000 in
lemma bs_eq_myBs (target : ℤ) (arr : Array ℤ) (lo hi : Nat) :
    origImpl.bs target arr lo hi = myBs target arr lo hi := by
  induction' n : hi - lo using Nat.strong_induction_on with n ih generalizing lo hi
  unfold origImpl.bs myBs; split_ifs <;> norm_num at *
  rw [ih _ _ _ _ rfl, ih _ _ _ _ rfl] <;> omega

-- origImpl unfolds to origImpl.bs
lemma origImpl_unfold (nums : List ℤ) (target : ℤ) :
    origImpl nums target = origImpl.bs target nums.toArray 0 nums.toArray.size := rfl

-- Combined soundness: if origImpl returns Int.ofNat k, then k < length and nums[k]? = some target
lemma origImpl_finds_target (nums : List ℤ) (target : ℤ) (k : Nat) :
    origImpl nums target = Int.ofNat k →
    k < nums.length ∧ nums[k]? = some target := by
  rw [origImpl_unfold] at *; intro h
  have hfind := myBs_finds_target target nums.toArray 0 nums.toArray.size k (by rw [← h, bs_eq_myBs])
  have hrange := myBs_range target nums.toArray 0 nums.toArray.size k (by rw [← bs_eq_myBs, h])
  aesop

-- Uniqueness of index in nodup list
lemma nodup_unique_idx (nums : List ℤ) (target : ℤ) (h_nodup : nums.Nodup)
    (i j : Nat) (hi : i < nums.length) (hj : j < nums.length)
    (hti : nums.get? i = some target) (htj : nums.get? j = some target) : i = j := by
  have hti' : nums[i] = target := by have := List.getElem?_eq_getElem hi; simp_all
  have htj' : nums[j] = target := by have := List.getElem?_eq_getElem hj; simp_all
  exact (h_nodup.getElem_inj_iff).mp (by rw [hti', htj'])

-- Sub-array properties
def sa_sorted (arr : Array ℤ) (lo hi : Nat) : Prop :=
  ∀ i j, lo ≤ i → i < j → j < hi → arr[i]! < arr[j]!

def sa_nodup (arr : Array ℤ) (lo hi : Nat) : Prop :=
  ∀ i j, lo ≤ i → i < hi → lo ≤ j → j < hi → arr[i]! = arr[j]! → i = j

def sa_rot_sorted (arr : Array ℤ) (lo hi : Nat) : Prop :=
  sa_sorted arr lo hi ∨
  (∃ q, lo < q ∧ q < hi ∧ sa_sorted arr lo q ∧ sa_sorted arr q hi ∧ arr[hi-1]! < arr[lo]!)

-- Completeness (proved in Proof2.lean, restated here)
-- We need: if arr[p]! = target and sub-array is rot_sorted/nodup, myBs finds p
set_option maxHeartbeats 800000 in
lemma myBs_eq_myBs2 (target : ℤ) (arr : Array ℤ) (lo hi : Nat) :
    myBs target arr lo hi = myBs2 target arr lo hi := by
  induction' n : hi - lo using Nat.strong_induction_on with n ih generalizing lo hi
  unfold myBs myBs2; split_ifs <;> norm_num at *
  rw [ih _ _ _ _ rfl, ih _ _ _ _ rfl] <;> omega

set_option maxHeartbeats 3200000 in
lemma myBs_complete (target : ℤ) (arr : Array ℤ) (lo hi p : Nat)
    (hhi : hi ≤ arr.size)
    (hnodup : sa_nodup arr lo hi)
    (hrot : sa_rot_sorted arr lo hi)
    (hp : lo ≤ p ∧ p < hi)
    (htarget : arr[p]! = target) :
    myBs target arr lo hi = Int.ofNat p := by
  rw [myBs_eq_myBs2]
  exact myBs2_complete target arr lo hi p hhi hnodup hrot hp htarget

-- Now we need to connect List.Nodup and isRotationOfStrictSorted to sa_nodup/sa_rot_sorted

def isStrictSorted' (nums : List Int) : Prop := nums.Sorted (· < ·)

def isRotationOfStrictSorted' (nums : List Int) : Prop :=
  ∃ base : List Int, isStrictSorted' base ∧ base.Nodup ∧ base.IsRotated nums

def inList' (nums : List Int) (x : Int) : Prop := x ∈ nums

-- Nodup list → sa_nodup on its array
lemma list_nodup_to_sa_nodup (nums : List ℤ) (h_nodup : nums.Nodup) :
    sa_nodup nums.toArray 0 nums.toArray.size := by
  intro i j _ hi _ hj heq
  simp at hi hj
  have h1 : nums.toArray[i]! = nums[i] := by simp [getElem!_def, List.getElem?_eq_getElem hi]
  have h2 : nums.toArray[j]! = nums[j] := by simp [getElem!_def, List.getElem?_eq_getElem hj]
  exact h_nodup.getElem_inj_iff.mp (by rw [← h1, ← h2]; exact heq)

-- isRotationOfStrictSorted → sa_rot_sorted on its array
lemma list_rot_sorted_to_sa_rot_sorted (nums : List ℤ)
    (h_rot : isRotationOfStrictSorted' nums) (h_nodup : nums.Nodup) :
    sa_rot_sorted nums.toArray 0 nums.toArray.size := by
  sorry

-- target ∈ nums → ∃ p, p < length ∧ arr[p]! = target
lemma mem_to_array_idx (nums : List ℤ) (target : ℤ) (hmem : target ∈ nums) :
    ∃ p, p < nums.toArray.size ∧ nums.toArray[p]! = target := by
  obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hmem
  exact ⟨i, by simp; exact hi, by simp [getElem!_def, List.getElem?_eq_getElem hi, hget]⟩

-- === MAIN THEOREMS ===

theorem goal_2_1 (nums : List ℤ) (target : ℤ)
    (h_len_pos : nums.length > 0) (h_nodup : nums.Nodup)
    (h_rot : isRotationOfStrictSorted' nums)
    (hmem : ¬inList' nums target)
    (hne : ¬origImpl nums target = -1)
    (i : ℕ) (hi : origImpl nums target = Int.ofNat i) :
    inList' nums target := by
  have ⟨hlt, hget⟩ := origImpl_finds_target nums target i hi
  rw [List.getElem?_eq_some_iff] at hget
  obtain ⟨_, heq⟩ := hget
  rw [← heq]
  exact List.getElem_mem ..

-- For goal_0_1, we need: if target ∈ nums, origImpl doesn't return -1
theorem goal_0_1 (nums : List ℤ) (target : ℤ)
    (h_len_pos : nums.length > 0) (h_nodup : nums.Nodup)
    (h_rot : isRotationOfStrictSorted' nums)
    (hmem : inList' nums target)
    (h_exists_idx : ∃ i < nums.length, nums.get? i = some target) :
    ∀ i < nums.length, nums.get? i = some target →
    origImpl nums target = Int.ofNat i := by
  -- Step 1: Get index p where target is in the array
  have ⟨p, hp_lt, hp_eq⟩ := mem_to_array_idx nums target hmem
  -- Step 2: Use completeness to show origImpl finds p
  have hsa_nodup := list_nodup_to_sa_nodup nums h_nodup
  have hsa_rot := list_rot_sorted_to_sa_rot_sorted nums h_rot h_nodup
  have h_mybs := myBs_complete target nums.toArray 0 nums.toArray.size p (le_refl _)
    hsa_nodup hsa_rot ⟨Nat.zero_le p, hp_lt⟩ hp_eq
  -- Step 3: Convert myBs result to origImpl result
  have h_bs : origImpl.bs target nums.toArray 0 nums.toArray.size = Int.ofNat p := by
    rw [bs_eq_myBs]; exact h_mybs
  have h_impl : origImpl nums target = Int.ofNat p := by
    rw [origImpl_unfold]; exact h_bs
  -- Step 4: For any i with nums.get? i = some target, i = p by uniqueness
  intro i hi hti
  have ⟨_, hget⟩ := origImpl_finds_target nums target p h_impl
  have hget' : nums.get? p = some target := by rwa [List.get?_eq_getElem?]
  have : p = i := nodup_unique_idx nums target h_nodup p i (by simp at hp_lt; exact hp_lt) hi hget' hti
  rw [this] at h_impl
  exact h_impl
