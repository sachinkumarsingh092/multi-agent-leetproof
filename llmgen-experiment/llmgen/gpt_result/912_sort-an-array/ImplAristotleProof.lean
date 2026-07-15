/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: a8ec7d64-0640-44e5-8140-cdf205dd75e9

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem goal_2 (nums : Array ℤ) (require_1 : ∀ i < nums.size, -OfNat.ofNat 50000 ≤ nums[i]! ∧ nums[i]! ≤ OfNat.ofNat 50000) : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (Array.replicate (OfNat.ofNat 100001) (OfNat.ofNat 0)) (OfNat.ofNat 0) (OfNat.ofNat 100001) = OfNat.ofNat 0

- theorem goal_3 (nums : Array ℤ) (require_1 : ∀ i < nums.size, -OfNat.ofNat 50000 ≤ nums[i]! ∧ nums[i]! ≤ OfNat.ofNat 50000) (i_1 : Array ℕ) (cIdx : ℕ) (out : Array ℤ) (invariant_rec_out_size : out.size = nums.size) (out_1 : Array ℤ) (remaining : ℕ) (invariant_in_out_size : out_1.size = nums.size) (invariant_in_remaining_le : remaining ≤ i_1[cIdx]!) (invariant_cnt_i_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1 ≤ nums.size) (invariant_rec_counts_size : i_1.size = OfNat.ofNat 100001) (invariant_rec_cIdx_le : cIdx ≤ OfNat.ofNat 100001) (if_pos : cIdx < OfNat.ofNat 100001) (invariant_in_counts_size : i_1.size = OfNat.ofNat 100001) (invariant_in_cIdx_lt : cIdx < OfNat.ofNat 100001) (if_pos_1 : OfNat.ofNat 0 < remaining) (invariant_cnt_size : i_1.size = OfNat.ofNat 100001) (done_1 : nums.size ≤ Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1) (invariant_cnt_hist : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → i_1[(v + OfNat.ofNat 50000).toNat]! = Array.count v (nums.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1))) (invariant_rec_outPos_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) ≤ out.size) (invariant_rec_prefix_sorted : ∀ (i j : ℕ), i < j → j < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) → j < out.size → (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ≤ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[j]!) (invariant_rec_prefix_range : ∀ i < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size), i < out.size → -OfNat.ofNat 50000 ≤ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ∧ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ≤ OfNat.ofNat 50000) (invariant_rec_prefix_counts_done : ∀ j < cIdx, Array.count (-OfNat.ofNat 50000 + j.cast) (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size))) = i_1[j]!) (invariant_rec_prefix_no_large : ∀ (v : ℤ), cIdx.cast < OfNat.ofNat 50000 + v → Array.count v (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size))) = OfNat.ofNat 0) (invariant_in_outPos_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) ≤ out_1.size) (invariant_in_space : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) + remaining ≤ out_1.size) (invariant_in_prefix_sorted : ∀ (i j : ℕ), i < j → j < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) → j < out_1.size → (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[i]! ≤ (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[j]!) (invariant_in_prefix_range : ∀ i < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining), i < out_1.size → -OfNat.ofNat 50000 ≤ (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[i]! ∧ (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[i]! ≤ OfNat.ofNat 50000) (invariant_in_prefix_counts_done : ∀ j < cIdx, Array.count (-OfNat.ofNat 50000 + j.cast) (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining))) = i_1[j]!) (invariant_in_prefix_counts_cur : Array.count (-OfNat.ofNat 50000 + cIdx.cast) (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining))) = i_1[cIdx]! - remaining) (invariant_in_prefix_no_large : ∀ (v : ℤ), cIdx.cast < OfNat.ofNat 50000 + v → Array.count v (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining))) = OfNat.ofNat 0) : ∀ (i j : ℕ), i < j → j < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) + OfNat.ofNat 1 → j < out_1.size → ((out_1.setIfInBounds (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)) (-OfNat.ofNat 50000 + cIdx.cast)).extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) + OfNat.ofNat 1))[i]! ≤ ((out_1.setIfInBounds (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)) (-OfNat.ofNat 50000 + cIdx.cast)).extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) + OfNat.ofNat 1))[j]!

- theorem goal_4 (nums : Array ℤ) (require_1 : ∀ i < nums.size, -OfNat.ofNat 50000 ≤ nums[i]! ∧ nums[i]! ≤ OfNat.ofNat 50000) (i_1 : Array ℕ) (cIdx : ℕ) (out : Array ℤ) (invariant_rec_out_size : out.size = nums.size) (out_1 : Array ℤ) (remaining : ℕ) (invariant_in_out_size : out_1.size = nums.size) (invariant_in_remaining_le : remaining ≤ i_1[cIdx]!) (invariant_cnt_i_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1 ≤ nums.size) (invariant_rec_counts_size : i_1.size = OfNat.ofNat 100001) (invariant_rec_cIdx_le : cIdx ≤ OfNat.ofNat 100001) (if_pos : cIdx < OfNat.ofNat 100001) (invariant_in_counts_size : i_1.size = OfNat.ofNat 100001) (invariant_in_cIdx_lt : cIdx < OfNat.ofNat 100001) (if_pos_1 : OfNat.ofNat 0 < remaining) (invariant_cnt_size : i_1.size = OfNat.ofNat 100001) (done_1 : nums.size ≤ Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1) (invariant_cnt_hist : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → i_1[(v + OfNat.ofNat 50000).toNat]! = Array.count v (nums.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1))) (invariant_rec_outPos_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) ≤ out.size) (invariant_rec_prefix_sorted : ∀ (i j : ℕ), i < j → j < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) → j < out.size → (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ≤ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[j]!) (invariant_rec_prefix_range : ∀ i < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size), i < out.size → -OfNat.ofNat 50000 ≤ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ∧ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ≤ OfNat.ofNat 50000) (invariant_rec_prefix_counts_done : ∀ j < cIdx, Array.count (-OfNat.ofNat 50000 + j.cast) (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size))) = i_1[j]!) (invariant_rec_prefix_no_large : ∀ (v : ℤ), cIdx.cast < OfNat.ofNat 50000 + v → Array.count v (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size))) = OfNat.ofNat 0) (invariant_in_outPos_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) ≤ out_1.size) (invariant_in_space : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) + remaining ≤ out_1.size) (invariant_in_prefix_sorted : ∀ (i j : ℕ), i < j → j < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) → j < out_1.size → (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[i]! ≤ (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[j]!) (invariant_in_prefix_range : ∀ i < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining), i < out_1.size → -OfNat.ofNat 50000 ≤ (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[i]! ∧ (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[i]! ≤ OfNat.ofNat 50000) (invariant_in_prefix_counts_done : ∀ j < cIdx, Array.count (-OfNat.ofNat 50000 + j.cast) (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining))) = i_1[j]!) (invariant_in_prefix_counts_cur : Array.count (-OfNat.ofNat 50000 + cIdx.cast) (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining))) = i_1[cIdx]! - remaining) (invariant_in_prefix_no_large : ∀ (v : ℤ), cIdx.cast < OfNat.ofNat 50000 + v → Array.count v (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining))) = OfNat.ofNat 0) : ∀ i < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) + OfNat.ofNat 1, i < out_1.size → -OfNat.ofNat 50000 ≤ ((out_1.setIfInBounds (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)) (-OfNat.ofNat 50000 + cIdx.cast)).extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) + OfNat.ofNat 1))[i]! ∧ ((out_1.setIfInBounds (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)) (-OfNat.ofNat 50000 + cIdx.cast)).extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) + OfNat.ofNat 1))[i]! ≤ OfNat.ofNat 50000

- theorem goal_5 (nums : Array ℤ) (require_1 : ∀ i < nums.size, -OfNat.ofNat 50000 ≤ nums[i]! ∧ nums[i]! ≤ OfNat.ofNat 50000) (i_1 : Array ℕ) (cIdx : ℕ) (out : Array ℤ) (invariant_rec_out_size : out.size = nums.size) (out_1 : Array ℤ) (remaining : ℕ) (invariant_in_out_size : out_1.size = nums.size) (invariant_in_remaining_le : remaining ≤ i_1[cIdx]!) (invariant_cnt_i_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1 ≤ nums.size) (invariant_rec_counts_size : i_1.size = OfNat.ofNat 100001) (invariant_rec_cIdx_le : cIdx ≤ OfNat.ofNat 100001) (if_pos : cIdx < OfNat.ofNat 100001) (invariant_in_counts_size : i_1.size = OfNat.ofNat 100001) (invariant_in_cIdx_lt : cIdx < OfNat.ofNat 100001) (if_pos_1 : OfNat.ofNat 0 < remaining) (invariant_cnt_size : i_1.size = OfNat.ofNat 100001) (done_1 : nums.size ≤ Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1) (invariant_cnt_hist : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → i_1[(v + OfNat.ofNat 50000).toNat]! = Array.count v (nums.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1))) (invariant_rec_outPos_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) ≤ out.size) (invariant_rec_prefix_sorted : ∀ (i j : ℕ), i < j → j < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) → j < out.size → (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ≤ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[j]!) (invariant_rec_prefix_range : ∀ i < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size), i < out.size → -OfNat.ofNat 50000 ≤ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ∧ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ≤ OfNat.ofNat 50000) (invariant_rec_prefix_counts_done : ∀ j < cIdx, Array.count (-OfNat.ofNat 50000 + j.cast) (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size))) = i_1[j]!) (invariant_rec_prefix_no_large : ∀ (v : ℤ), cIdx.cast < OfNat.ofNat 50000 + v → Array.count v (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size))) = OfNat.ofNat 0) (invariant_in_outPos_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) ≤ out_1.size) (invariant_in_space : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) + remaining ≤ out_1.size) (invariant_in_prefix_sorted : ∀ (i j : ℕ), i < j → j < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) → j < out_1.size → (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[i]! ≤ (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[j]!) (invariant_in_prefix_range : ∀ i < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining), i < out_1.size → -OfNat.ofNat 50000 ≤ (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[i]! ∧ (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[i]! ≤ OfNat.ofNat 50000) (invariant_in_prefix_counts_done : ∀ j < cIdx, Array.count (-OfNat.ofNat 50000 + j.cast) (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining))) = i_1[j]!) (invariant_in_prefix_counts_cur : Array.count (-OfNat.ofNat 50000 + cIdx.cast) (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining))) = i_1[cIdx]! - remaining) (invariant_in_prefix_no_large : ∀ (v : ℤ), cIdx.cast < OfNat.ofNat 50000 + v → Array.count v (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining))) = OfNat.ofNat 0) : ∀ j < cIdx, Array.count (-OfNat.ofNat 50000 + j.cast) ((out_1.setIfInBounds (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)) (-OfNat.ofNat 50000 + cIdx.cast)).extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) + OfNat.ofNat 1)) = i_1[j]!

- theorem goal_6 (nums : Array ℤ) (require_1 : ∀ i < nums.size, -OfNat.ofNat 50000 ≤ nums[i]! ∧ nums[i]! ≤ OfNat.ofNat 50000) (i_1 : Array ℕ) (cIdx : ℕ) (out : Array ℤ) (invariant_rec_out_size : out.size = nums.size) (out_1 : Array ℤ) (remaining : ℕ) (invariant_in_out_size : out_1.size = nums.size) (invariant_in_remaining_le : remaining ≤ i_1[cIdx]!) (invariant_cnt_i_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1 ≤ nums.size) (invariant_rec_counts_size : i_1.size = OfNat.ofNat 100001) (invariant_rec_cIdx_le : cIdx ≤ OfNat.ofNat 100001) (if_pos : cIdx < OfNat.ofNat 100001) (invariant_in_counts_size : i_1.size = OfNat.ofNat 100001) (invariant_in_cIdx_lt : cIdx < OfNat.ofNat 100001) (if_pos_1 : OfNat.ofNat 0 < remaining) (invariant_cnt_size : i_1.size = OfNat.ofNat 100001) (done_1 : nums.size ≤ Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1) (invariant_cnt_hist : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → i_1[(v + OfNat.ofNat 50000).toNat]! = Array.count v (nums.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1))) (invariant_rec_outPos_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) ≤ out.size) (invariant_rec_prefix_sorted : ∀ (i j : ℕ), i < j → j < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) → j < out.size → (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ≤ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[j]!) (invariant_rec_prefix_range : ∀ i < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size), i < out.size → -OfNat.ofNat 50000 ≤ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ∧ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ≤ OfNat.ofNat 50000) (invariant_rec_prefix_counts_done : ∀ j < cIdx, Array.count (-OfNat.ofNat 50000 + j.cast) (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size))) = i_1[j]!) (invariant_rec_prefix_no_large : ∀ (v : ℤ), cIdx.cast < OfNat.ofNat 50000 + v → Array.count v (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size))) = OfNat.ofNat 0) (invariant_in_outPos_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) ≤ out_1.size) (invariant_in_space : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) + remaining ≤ out_1.size) (invariant_in_prefix_sorted : ∀ (i j : ℕ), i < j → j < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) → j < out_1.size → (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[i]! ≤ (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[j]!) (invariant_in_prefix_range : ∀ i < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining), i < out_1.size → -OfNat.ofNat 50000 ≤ (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[i]! ∧ (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[i]! ≤ OfNat.ofNat 50000) (invariant_in_prefix_counts_done : ∀ j < cIdx, Array.count (-OfNat.ofNat 50000 + j.cast) (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining))) = i_1[j]!) (invariant_in_prefix_counts_cur : Array.count (-OfNat.ofNat 50000 + cIdx.cast) (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining))) = i_1[cIdx]! - remaining) (invariant_in_prefix_no_large : ∀ (v : ℤ), cIdx.cast < OfNat.ofNat 50000 + v → Array.count v (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining))) = OfNat.ofNat 0) : Array.count (-OfNat.ofNat 50000 + cIdx.cast) ((out_1.setIfInBounds (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)) (-OfNat.ofNat 50000 + cIdx.cast)).extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) + OfNat.ofNat 1)) = i_1[cIdx]! - (remaining - OfNat.ofNat 1)

- theorem goal_7 (nums : Array ℤ) (require_1 : ∀ i < nums.size, -OfNat.ofNat 50000 ≤ nums[i]! ∧ nums[i]! ≤ OfNat.ofNat 50000) (i_1 : Array ℕ) (cIdx : ℕ) (out : Array ℤ) (invariant_rec_out_size : out.size = nums.size) (out_1 : Array ℤ) (remaining : ℕ) (invariant_in_out_size : out_1.size = nums.size) (invariant_in_remaining_le : remaining ≤ i_1[cIdx]!) (invariant_cnt_i_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1 ≤ nums.size) (invariant_rec_counts_size : i_1.size = OfNat.ofNat 100001) (invariant_rec_cIdx_le : cIdx ≤ OfNat.ofNat 100001) (if_pos : cIdx < OfNat.ofNat 100001) (invariant_in_counts_size : i_1.size = OfNat.ofNat 100001) (invariant_in_cIdx_lt : cIdx < OfNat.ofNat 100001) (if_pos_1 : OfNat.ofNat 0 < remaining) (invariant_cnt_size : i_1.size = OfNat.ofNat 100001) (done_1 : nums.size ≤ Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1) (invariant_cnt_hist : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → i_1[(v + OfNat.ofNat 50000).toNat]! = Array.count v (nums.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1))) (invariant_rec_outPos_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) ≤ out.size) (invariant_rec_prefix_sorted : ∀ (i j : ℕ), i < j → j < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) → j < out.size → (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ≤ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[j]!) (invariant_rec_prefix_range : ∀ i < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size), i < out.size → -OfNat.ofNat 50000 ≤ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ∧ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ≤ OfNat.ofNat 50000) (invariant_rec_prefix_counts_done : ∀ j < cIdx, Array.count (-OfNat.ofNat 50000 + j.cast) (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size))) = i_1[j]!) (invariant_rec_prefix_no_large : ∀ (v : ℤ), cIdx.cast < OfNat.ofNat 50000 + v → Array.count v (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size))) = OfNat.ofNat 0) (invariant_in_outPos_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) ≤ out_1.size) (invariant_in_space : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) + remaining ≤ out_1.size) (invariant_in_prefix_sorted : ∀ (i j : ℕ), i < j → j < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) → j < out_1.size → (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[i]! ≤ (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[j]!) (invariant_in_prefix_range : ∀ i < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining), i < out_1.size → -OfNat.ofNat 50000 ≤ (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[i]! ∧ (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[i]! ≤ OfNat.ofNat 50000) (invariant_in_prefix_counts_done : ∀ j < cIdx, Array.count (-OfNat.ofNat 50000 + j.cast) (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining))) = i_1[j]!) (invariant_in_prefix_counts_cur : Array.count (-OfNat.ofNat 50000 + cIdx.cast) (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining))) = i_1[cIdx]! - remaining) (invariant_in_prefix_no_large : ∀ (v : ℤ), cIdx.cast < OfNat.ofNat 50000 + v → Array.count v (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining))) = OfNat.ofNat 0) : ∀ (v : ℤ), cIdx.cast < OfNat.ofNat 50000 + v → Array.count v ((out_1.setIfInBounds (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)) (-OfNat.ofNat 50000 + cIdx.cast)).extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) + OfNat.ofNat 1)) = OfNat.ofNat 0

- theorem goal_8 (nums : Array ℤ) (require_1 : ∀ i < nums.size, -OfNat.ofNat 50000 ≤ nums[i]! ∧ nums[i]! ≤ OfNat.ofNat 50000) (i_1 : Array ℕ) (cIdx : ℕ) (out : Array ℤ) (invariant_rec_out_size : out.size = nums.size) (invariant_cnt_i_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1 ≤ nums.size) (invariant_rec_counts_size : i_1.size = OfNat.ofNat 100001) (invariant_rec_cIdx_le : cIdx ≤ OfNat.ofNat 100001) (if_pos : cIdx < OfNat.ofNat 100001) (invariant_cnt_size : i_1.size = OfNat.ofNat 100001) (done_1 : nums.size ≤ Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1) (invariant_cnt_hist : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → i_1[(v + OfNat.ofNat 50000).toNat]! = Array.count v (nums.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1))) (invariant_rec_outPos_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) ≤ out.size) (invariant_rec_prefix_sorted : ∀ (i j : ℕ), i < j → j < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) → j < out.size → (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ≤ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[j]!) (invariant_rec_prefix_range : ∀ i < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size), i < out.size → -OfNat.ofNat 50000 ≤ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ∧ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ≤ OfNat.ofNat 50000) (invariant_rec_prefix_counts_done : ∀ j < cIdx, Array.count (-OfNat.ofNat 50000 + j.cast) (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size))) = i_1[j]!) (invariant_rec_prefix_no_large : ∀ (v : ℤ), cIdx.cast < OfNat.ofNat 50000 + v → Array.count v (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size))) = OfNat.ofNat 0) : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + i_1[cIdx]! ≤ out.size

- theorem goal_9 (nums : Array ℤ) (require_1 : ∀ i < nums.size, -OfNat.ofNat 50000 ≤ nums[i]! ∧ nums[i]! ≤ OfNat.ofNat 50000) (i_1 : Array ℕ) (cIdx : ℕ) (out : Array ℤ) (invariant_rec_out_size : out.size = nums.size) (invariant_cnt_i_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1 ≤ nums.size) (invariant_rec_counts_size : i_1.size = OfNat.ofNat 100001) (invariant_rec_cIdx_le : cIdx ≤ OfNat.ofNat 100001) (if_pos : cIdx < OfNat.ofNat 100001) (invariant_cnt_size : i_1.size = OfNat.ofNat 100001) (done_1 : nums.size ≤ Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1) (invariant_cnt_hist : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → i_1[(v + OfNat.ofNat 50000).toNat]! = Array.count v (nums.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1))) (invariant_rec_outPos_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) ≤ out.size) (invariant_rec_prefix_sorted : ∀ (i j : ℕ), i < j → j < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) → j < out.size → (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ≤ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[j]!) (invariant_rec_prefix_range : ∀ i < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size), i < out.size → -OfNat.ofNat 50000 ≤ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ∧ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ≤ OfNat.ofNat 50000) (invariant_rec_prefix_counts_done : ∀ j < cIdx, Array.count (-OfNat.ofNat 50000 + j.cast) (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size))) = i_1[j]!) (invariant_rec_prefix_no_large : ∀ (v : ℤ), cIdx.cast < OfNat.ofNat 50000 + v → Array.count v (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size))) = OfNat.ofNat 0) : Array.count (-OfNat.ofNat 50000 + cIdx.cast) (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size))) = OfNat.ofNat 0

- theorem goal_10 (nums : Array ℤ) (require_1 : ∀ i < nums.size, -OfNat.ofNat 50000 ≤ nums[i]! ∧ nums[i]! ≤ OfNat.ofNat 50000) (i_1 : Array ℕ) (cIdx : ℕ) (out : Array ℤ) (invariant_rec_out_size : out.size = nums.size) (i_4 : Array ℤ) (remaining_1 : ℕ) (invariant_cnt_i_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1 ≤ nums.size) (invariant_in_out_size : i_4.size = nums.size) (invariant_in_remaining_le : remaining_1 ≤ i_1[cIdx]!) (invariant_rec_counts_size : i_1.size = OfNat.ofNat 100001) (invariant_rec_cIdx_le : cIdx ≤ OfNat.ofNat 100001) (if_pos : cIdx < OfNat.ofNat 100001) (invariant_in_counts_size : i_1.size = OfNat.ofNat 100001) (invariant_in_cIdx_lt : cIdx < OfNat.ofNat 100001) (invariant_cnt_size : i_1.size = OfNat.ofNat 100001) (done_1 : nums.size ≤ Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1) (invariant_cnt_hist : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → i_1[(v + OfNat.ofNat 50000).toNat]! = Array.count v (nums.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1))) (invariant_rec_outPos_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) ≤ out.size) (invariant_rec_prefix_sorted : ∀ (i j : ℕ), i < j → j < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) → j < out.size → (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ≤ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[j]!) (invariant_rec_prefix_range : ∀ i < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size), i < out.size → -OfNat.ofNat 50000 ≤ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ∧ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ≤ OfNat.ofNat 50000) (invariant_rec_prefix_counts_done : ∀ j < cIdx, Array.count (-OfNat.ofNat 50000 + j.cast) (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size))) = i_1[j]!) (invariant_rec_prefix_no_large : ∀ (v : ℤ), cIdx.cast < OfNat.ofNat 50000 + v → Array.count v (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size))) = OfNat.ofNat 0) (done_3 : remaining_1 = OfNat.ofNat 0) (invariant_in_outPos_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining_1) ≤ i_4.size) (invariant_in_space : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining_1) + remaining_1 ≤ i_4.size) (invariant_in_prefix_sorted : ∀ (i j : ℕ), i < j → j < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining_1) → j < i_4.size → (i_4.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining_1)))[i]! ≤ (i_4.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining_1)))[j]!) (invariant_in_prefix_range : ∀ i < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining_1), i < i_4.size → -OfNat.ofNat 50000 ≤ (i_4.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining_1)))[i]! ∧ (i_4.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining_1)))[i]! ≤ OfNat.ofNat 50000) (invariant_in_prefix_counts_done : ∀ j < cIdx, Array.count (-OfNat.ofNat 50000 + j.cast) (i_4.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining_1))) = i_1[j]!) (invariant_in_prefix_counts_cur : Array.count (-OfNat.ofNat 50000 + cIdx.cast) (i_4.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining_1))) = i_1[cIdx]! - remaining_1) (invariant_in_prefix_no_large : ∀ (v : ℤ), cIdx.cast < OfNat.ofNat 50000 + v → Array.count v (i_4.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining_1))) = OfNat.ofNat 0) : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining_1) = Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) (cIdx + OfNat.ofNat 1)) (OfNat.ofNat 0) (min (cIdx + OfNat.ofNat 1) i_1.size)

- theorem goal_11 (nums : Array ℤ) (require_1 : ∀ i < nums.size, -OfNat.ofNat 50000 ≤ nums[i]! ∧ nums[i]! ≤ OfNat.ofNat 50000) (i_1 : Array ℕ) (i_4 : ℕ) (i_5 : Array ℤ) (invariant_cnt_i_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1 ≤ nums.size) (invariant_rec_out_size : i_5.size = nums.size) (invariant_rec_counts_size : i_1.size = OfNat.ofNat 100001) (invariant_cnt_size : i_1.size = OfNat.ofNat 100001) (done_1 : nums.size ≤ Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1) (invariant_cnt_hist : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → i_1[(v + OfNat.ofNat 50000).toNat]! = Array.count v (nums.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1))) (invariant_rec_cIdx_le : i_4 ≤ OfNat.ofNat 100001) (done_2 : OfNat.ofNat 100001 ≤ i_4) (invariant_rec_outPos_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) i_4) (OfNat.ofNat 0) (min i_4 i_1.size) ≤ i_5.size) (invariant_rec_prefix_sorted : ∀ (i j : ℕ), i < j → j < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) i_4) (OfNat.ofNat 0) (min i_4 i_1.size) → j < i_5.size → (i_5.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) i_4) (OfNat.ofNat 0) (min i_4 i_1.size)))[i]! ≤ (i_5.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) i_4) (OfNat.ofNat 0) (min i_4 i_1.size)))[j]!) (invariant_rec_prefix_range : ∀ i < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) i_4) (OfNat.ofNat 0) (min i_4 i_1.size), i < i_5.size → -OfNat.ofNat 50000 ≤ (i_5.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) i_4) (OfNat.ofNat 0) (min i_4 i_1.size)))[i]! ∧ (i_5.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) i_4) (OfNat.ofNat 0) (min i_4 i_1.size)))[i]! ≤ OfNat.ofNat 50000) (invariant_rec_prefix_counts_done : ∀ j < i_4, Array.count (-OfNat.ofNat 50000 + j.cast) (i_5.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) i_4) (OfNat.ofNat 0) (min i_4 i_1.size))) = i_1[j]!) (invariant_rec_prefix_no_large : ∀ (v : ℤ), i_4.cast < OfNat.ofNat 50000 + v → Array.count v (i_5.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) i_4) (OfNat.ofNat 0) (min i_4 i_1.size))) = OfNat.ofNat 0) : postcondition nums i_5

At Harmonic, we use a modified version of the `generalize_proofs` tactic.
For compatibility, we include this tactic at the start of the file.
If you add the comment "-- Harmonic `generalize_proofs` tactic" to your file, we will not do this.
-/

import Mathlib.Tactic


import Mathlib.Tactic.GeneralizeProofs

namespace Harmonic.GeneralizeProofs
-- Harmonic `generalize_proofs` tactic

open Lean Meta Elab Parser.Tactic Elab.Tactic Mathlib.Tactic.GeneralizeProofs
def mkLambdaFVarsUsedOnly' (fvars : Array Expr) (e : Expr) : MetaM (Array Expr × Expr) := do
  let mut e := e
  let mut fvars' : List Expr := []
  for i' in [0:fvars.size] do
    let fvar := fvars[fvars.size - i' - 1]!
    e ← mkLambdaFVars #[fvar] e (usedOnly := false) (usedLetOnly := false)
    match e with
    | .letE _ _ v b _ => e := b.instantiate1 v
    | .lam _ _ _b _ => fvars' := fvar :: fvars'
    | _ => unreachable!
  return (fvars'.toArray, e)

partial def abstractProofs' (e : Expr) (ty? : Option Expr) : MAbs Expr := do
  if (← read).depth ≤ (← read).config.maxDepth then MAbs.withRecurse <| visit (← instantiateMVars e) ty?
  else return e
where
  visit (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    if (← read).config.debug then
      if let some ty := ty? then
        unless ← isDefEq (← inferType e) ty do
          throwError "visit: type of{indentD e}\nis not{indentD ty}"
    if e.isAtomic then
      return e
    else
      checkCache (e, ty?) fun _ ↦ do
        if ← isProof e then
          visitProof e ty?
        else
          match e with
          | .forallE n t b i =>
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              mkForallFVars #[x] (← visit (b.instantiate1 x) none) (usedOnly := false) (usedLetOnly := false)
          | .lam n t b i => do
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              let ty'? ←
                if let some ty := ty? then
                  let .forallE _ _ tyB _ ← pure ty
                    | throwError "Expecting forall in abstractProofs .lam"
                  pure <| some <| tyB.instantiate1 x
                else
                  pure none
              mkLambdaFVars #[x] (← visit (b.instantiate1 x) ty'?) (usedOnly := false) (usedLetOnly := false)
          | .letE n t v b _ =>
            let t' ← visit t none
            withLetDecl n t' (← visit v t') fun x ↦ MAbs.withLocal x do
              mkLetFVars #[x] (← visit (b.instantiate1 x) ty?) (usedLetOnly := false)
          | .app .. =>
            e.withApp fun f args ↦ do
              let f' ← visit f none
              let argTys ← appArgExpectedTypes f' args ty?
              let mut args' := #[]
              for arg in args, argTy in argTys do
                args' := args'.push <| ← visit arg argTy
              return mkAppN f' args'
          | .mdata _ b  => return e.updateMData! (← visit b ty?)
          | .proj _ _ b => return e.updateProj! (← visit b none)
          | _           => unreachable!
  visitProof (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    let eOrig := e
    let fvars := (← read).fvars
    let e := e.withApp' fun f args => f.beta args
    if e.withApp' fun f args => f.isAtomic && args.all fvars.contains then return e
    let e ←
      if let some ty := ty? then
        if (← read).config.debug then
          unless ← isDefEq ty (← inferType e) do
            throwError m!"visitProof: incorrectly propagated type{indentD ty}\nfor{indentD e}"
        mkExpectedTypeHint e ty
      else pure e
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← getLCtx) e do
        throwError m!"visitProof: proof{indentD e}\nis not well-formed in the current context\n\
          fvars: {fvars}"
    let (fvars', pf) ← mkLambdaFVarsUsedOnly' fvars e
    if !(← read).config.abstract && !fvars'.isEmpty then
      return eOrig
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← read).initLCtx pf do
        throwError m!"visitProof: proof{indentD pf}\nis not well-formed in the initial context\n\
          fvars: {fvars}\n{(← mkFreshExprMVar none).mvarId!}"
    let pfTy ← instantiateMVars (← inferType pf)
    let pfTy ← abstractProofs' pfTy none
    if let some pf' ← MAbs.findProof? pfTy then
      return mkAppN pf' fvars'
    MAbs.insertProof pfTy pf
    return mkAppN pf fvars'
partial def withGeneralizedProofs' {α : Type} [Inhabited α] (e : Expr) (ty? : Option Expr)
    (k : Array Expr → Array Expr → Expr → MGen α) :
    MGen α := do
  let propToFVar := (← get).propToFVar
  let (e, generalizations) ← MGen.runMAbs <| abstractProofs' e ty?
  let rec
    go [Inhabited α] (i : Nat) (fvars pfs : Array Expr)
        (proofToFVar propToFVar : ExprMap Expr) : MGen α := do
      if h : i < generalizations.size then
        let (ty, pf) := generalizations[i]
        let ty := (← instantiateMVars (ty.replace proofToFVar.get?)).cleanupAnnotations
        withLocalDeclD (← mkFreshUserName `pf) ty fun fvar => do
          go (i + 1) (fvars := fvars.push fvar) (pfs := pfs.push pf)
            (proofToFVar := proofToFVar.insert pf fvar)
            (propToFVar := propToFVar.insert ty fvar)
      else
        withNewLocalInstances fvars 0 do
          let e' := e.replace proofToFVar.get?
          modify fun s => { s with propToFVar }
          k fvars pfs e'
  go 0 #[] #[] (proofToFVar := {}) (propToFVar := propToFVar)

partial def generalizeProofsCore'
    (g : MVarId) (fvars rfvars : Array FVarId) (target : Bool) :
    MGen (Array Expr × MVarId) := go g 0 #[]
where
  go (g : MVarId) (i : Nat) (hs : Array Expr) : MGen (Array Expr × MVarId) := g.withContext do
    let tag ← g.getTag
    if h : i < rfvars.size then
      let fvar := rfvars[i]
      if fvars.contains fvar then
        let tgt ← instantiateMVars <| ← g.getType
        let ty := (if tgt.isLet then tgt.letType! else tgt.bindingDomain!).cleanupAnnotations
        if ← pure tgt.isLet <&&> Meta.isProp ty then
          let tgt' := Expr.forallE tgt.letName! ty tgt.letBody! .default
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .app g' tgt.letValue!
          return ← go g'.mvarId! i hs
        if let some pf := (← get).propToFVar.get? ty then
          let tgt' := tgt.bindingBody!.instantiate1 pf
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .lam tgt.bindingName! tgt.bindingDomain! g' tgt.bindingInfo!
          return ← go g'.mvarId! (i + 1) hs
        match tgt with
        | .forallE n t b bi =>
          let prop ← Meta.isProp t
          withGeneralizedProofs' t none fun hs' pfs' t' => do
            let t' := t'.cleanupAnnotations
            let tgt' := Expr.forallE n t' b bi
            let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
            g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
            let (fvar', g') ← g'.mvarId!.intro1P
            g'.withContext do Elab.pushInfoLeaf <|
              .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
            if prop then
              MGen.insertFVar t' (.fvar fvar')
            go g' (i + 1) (hs ++ hs')
        | .letE n t v b _ =>
          withGeneralizedProofs' t none fun hs' pfs' t' => do
            withGeneralizedProofs' v t' fun hs'' pfs'' v' => do
              let tgt' := Expr.letE n t' v' b false
              let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
              g.assign <| mkAppN (← mkLambdaFVars (hs' ++ hs'') g' (usedOnly := false) (usedLetOnly := false)) (pfs' ++ pfs'')
              let (fvar', g') ← g'.mvarId!.intro1P
              g'.withContext do Elab.pushInfoLeaf <|
                .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
              go g' (i + 1) (hs ++ hs' ++ hs'')
        | _ => unreachable!
      else
        let (fvar', g') ← g.intro1P
        g'.withContext do Elab.pushInfoLeaf <|
          .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
        go g' (i + 1) hs
    else if target then
      withGeneralizedProofs' (← g.getType) none fun hs' pfs' ty' => do
        let g' ← mkFreshExprSyntheticOpaqueMVar ty' tag
        g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
        return (hs ++ hs', g'.mvarId!)
    else
      return (hs, g)

end GeneralizeProofs

open Lean Elab Parser.Tactic Elab.Tactic Mathlib.Tactic.GeneralizeProofs
partial def generalizeProofs'
    (g : MVarId) (fvars : Array FVarId) (target : Bool) (config : Config := {}) :
    MetaM (Array Expr × MVarId) := do
  let (rfvars, g) ← g.revert fvars (clearAuxDeclsInsteadOfRevert := true)
  g.withContext do
    let s := { propToFVar := ← initialPropToFVar }
    GeneralizeProofs.generalizeProofsCore' g fvars rfvars target |>.run config |>.run' s

elab (name := generalizeProofsElab'') "generalize_proofs" config?:(Parser.Tactic.config)?
    hs:(ppSpace colGt binderIdent)* loc?:(location)? : tactic => withMainContext do
  let config ← elabConfig (mkOptionalNode config?)
  let (fvars, target) ←
    match expandOptLocation (Lean.mkOptionalNode loc?) with
    | .wildcard => pure ((← getLCtx).getFVarIds, true)
    | .targets t target => pure (← getFVarIds t, target)
  liftMetaTactic1 fun g => do
    let (pfs, g) ← generalizeProofs' g fvars target config
    g.withContext do
      let mut lctx ← getLCtx
      for h in hs, fvar in pfs do
        if let `(binderIdent| $s:ident) := h then
          lctx := lctx.setUserName fvar.fvarId! s.getId
        Expr.addLocalVarInfoForBinderIdent fvar h
      Meta.withLCtx lctx (← Meta.getLocalInstances) do
        let g' ← Meta.mkFreshExprSyntheticOpaqueMVar (← g.getType) (← g.getTag)
        g.assign g'
        return g'.mvarId!

end Harmonic

-- Never add new imports here

set_option maxHeartbeats 10000000

set_option pp.coercions false

/- Problem Description
    SortAnArray: Given an array of integers, return the same elements sorted in ascending (nondecreasing) order.
    **Important: complexity should be O(n + k) time and O(k) space, where k is the range of values**
    Natural language breakdown:
    1. Input is an array of integers `nums`.
    2. The output is an array of integers with the same length as `nums`.
    3. The output must be sorted in nondecreasing order (ascending with duplicates allowed).
    4. The output must be a permutation of the input: every integer value occurs the same number of times in the output as in the input.
    5. Constraints: 1 ≤ nums.length ≤ 5 * 10^4.
    6. Constraints: each element nums[i] satisfies -5 * 10^4 ≤ nums[i] ≤ 5 * 10^4.
-/

section Specs

-- The allowed value range from the problem constraints.
def minVal : Int := -50000

def maxVal : Int := 50000

-- Array is sorted in nondecreasing order.
def isSortedNondecreasing (arr : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < arr.size → arr[i]! ≤ arr[j]!

-- All elements satisfy the given inclusive bounds.
def allInRange (arr : Array Int) : Prop :=
  ∀ (i : Nat), i < arr.size → minVal ≤ arr[i]! ∧ arr[i]! ≤ maxVal

-- Input constraints from the problem statement.
def precondition (nums : Array Int) : Prop :=
  allInRange nums

-- Output requirements: same length, sorted, stays within the required bounds,
-- and has exactly the same multiplicities as the input for every Int value.
def postcondition (nums : Array Int) (result : Array Int) : Prop :=
  result.size = nums.size ∧
  isSortedNondecreasing result ∧
  allInRange result ∧
  (∀ (v : Int), result.count v = nums.count v)

end Specs

section TestCases

-- Test case 1: Example 1
-- Input: [5,2,3,1]
-- Output: [1,2,3,5]
def test1_nums : Array Int := #[5, 2, 3, 1]

def test1_Expected : Array Int := #[1, 2, 3, 5]

-- Test case 2: Example 2 with duplicates
-- Input: [5,1,1,2,0,0]
-- Output: [0,0,1,1,2,5]
def test2_nums : Array Int := #[5, 1, 1, 2, 0, 0]

def test2_Expected : Array Int := #[0, 0, 1, 1, 2, 5]

-- Test case 3: Single element (boundary size)
def test3_nums : Array Int := #[42]

def test3_Expected : Array Int := #[42]

-- Test case 4: Already sorted array (includes negatives and 0)
def test4_nums : Array Int := #[-3, -1, 0, 2, 4]

def test4_Expected : Array Int := #[-3, -1, 0, 2, 4]

-- Test case 5: Reverse sorted array
def test5_nums : Array Int := #[4, 3, 2, 1, 0]

def test5_Expected : Array Int := #[0, 1, 2, 3, 4]

-- Test case 6: All elements equal
def test6_nums : Array Int := #[7, 7, 7, 7]

def test6_Expected : Array Int := #[7, 7, 7, 7]

-- Test case 7: Includes negative numbers and duplicates
def test7_nums : Array Int := #[-1, -5, -1, 3, 0, -5]

def test7_Expected : Array Int := #[-5, -5, -1, -1, 0, 3]

-- Test case 8: Includes min/max constraint boundaries
def test8_nums : Array Int := #[50000, -50000, 0, 50000, -50000]

def test8_Expected : Array Int := #[-50000, -50000, 0, 50000, 50000]

-- Test case 9: Mixed values with repeated zeros
def test9_nums : Array Int := #[0, 2, 0, 1, 2, 0]

def test9_Expected : Array Int := #[0, 0, 0, 1, 2, 2]

end TestCases

section Proof

theorem goal_2 (nums : Array ℤ) (require_1 : ∀ i < nums.size, -OfNat.ofNat 50000 ≤ nums[i]! ∧ nums[i]! ≤ OfNat.ofNat 50000) : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (Array.replicate (OfNat.ofNat 100001) (OfNat.ofNat 0)) (OfNat.ofNat 0) (OfNat.ofNat 100001) = OfNat.ofNat 0 := by
    native_decide +revert

noncomputable section AristotleLemmas

/-
Extracting a prefix of size `i+1` from an array after setting the element at index `i` is equivalent to taking the prefix of size `i` from the original array and pushing the new value `v`. This holds provided `i` is within bounds.
-/
lemma extract_setIfInBounds_succ_eq_push {α : Type} [Inhabited α] (arr : Array α) (i : Nat) (v : α) (h : i < arr.size) :
  (arr.setIfInBounds i v).extract 0 (i + 1) = (arr.extract 0 i).push v := by
    ext j;
    · grind +ring;
    · by_cases hj : j < i <;> simp_all +decide [ Array.getElem_push ];
      · grind;
      · grind +ring

/-
When the index `i` is within the bounds of the array `arr`, `setIfInBounds` is equivalent to `set`.
-/
lemma setIfInBounds_eq_set_of_lt {α : Type} [Inhabited α] (arr : Array α) (i : Nat) (v : α) (h : i < arr.size) :
  arr.setIfInBounds i v = arr.set i v := by
    rw [ Array.setIfInBounds ] ; aesop

/-
If an array is sorted and all its elements are less than or equal to a value `v`, then pushing `v` to the array results in a sorted array.
-/
lemma sorted_push_of_sorted_and_le (arr : Array Int) (v : Int)
  (h_sorted : isSortedNondecreasing arr)
  (h_le : ∀ i : Nat, i < arr.size → arr[i]! ≤ v) :
  isSortedNondecreasing (arr.push v) := by
    -- Let's unfold the definition of `isSortedNondecreasing`.
    unfold isSortedNondecreasing at *;
    grind +ring

/-
If the count of every integer strictly greater than `limit` in the array `arr` is zero, then every element `x` in `arr` must be less than or equal to `limit`.
-/
lemma le_of_all_count_zero_gt (arr : Array Int) (limit : Int)
  (h : ∀ v, limit < v → arr.count v = 0) :
  ∀ x, x ∈ arr → x ≤ limit := by
    -- If $x$ is in the array and $x > \text{limit}$, then by $h$, the count of $x$ in the array is zero, which contradicts $x$ being in the array.
    intros x hx
    by_contra h_contra
    have h_count : arr.count x = 0 := by
      exact h x <| not_le.mp h_contra;
    simp_all +decide [ Array.count ];
    exact h x h_contra x hx rfl

end AristotleLemmas

theorem goal_3 (nums : Array ℤ) (require_1 : ∀ i < nums.size, -OfNat.ofNat 50000 ≤ nums[i]! ∧ nums[i]! ≤ OfNat.ofNat 50000) (i_1 : Array ℕ) (cIdx : ℕ) (out : Array ℤ) (invariant_rec_out_size : out.size = nums.size) (out_1 : Array ℤ) (remaining : ℕ) (invariant_in_out_size : out_1.size = nums.size) (invariant_in_remaining_le : remaining ≤ i_1[cIdx]!) (invariant_cnt_i_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1 ≤ nums.size) (invariant_rec_counts_size : i_1.size = OfNat.ofNat 100001) (invariant_rec_cIdx_le : cIdx ≤ OfNat.ofNat 100001) (if_pos : cIdx < OfNat.ofNat 100001) (invariant_in_counts_size : i_1.size = OfNat.ofNat 100001) (invariant_in_cIdx_lt : cIdx < OfNat.ofNat 100001) (if_pos_1 : OfNat.ofNat 0 < remaining) (invariant_cnt_size : i_1.size = OfNat.ofNat 100001) (done_1 : nums.size ≤ Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1) (invariant_cnt_hist : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → i_1[(v + OfNat.ofNat 50000).toNat]! = Array.count v (nums.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1))) (invariant_rec_outPos_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) ≤ out.size) (invariant_rec_prefix_sorted : ∀ (i j : ℕ), i < j → j < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) → j < out.size → (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ≤ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[j]!) (invariant_rec_prefix_range : ∀ i < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size), i < out.size → -OfNat.ofNat 50000 ≤ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ∧ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ≤ OfNat.ofNat 50000) (invariant_rec_prefix_counts_done : ∀ j < cIdx, Array.count (-OfNat.ofNat 50000 + j.cast) (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size))) = i_1[j]!) (invariant_rec_prefix_no_large : ∀ (v : ℤ), cIdx.cast < OfNat.ofNat 50000 + v → Array.count v (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size))) = OfNat.ofNat 0) (invariant_in_outPos_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) ≤ out_1.size) (invariant_in_space : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) + remaining ≤ out_1.size) (invariant_in_prefix_sorted : ∀ (i j : ℕ), i < j → j < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) → j < out_1.size → (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[i]! ≤ (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[j]!) (invariant_in_prefix_range : ∀ i < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining), i < out_1.size → -OfNat.ofNat 50000 ≤ (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[i]! ∧ (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[i]! ≤ OfNat.ofNat 50000) (invariant_in_prefix_counts_done : ∀ j < cIdx, Array.count (-OfNat.ofNat 50000 + j.cast) (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining))) = i_1[j]!) (invariant_in_prefix_counts_cur : Array.count (-OfNat.ofNat 50000 + cIdx.cast) (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining))) = i_1[cIdx]! - remaining) (invariant_in_prefix_no_large : ∀ (v : ℤ), cIdx.cast < OfNat.ofNat 50000 + v → Array.count v (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining))) = OfNat.ofNat 0) : ∀ (i j : ℕ), i < j → j < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) + OfNat.ofNat 1 → j < out_1.size → ((out_1.setIfInBounds (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)) (-OfNat.ofNat 50000 + cIdx.cast)).extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) + OfNat.ofNat 1))[i]! ≤ ((out_1.setIfInBounds (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)) (-OfNat.ofNat 50000 + cIdx.cast)).extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) + OfNat.ofNat 1))[j]! := by
    intros i j hij hj_lt hj_lt_out
    have h_le : ∀ x ∈ out_1.extract 0 (Array.foldl (fun (s x : ℕ) => s + x) (OfNat.ofNat (OfNat.ofNat 0)) (i_1.extract (OfNat.ofNat (OfNat.ofNat 0)) cIdx) (OfNat.ofNat (OfNat.ofNat 0)) (Min.min cIdx i_1.size) + (i_1[cIdx]! - remaining)), x ≤ -OfNat.ofNat (OfNat.ofNat 50000) + cIdx.cast := by
      intros x hx; specialize invariant_in_prefix_no_large x; simp_all +decide [ Array.count_eq_zero ] ;
    generalize_proofs at *; (
    have h_sorted : isSortedNondecreasing (out_1.extract 0 (Array.foldl (fun (s x : ℕ) => s + x) (OfNat.ofNat (OfNat.ofNat 0)) (i_1.extract (OfNat.ofNat (OfNat.ofNat 0)) cIdx) (OfNat.ofNat (OfNat.ofNat 0)) (Min.min cIdx i_1.size) + (i_1[cIdx]! - remaining))) := by
      convert invariant_in_prefix_sorted using 1
      generalize_proofs at *; (
      simp +decide [ isSortedNondecreasing ])
    generalize_proofs at *; (
    have h_sorted_push : isSortedNondecreasing ((out_1.extract 0 (Array.foldl (fun (s x : ℕ) => s + x) (OfNat.ofNat (OfNat.ofNat 0)) (i_1.extract (OfNat.ofNat (OfNat.ofNat 0)) cIdx) (OfNat.ofNat (OfNat.ofNat 0)) (Min.min cIdx i_1.size) + (i_1[cIdx]! - remaining))).push (-OfNat.ofNat (OfNat.ofNat 50000) + cIdx.cast)) := by
      apply_rules [ sorted_push_of_sorted_and_le ];
      exact fun i hi => h_le _ <| by
        convert Array.getElem_mem _;
        any_goals exact hi;
        exact?
    generalize_proofs at *; (
    convert h_sorted_push i j hij _ using 1
    all_goals generalize_proofs at *;
    · convert congr_arg ( fun x : Array ℤ => x[i]! ) ( extract_setIfInBounds_succ_eq_push _ _ _ _ ) using 1
      (generalize_proofs at *; (
      grind));
    · rw [ extract_setIfInBounds_succ_eq_push ] ; norm_num;
      grind +ring;
    · simp +zetaDelta at *;
      rw [ min_def ] ; split_ifs <;> linarith! [ Nat.sub_add_cancel invariant_in_remaining_le ] ;)))

theorem goal_4 (nums : Array ℤ) (require_1 : ∀ i < nums.size, -OfNat.ofNat 50000 ≤ nums[i]! ∧ nums[i]! ≤ OfNat.ofNat 50000) (i_1 : Array ℕ) (cIdx : ℕ) (out : Array ℤ) (invariant_rec_out_size : out.size = nums.size) (out_1 : Array ℤ) (remaining : ℕ) (invariant_in_out_size : out_1.size = nums.size) (invariant_in_remaining_le : remaining ≤ i_1[cIdx]!) (invariant_cnt_i_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1 ≤ nums.size) (invariant_rec_counts_size : i_1.size = OfNat.ofNat 100001) (invariant_rec_cIdx_le : cIdx ≤ OfNat.ofNat 100001) (if_pos : cIdx < OfNat.ofNat 100001) (invariant_in_counts_size : i_1.size = OfNat.ofNat 100001) (invariant_in_cIdx_lt : cIdx < OfNat.ofNat 100001) (if_pos_1 : OfNat.ofNat 0 < remaining) (invariant_cnt_size : i_1.size = OfNat.ofNat 100001) (done_1 : nums.size ≤ Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1) (invariant_cnt_hist : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → i_1[(v + OfNat.ofNat 50000).toNat]! = Array.count v (nums.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1))) (invariant_rec_outPos_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) ≤ out.size) (invariant_rec_prefix_sorted : ∀ (i j : ℕ), i < j → j < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) → j < out.size → (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ≤ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[j]!) (invariant_rec_prefix_range : ∀ i < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size), i < out.size → -OfNat.ofNat 50000 ≤ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ∧ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ≤ OfNat.ofNat 50000) (invariant_rec_prefix_counts_done : ∀ j < cIdx, Array.count (-OfNat.ofNat 50000 + j.cast) (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size))) = i_1[j]!) (invariant_rec_prefix_no_large : ∀ (v : ℤ), cIdx.cast < OfNat.ofNat 50000 + v → Array.count v (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size))) = OfNat.ofNat 0) (invariant_in_outPos_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) ≤ out_1.size) (invariant_in_space : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) + remaining ≤ out_1.size) (invariant_in_prefix_sorted : ∀ (i j : ℕ), i < j → j < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) → j < out_1.size → (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[i]! ≤ (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[j]!) (invariant_in_prefix_range : ∀ i < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining), i < out_1.size → -OfNat.ofNat 50000 ≤ (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[i]! ∧ (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[i]! ≤ OfNat.ofNat 50000) (invariant_in_prefix_counts_done : ∀ j < cIdx, Array.count (-OfNat.ofNat 50000 + j.cast) (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining))) = i_1[j]!) (invariant_in_prefix_counts_cur : Array.count (-OfNat.ofNat 50000 + cIdx.cast) (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining))) = i_1[cIdx]! - remaining) (invariant_in_prefix_no_large : ∀ (v : ℤ), cIdx.cast < OfNat.ofNat 50000 + v → Array.count v (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining))) = OfNat.ofNat 0) : ∀ i < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) + OfNat.ofNat 1, i < out_1.size → -OfNat.ofNat 50000 ≤ ((out_1.setIfInBounds (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)) (-OfNat.ofNat 50000 + cIdx.cast)).extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) + OfNat.ofNat 1))[i]! ∧ ((out_1.setIfInBounds (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)) (-OfNat.ofNat 50000 + cIdx.cast)).extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) + OfNat.ofNat 1))[i]! ≤ OfNat.ofNat 50000 := by
    intros i hi hi';
    by_cases hi'' : i < Array.foldl (fun s x => s + x) (OfNat.ofNat (OfNat.ofNat 0)) (i_1.extract (OfNat.ofNat (OfNat.ofNat 0)) cIdx) (OfNat.ofNat (OfNat.ofNat 0)) (Min.min cIdx i_1.size) + (i_1[cIdx]! - remaining);
    · simp_all +decide [ Array.setIfInBounds ];
      split_ifs <;> simp_all +decide [ Array.set ];
      rw [ List.getElem_set ] ; aesop;
    · -- Since $i$ is not less than the sum of the counts plus the remaining elements, we have $i = \text{sum of counts} + \text{remaining elements}$.
      have hi_eq : i = Array.foldl (fun s x => s + x) (OfNat.ofNat (OfNat.ofNat 0)) (i_1.extract (OfNat.ofNat (OfNat.ofNat 0)) cIdx) (OfNat.ofNat (OfNat.ofNat 0)) (Min.min cIdx i_1.size) + (i_1[cIdx]! - remaining) := by
        exact le_antisymm ( Nat.le_of_lt_succ hi ) ( not_lt.mp hi'' );
      simp +decide [ hi_eq, Array.setIfInBounds ];
      split_ifs <;> simp_all +decide [ Array.set ];
      grind +ring

theorem goal_5 (nums : Array ℤ) (require_1 : ∀ i < nums.size, -OfNat.ofNat 50000 ≤ nums[i]! ∧ nums[i]! ≤ OfNat.ofNat 50000) (i_1 : Array ℕ) (cIdx : ℕ) (out : Array ℤ) (invariant_rec_out_size : out.size = nums.size) (out_1 : Array ℤ) (remaining : ℕ) (invariant_in_out_size : out_1.size = nums.size) (invariant_in_remaining_le : remaining ≤ i_1[cIdx]!) (invariant_cnt_i_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1 ≤ nums.size) (invariant_rec_counts_size : i_1.size = OfNat.ofNat 100001) (invariant_rec_cIdx_le : cIdx ≤ OfNat.ofNat 100001) (if_pos : cIdx < OfNat.ofNat 100001) (invariant_in_counts_size : i_1.size = OfNat.ofNat 100001) (invariant_in_cIdx_lt : cIdx < OfNat.ofNat 100001) (if_pos_1 : OfNat.ofNat 0 < remaining) (invariant_cnt_size : i_1.size = OfNat.ofNat 100001) (done_1 : nums.size ≤ Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1) (invariant_cnt_hist : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → i_1[(v + OfNat.ofNat 50000).toNat]! = Array.count v (nums.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1))) (invariant_rec_outPos_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) ≤ out.size) (invariant_rec_prefix_sorted : ∀ (i j : ℕ), i < j → j < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) → j < out.size → (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ≤ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[j]!) (invariant_rec_prefix_range : ∀ i < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size), i < out.size → -OfNat.ofNat 50000 ≤ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ∧ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ≤ OfNat.ofNat 50000) (invariant_rec_prefix_counts_done : ∀ j < cIdx, Array.count (-OfNat.ofNat 50000 + j.cast) (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size))) = i_1[j]!) (invariant_rec_prefix_no_large : ∀ (v : ℤ), cIdx.cast < OfNat.ofNat 50000 + v → Array.count v (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size))) = OfNat.ofNat 0) (invariant_in_outPos_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) ≤ out_1.size) (invariant_in_space : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) + remaining ≤ out_1.size) (invariant_in_prefix_sorted : ∀ (i j : ℕ), i < j → j < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) → j < out_1.size → (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[i]! ≤ (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[j]!) (invariant_in_prefix_range : ∀ i < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining), i < out_1.size → -OfNat.ofNat 50000 ≤ (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[i]! ∧ (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[i]! ≤ OfNat.ofNat 50000) (invariant_in_prefix_counts_done : ∀ j < cIdx, Array.count (-OfNat.ofNat 50000 + j.cast) (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining))) = i_1[j]!) (invariant_in_prefix_counts_cur : Array.count (-OfNat.ofNat 50000 + cIdx.cast) (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining))) = i_1[cIdx]! - remaining) (invariant_in_prefix_no_large : ∀ (v : ℤ), cIdx.cast < OfNat.ofNat 50000 + v → Array.count v (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining))) = OfNat.ofNat 0) : ∀ j < cIdx, Array.count (-OfNat.ofNat 50000 + j.cast) ((out_1.setIfInBounds (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)) (-OfNat.ofNat 50000 + cIdx.cast)).extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) + OfNat.ofNat 1)) = i_1[j]! := by
    -- Since $j < cIdx$, the element at $j$ in the extracted array is the same as in the original $out_1$ array.
    intros j hj
    simp [Array.setIfInBounds, hj];
    split_ifs <;> simp_all +decide [ Array.count ];
    · convert invariant_in_prefix_counts_done j hj using 1;
      simp +decide [ Array.set ];
      rw [ List.take_set ];
      rw [ List.set_eq_take_cons_drop ] ; simp +decide [ List.countP_cons ] ; ring;
      · simp +decide [ List.take_take, hj.ne' ];
        -- Since the array's extract is equivalent to the list's take, their counts should be equal.
        have h_eq : List.take (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) cIdx + (i_1[cIdx] - remaining)) out_1.toList = (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) cIdx + (i_1[cIdx] - remaining))).toList := by
          simp +decide [ Array.toList ];
        grind;
      · grind +ring;
    · grind

theorem goal_6 (nums : Array ℤ) (require_1 : ∀ i < nums.size, -OfNat.ofNat 50000 ≤ nums[i]! ∧ nums[i]! ≤ OfNat.ofNat 50000) (i_1 : Array ℕ) (cIdx : ℕ) (out : Array ℤ) (invariant_rec_out_size : out.size = nums.size) (out_1 : Array ℤ) (remaining : ℕ) (invariant_in_out_size : out_1.size = nums.size) (invariant_in_remaining_le : remaining ≤ i_1[cIdx]!) (invariant_cnt_i_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1 ≤ nums.size) (invariant_rec_counts_size : i_1.size = OfNat.ofNat 100001) (invariant_rec_cIdx_le : cIdx ≤ OfNat.ofNat 100001) (if_pos : cIdx < OfNat.ofNat 100001) (invariant_in_counts_size : i_1.size = OfNat.ofNat 100001) (invariant_in_cIdx_lt : cIdx < OfNat.ofNat 100001) (if_pos_1 : OfNat.ofNat 0 < remaining) (invariant_cnt_size : i_1.size = OfNat.ofNat 100001) (done_1 : nums.size ≤ Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1) (invariant_cnt_hist : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → i_1[(v + OfNat.ofNat 50000).toNat]! = Array.count v (nums.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1))) (invariant_rec_outPos_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) ≤ out.size) (invariant_rec_prefix_sorted : ∀ (i j : ℕ), i < j → j < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) → j < out.size → (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ≤ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[j]!) (invariant_rec_prefix_range : ∀ i < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size), i < out.size → -OfNat.ofNat 50000 ≤ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ∧ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ≤ OfNat.ofNat 50000) (invariant_rec_prefix_counts_done : ∀ j < cIdx, Array.count (-OfNat.ofNat 50000 + j.cast) (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size))) = i_1[j]!) (invariant_rec_prefix_no_large : ∀ (v : ℤ), cIdx.cast < OfNat.ofNat 50000 + v → Array.count v (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size))) = OfNat.ofNat 0) (invariant_in_outPos_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) ≤ out_1.size) (invariant_in_space : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) + remaining ≤ out_1.size) (invariant_in_prefix_sorted : ∀ (i j : ℕ), i < j → j < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) → j < out_1.size → (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[i]! ≤ (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[j]!) (invariant_in_prefix_range : ∀ i < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining), i < out_1.size → -OfNat.ofNat 50000 ≤ (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[i]! ∧ (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[i]! ≤ OfNat.ofNat 50000) (invariant_in_prefix_counts_done : ∀ j < cIdx, Array.count (-OfNat.ofNat 50000 + j.cast) (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining))) = i_1[j]!) (invariant_in_prefix_counts_cur : Array.count (-OfNat.ofNat 50000 + cIdx.cast) (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining))) = i_1[cIdx]! - remaining) (invariant_in_prefix_no_large : ∀ (v : ℤ), cIdx.cast < OfNat.ofNat 50000 + v → Array.count v (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining))) = OfNat.ofNat 0) : Array.count (-OfNat.ofNat 50000 + cIdx.cast) ((out_1.setIfInBounds (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)) (-OfNat.ofNat 50000 + cIdx.cast)).extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) + OfNat.ofNat 1)) = i_1[cIdx]! - (remaining - OfNat.ofNat 1) := by
    -- By definition of `setIfInBounds`, the count of `-50000 + cIdx.cast` in the modified array is the count in the original array plus the count of the new element.
    have h_count : Array.count (-OfNat.ofNat (OfNat.ofNat 50000) + cIdx.cast) ((out_1.setIfInBounds (Array.foldl (fun s x => s + x) (OfNat.ofNat (OfNat.ofNat 0)) (i_1.extract (OfNat.ofNat (OfNat.ofNat 0)) cIdx) (OfNat.ofNat (OfNat.ofNat 0)) (Min.min cIdx i_1.size) + (i_1[cIdx]! - remaining)) (-OfNat.ofNat (OfNat.ofNat 50000) + cIdx.cast)).extract (OfNat.ofNat (OfNat.ofNat 0)) (Array.foldl (fun s x => s + x) (OfNat.ofNat (OfNat.ofNat 0)) (i_1.extract (OfNat.ofNat (OfNat.ofNat 0)) cIdx) (OfNat.ofNat (OfNat.ofNat 0)) (Min.min cIdx i_1.size) + (i_1[cIdx]! - remaining) + OfNat.ofNat (OfNat.ofNat 1))) = Array.count (-OfNat.ofNat (OfNat.ofNat 50000) + cIdx.cast) (out_1.extract (OfNat.ofNat (OfNat.ofNat 0)) (Array.foldl (fun s x => s + x) (OfNat.ofNat (OfNat.ofNat 0)) (i_1.extract (OfNat.ofNat (OfNat.ofNat 0)) cIdx) (OfNat.ofNat (OfNat.ofNat 0)) (Min.min cIdx i_1.size) + (i_1[cIdx]! - remaining))) + 1 := by
      rw [ Array.setIfInBounds ];
      split_ifs <;> simp_all +decide [ Array.count_set ];
      · simp_all +decide [ Array.set, Array.count ];
        simp_all +decide [ List.take_set, List.countP_set ];
        split_ifs <;> simp_all +decide [ List.take_succ ];
        · convert invariant_in_prefix_counts_cur using 1;
          rw [ Array.countP ];
          -- By definition of `List.countP`, we can rewrite the left-hand side of the equation.
          have h_countP : ∀ (l : List ℤ) (p : ℤ → Bool), List.countP p l = List.foldr (fun a acc => if p a then acc + 1 else acc) 0 l := by
            intro l p; induction l <;> simp +decide [ * ] ;
            split_ifs <;> simp_all +decide [ List.countP_cons ];
          convert h_countP _ _ using 1;
          conv => rw [ ← Array.foldr_toList ] ;
          simp +zetaDelta at *;
          grind;
        · convert invariant_in_prefix_counts_cur using 1;
          rw [ Array.countP ];
          rw [ ← Array.foldr_toList ];
          rw [ ← List.take_append_drop ( Array.foldl ( fun s x => s + x ) ( OfNat.ofNat ( OfNat.ofNat ( OfNat.ofNat 0 ) ) ) ( i_1.extract ( OfNat.ofNat 0 ) cIdx ) ( OfNat.ofNat ( OfNat.ofNat ( OfNat.ofNat 0 ) ) ) cIdx + ( i_1[cIdx] - remaining ) ) out_1.toList ] ; simp +decide [ List.take_append_of_le_length ];
          induction ( List.take ( Array.foldl ( fun s x => s + x ) ( OfNat.ofNat ( OfNat.ofNat ( OfNat.ofNat 0 ) ) ) ( i_1.extract ( OfNat.ofNat 0 ) cIdx ) ( OfNat.ofNat ( OfNat.ofNat ( OfNat.ofNat 0 ) ) ) cIdx + ( i_1[cIdx] - remaining ) ) out_1.toList ) <;> simp +decide [ * ];
          by_cases h : ‹ℤ› == -OfNat.ofNat (OfNat.ofNat (OfNat.ofNat 50000)) + cIdx.cast <;> simp +decide [ h, * ];
      · exact absurd ‹_› ( by linarith );
    convert h_count using 1;
    exact Nat.sub_eq_of_eq_add <| by linarith [ Nat.sub_add_cancel <| show 1 ≤ remaining from if_pos_1, Nat.sub_add_cancel <| show remaining ≤ i_1[cIdx]! from invariant_in_remaining_le ] ;

theorem goal_7 (nums : Array ℤ) (require_1 : ∀ i < nums.size, -OfNat.ofNat 50000 ≤ nums[i]! ∧ nums[i]! ≤ OfNat.ofNat 50000) (i_1 : Array ℕ) (cIdx : ℕ) (out : Array ℤ) (invariant_rec_out_size : out.size = nums.size) (out_1 : Array ℤ) (remaining : ℕ) (invariant_in_out_size : out_1.size = nums.size) (invariant_in_remaining_le : remaining ≤ i_1[cIdx]!) (invariant_cnt_i_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1 ≤ nums.size) (invariant_rec_counts_size : i_1.size = OfNat.ofNat 100001) (invariant_rec_cIdx_le : cIdx ≤ OfNat.ofNat 100001) (if_pos : cIdx < OfNat.ofNat 100001) (invariant_in_counts_size : i_1.size = OfNat.ofNat 100001) (invariant_in_cIdx_lt : cIdx < OfNat.ofNat 100001) (if_pos_1 : OfNat.ofNat 0 < remaining) (invariant_cnt_size : i_1.size = OfNat.ofNat 100001) (done_1 : nums.size ≤ Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1) (invariant_cnt_hist : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → i_1[(v + OfNat.ofNat 50000).toNat]! = Array.count v (nums.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1))) (invariant_rec_outPos_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) ≤ out.size) (invariant_rec_prefix_sorted : ∀ (i j : ℕ), i < j → j < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) → j < out.size → (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ≤ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[j]!) (invariant_rec_prefix_range : ∀ i < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size), i < out.size → -OfNat.ofNat 50000 ≤ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ∧ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ≤ OfNat.ofNat 50000) (invariant_rec_prefix_counts_done : ∀ j < cIdx, Array.count (-OfNat.ofNat 50000 + j.cast) (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size))) = i_1[j]!) (invariant_rec_prefix_no_large : ∀ (v : ℤ), cIdx.cast < OfNat.ofNat 50000 + v → Array.count v (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size))) = OfNat.ofNat 0) (invariant_in_outPos_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) ≤ out_1.size) (invariant_in_space : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) + remaining ≤ out_1.size) (invariant_in_prefix_sorted : ∀ (i j : ℕ), i < j → j < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) → j < out_1.size → (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[i]! ≤ (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[j]!) (invariant_in_prefix_range : ∀ i < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining), i < out_1.size → -OfNat.ofNat 50000 ≤ (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[i]! ∧ (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[i]! ≤ OfNat.ofNat 50000) (invariant_in_prefix_counts_done : ∀ j < cIdx, Array.count (-OfNat.ofNat 50000 + j.cast) (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining))) = i_1[j]!) (invariant_in_prefix_counts_cur : Array.count (-OfNat.ofNat 50000 + cIdx.cast) (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining))) = i_1[cIdx]! - remaining) (invariant_in_prefix_no_large : ∀ (v : ℤ), cIdx.cast < OfNat.ofNat 50000 + v → Array.count v (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining))) = OfNat.ofNat 0) : ∀ (v : ℤ), cIdx.cast < OfNat.ofNat 50000 + v → Array.count v ((out_1.setIfInBounds (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)) (-OfNat.ofNat 50000 + cIdx.cast)).extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) + OfNat.ofNat 1)) = OfNat.ofNat 0 := by
    intro v hv; specialize invariant_in_prefix_no_large v hv; simp_all +decide [ Array.count ] ;
    intro a ha; contrapose! invariant_in_prefix_no_large; simp_all +decide [ Array.setIfInBounds ] ;
    split_ifs at ha <;> simp_all +decide [ Array.mem_iff_getElem ] ;
    · obtain ⟨ i, hi, hi' ⟩ := ha; use i; simp_all +decide [ Array.getElem_set ] ;
      split_ifs at hi' <;> simp_all +decide [ Array.getElem_set ] ;
      · grind;
      · exact lt_of_le_of_ne ( Nat.le_of_lt_succ hi.1 ) ( Ne.symm ‹_› );
    · grind +ring

theorem goal_8 (nums : Array ℤ) (require_1 : ∀ i < nums.size, -OfNat.ofNat 50000 ≤ nums[i]! ∧ nums[i]! ≤ OfNat.ofNat 50000) (i_1 : Array ℕ) (cIdx : ℕ) (out : Array ℤ) (invariant_rec_out_size : out.size = nums.size) (invariant_cnt_i_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1 ≤ nums.size) (invariant_rec_counts_size : i_1.size = OfNat.ofNat 100001) (invariant_rec_cIdx_le : cIdx ≤ OfNat.ofNat 100001) (if_pos : cIdx < OfNat.ofNat 100001) (invariant_cnt_size : i_1.size = OfNat.ofNat 100001) (done_1 : nums.size ≤ Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1) (invariant_cnt_hist : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → i_1[(v + OfNat.ofNat 50000).toNat]! = Array.count v (nums.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1))) (invariant_rec_outPos_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) ≤ out.size) (invariant_rec_prefix_sorted : ∀ (i j : ℕ), i < j → j < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) → j < out.size → (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ≤ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[j]!) (invariant_rec_prefix_range : ∀ i < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size), i < out.size → -OfNat.ofNat 50000 ≤ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ∧ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ≤ OfNat.ofNat 50000) (invariant_rec_prefix_counts_done : ∀ j < cIdx, Array.count (-OfNat.ofNat 50000 + j.cast) (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size))) = i_1[j]!) (invariant_rec_prefix_no_large : ∀ (v : ℤ), cIdx.cast < OfNat.ofNat 50000 + v → Array.count v (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size))) = OfNat.ofNat 0) : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + i_1[cIdx]! ≤ out.size := by
    -- By definition of `Array.foldl`, we know that the sum of the elements in `i_1` up to `cIdx` is equal to the sum of the elements in `i_1` up to `cIdx`.
    have h_sum_eq : Array.foldl (fun (s x : ℕ) => s + x) (OfNat.ofNat (OfNat.ofNat 0)) (i_1.extract (OfNat.ofNat (OfNat.ofNat 0)) cIdx) (OfNat.ofNat (OfNat.ofNat 0)) (Min.min cIdx i_1.size) + i_1[cIdx]! ≤ Array.foldl (fun (s x : ℕ) => s + x) (OfNat.ofNat (OfNat.ofNat 0)) i_1 := by
      have h_foldl_le : ∀ (l : List ℕ) (c : ℕ), c < l.length → List.foldl (fun s x => s + x) 0 (List.take c l) + l.get! c ≤ List.foldl (fun s x => s + x) 0 l := by
        intros l c hc
        have h_foldl_le : List.foldl (fun s x => s + x) 0 (List.take (c + 1) l) ≤ List.foldl (fun s x => s + x) 0 l := by
          have h_foldl_le : ∀ (l : List ℕ) (c : ℕ), c < l.length → List.foldl (fun s x => s + x) 0 (List.take (c + 1) l) ≤ List.foldl (fun s x => s + x) 0 l := by
            intros l c hc
            have h_foldl_le : List.foldl (fun s x => s + x) 0 (List.take (c + 1) l) ≤ List.foldl (fun s x => s + x) 0 (List.take (c + 1) l ++ List.drop (c + 1) l) := by
              induction' ( List.drop ( c + 1 ) l ) using List.reverseRecOn with l ih <;> simp +decide [ * ] at * ; linarith! [ Nat.zero_le ( List.foldl ( fun s x => s + x ) 0 l ) ] ;
            rwa [ List.take_append_drop ] at h_foldl_le;
          generalize_proofs at *; (
          exact h_foldl_le l c hc)
        generalize_proofs at *; (
        convert h_foldl_le using 1 ; simp +arith +decide [ List.take_succ ] ; ring!;
        cases l[c]? <;> simp +arith +decide [ * ] ; ring!;)
      generalize_proofs at *; (
      cases i_1 ; aesop ( simp_config := { decide := true } ) ;)
    generalize_proofs at *; (
    exact h_sum_eq.trans ( by linarith ))

noncomputable section AristotleLemmas

/-
If the sum of counts of a list of distinct values equals the size of the array, then the count of any value not in that list is 0.
-/
theorem count_eq_zero_of_counts_sum_eq_size {α : Type} [DecidableEq α] (arr : Array α) (vals : List α) (distinct : vals.Nodup) (h_sum : (vals.map (arr.count ·)).sum = arr.size) (x : α) (hx : x ∉ vals) : arr.count x = 0 := by
  contrapose! h_sum;
  refine' ne_of_lt ( lt_of_lt_of_le _ ( show arr.size ≥ ∑ y ∈ ({x} : Finset α) ∪ Finset.image ( fun y => y ) ( vals.toFinset ), Array.count y arr from _ ) ) <;> simp_all +decide [ Finset.sum_union ];
  · rw [ List.sum_toFinset ] ; exact lt_add_of_pos_left _ ( Nat.pos_of_ne_zero h_sum ) ;
    assumption;
  · have h_sum_le_size : ∀ (arr : Array α) (s : Finset α), (∑ x ∈ s, Array.count x arr) ≤ arr.size := by
      intros arr s; induction arr using Array.recOn ; simp_all +decide [ Finset.sum_add_distrib ] ;
      induction ‹List α› <;> simp_all +decide [ List.count_cons ];
      simp_all +decide [ Finset.sum_add_distrib ];
      split_ifs <;> simp_all +decide [ add_comm ] ; linarith;
      exact le_add_right ‹_›;
    convert h_sum_le_size arr ( { x } ∪ vals.toFinset ) using 1 ; aesop

end AristotleLemmas

theorem goal_9 (nums : Array ℤ) (require_1 : ∀ i < nums.size, -OfNat.ofNat 50000 ≤ nums[i]! ∧ nums[i]! ≤ OfNat.ofNat 50000) (i_1 : Array ℕ) (cIdx : ℕ) (out : Array ℤ) (invariant_rec_out_size : out.size = nums.size) (invariant_cnt_i_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1 ≤ nums.size) (invariant_rec_counts_size : i_1.size = OfNat.ofNat 100001) (invariant_rec_cIdx_le : cIdx ≤ OfNat.ofNat 100001) (if_pos : cIdx < OfNat.ofNat 100001) (invariant_cnt_size : i_1.size = OfNat.ofNat 100001) (done_1 : nums.size ≤ Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1) (invariant_cnt_hist : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → i_1[(v + OfNat.ofNat 50000).toNat]! = Array.count v (nums.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1))) (invariant_rec_outPos_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) ≤ out.size) (invariant_rec_prefix_sorted : ∀ (i j : ℕ), i < j → j < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) → j < out.size → (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ≤ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[j]!) (invariant_rec_prefix_range : ∀ i < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size), i < out.size → -OfNat.ofNat 50000 ≤ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ∧ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ≤ OfNat.ofNat 50000) (invariant_rec_prefix_counts_done : ∀ j < cIdx, Array.count (-OfNat.ofNat 50000 + j.cast) (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size))) = i_1[j]!) (invariant_rec_prefix_no_large : ∀ (v : ℤ), cIdx.cast < OfNat.ofNat 50000 + v → Array.count v (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size))) = OfNat.ofNat 0) : Array.count (-OfNat.ofNat 50000 + cIdx.cast) (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size))) = OfNat.ofNat 0 := by
    apply count_eq_zero_of_counts_sum_eq_size;
    any_goals exact List.map ( fun j : ℕ => -50000 + j ) ( List.range cIdx );
    · rw [ List.nodup_map_iff_inj_on ] ; aesop;
      exact?;
    · have h_sum : (List.map (fun j => i_1[j]!) (List.range cIdx)).sum = Array.foldl (fun s x => s + x) (OfNat.ofNat (OfNat.ofNat 0)) (i_1.extract (OfNat.ofNat (OfNat.ofNat 0)) cIdx) (OfNat.ofNat (OfNat.ofNat 0)) (Min.min cIdx i_1.size) := by
        have h_sum : ∀ (arr : Array ℕ) (cIdx : ℕ), cIdx ≤ arr.size → (List.map (fun j => arr[j]!) (List.range cIdx)).sum = Array.foldl (fun s x => s + x) (OfNat.ofNat (OfNat.ofNat 0)) (arr.extract (OfNat.ofNat (OfNat.ofNat 0)) cIdx) (OfNat.ofNat (OfNat.ofNat 0)) (Min.min cIdx arr.size) := by
          intros arr cIdx hcIdx; induction' cIdx with cIdx ih generalizing arr <;> simp +decide [ *, List.range_succ ] ;
          rw [ ih arr ( Nat.le_of_succ_le hcIdx ) ];
          rw [ show arr.extract 0 ( cIdx + 1 ) = arr.extract 0 cIdx ++ #[arr[cIdx]!] from ?_ ];
          · simp +decide [ Array.foldl_append, min_eq_left ( by linarith : cIdx ≤ arr.size ) ];
          · refine' Array.ext _ _ <;> simp +decide [ hcIdx ];
            · exact Nat.le_of_succ_le hcIdx;
            · intro i hi₁ hi₂; rcases lt_or_eq_of_le ( Nat.le_of_lt_succ hi₁ ) with hi | rfl <;> simp_all +decide [ Array.getElem_push ] ;
              · exact fun h => False.elim <| h.not_lt <| by linarith;
              · exact?;
        exact h_sum i_1 cIdx ( by linarith );
      convert h_sum using 1;
      · rw [ List.map_map ];
        exact congr_arg _ ( List.map_congr_left fun x hx => invariant_rec_prefix_counts_done x ( List.mem_range.mp hx ) );
      · aesop;
    · norm_num [ List.mem_map, List.mem_range ]

theorem goal_10 (nums : Array ℤ) (require_1 : ∀ i < nums.size, -OfNat.ofNat 50000 ≤ nums[i]! ∧ nums[i]! ≤ OfNat.ofNat 50000) (i_1 : Array ℕ) (cIdx : ℕ) (out : Array ℤ) (invariant_rec_out_size : out.size = nums.size) (i_4 : Array ℤ) (remaining_1 : ℕ) (invariant_cnt_i_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1 ≤ nums.size) (invariant_in_out_size : i_4.size = nums.size) (invariant_in_remaining_le : remaining_1 ≤ i_1[cIdx]!) (invariant_rec_counts_size : i_1.size = OfNat.ofNat 100001) (invariant_rec_cIdx_le : cIdx ≤ OfNat.ofNat 100001) (if_pos : cIdx < OfNat.ofNat 100001) (invariant_in_counts_size : i_1.size = OfNat.ofNat 100001) (invariant_in_cIdx_lt : cIdx < OfNat.ofNat 100001) (invariant_cnt_size : i_1.size = OfNat.ofNat 100001) (done_1 : nums.size ≤ Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1) (invariant_cnt_hist : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → i_1[(v + OfNat.ofNat 50000).toNat]! = Array.count v (nums.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1))) (invariant_rec_outPos_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) ≤ out.size) (invariant_rec_prefix_sorted : ∀ (i j : ℕ), i < j → j < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) → j < out.size → (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ≤ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[j]!) (invariant_rec_prefix_range : ∀ i < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size), i < out.size → -OfNat.ofNat 50000 ≤ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ∧ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ≤ OfNat.ofNat 50000) (invariant_rec_prefix_counts_done : ∀ j < cIdx, Array.count (-OfNat.ofNat 50000 + j.cast) (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size))) = i_1[j]!) (invariant_rec_prefix_no_large : ∀ (v : ℤ), cIdx.cast < OfNat.ofNat 50000 + v → Array.count v (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size))) = OfNat.ofNat 0) (done_3 : remaining_1 = OfNat.ofNat 0) (invariant_in_outPos_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining_1) ≤ i_4.size) (invariant_in_space : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining_1) + remaining_1 ≤ i_4.size) (invariant_in_prefix_sorted : ∀ (i j : ℕ), i < j → j < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining_1) → j < i_4.size → (i_4.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining_1)))[i]! ≤ (i_4.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining_1)))[j]!) (invariant_in_prefix_range : ∀ i < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining_1), i < i_4.size → -OfNat.ofNat 50000 ≤ (i_4.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining_1)))[i]! ∧ (i_4.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining_1)))[i]! ≤ OfNat.ofNat 50000) (invariant_in_prefix_counts_done : ∀ j < cIdx, Array.count (-OfNat.ofNat 50000 + j.cast) (i_4.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining_1))) = i_1[j]!) (invariant_in_prefix_counts_cur : Array.count (-OfNat.ofNat 50000 + cIdx.cast) (i_4.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining_1))) = i_1[cIdx]! - remaining_1) (invariant_in_prefix_no_large : ∀ (v : ℤ), cIdx.cast < OfNat.ofNat 50000 + v → Array.count v (i_4.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining_1))) = OfNat.ofNat 0) : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining_1) = Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) (cIdx + OfNat.ofNat 1)) (OfNat.ofNat 0) (min (cIdx + OfNat.ofNat 1) i_1.size) := by
    simp +zetaDelta at *;
    rw [ show i_1.extract 0 ( cIdx + 1 ) = i_1.extract 0 cIdx ++ #[i_1[cIdx]!] from ?_ ];
    · simp +decide [ Array.foldl_append, min_eq_left ( show cIdx + 1 ≤ i_1.size from by linarith ) ];
      simp +decide [ Array.foldl_push, min_eq_left ( show cIdx ≤ i_1.size from by linarith ) ];
      rw [ Nat.sub_eq_of_eq_add ] ; linarith [ show remaining_1 = 0 from by linarith ] ;
    · simp +zetaDelta at *;
      refine' Array.ext _ _ <;> simp +decide [ *, Array.getElem_push ]

theorem goal_11 (nums : Array ℤ) (require_1 : ∀ i < nums.size, -OfNat.ofNat 50000 ≤ nums[i]! ∧ nums[i]! ≤ OfNat.ofNat 50000) (i_1 : Array ℕ) (i_4 : ℕ) (i_5 : Array ℤ) (invariant_cnt_i_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1 ≤ nums.size) (invariant_rec_out_size : i_5.size = nums.size) (invariant_rec_counts_size : i_1.size = OfNat.ofNat 100001) (invariant_cnt_size : i_1.size = OfNat.ofNat 100001) (done_1 : nums.size ≤ Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1) (invariant_cnt_hist : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → i_1[(v + OfNat.ofNat 50000).toNat]! = Array.count v (nums.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1))) (invariant_rec_cIdx_le : i_4 ≤ OfNat.ofNat 100001) (done_2 : OfNat.ofNat 100001 ≤ i_4) (invariant_rec_outPos_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) i_4) (OfNat.ofNat 0) (min i_4 i_1.size) ≤ i_5.size) (invariant_rec_prefix_sorted : ∀ (i j : ℕ), i < j → j < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) i_4) (OfNat.ofNat 0) (min i_4 i_1.size) → j < i_5.size → (i_5.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) i_4) (OfNat.ofNat 0) (min i_4 i_1.size)))[i]! ≤ (i_5.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) i_4) (OfNat.ofNat 0) (min i_4 i_1.size)))[j]!) (invariant_rec_prefix_range : ∀ i < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) i_4) (OfNat.ofNat 0) (min i_4 i_1.size), i < i_5.size → -OfNat.ofNat 50000 ≤ (i_5.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) i_4) (OfNat.ofNat 0) (min i_4 i_1.size)))[i]! ∧ (i_5.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) i_4) (OfNat.ofNat 0) (min i_4 i_1.size)))[i]! ≤ OfNat.ofNat 50000) (invariant_rec_prefix_counts_done : ∀ j < i_4, Array.count (-OfNat.ofNat 50000 + j.cast) (i_5.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) i_4) (OfNat.ofNat 0) (min i_4 i_1.size))) = i_1[j]!) (invariant_rec_prefix_no_large : ∀ (v : ℤ), i_4.cast < OfNat.ofNat 50000 + v → Array.count v (i_5.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) i_4) (OfNat.ofNat 0) (min i_4 i_1.size))) = OfNat.ofNat 0) : postcondition nums i_5 := by
    -- By definition of `postcondition`, we need to show that `i_5` is sorted and has the same elements as `nums`.
    unfold postcondition;
    refine' ⟨ invariant_rec_out_size, _, _, _ ⟩;
    · -- Since the size of the extract is equal to the size of i_5, we can conclude that the entire array i_5 is sorted.
      have h_size_eq : (i_1.extract (0 : ℕ) i_4).foldl (fun s x => s + x) 0 + (i_1[i_4]!) = i_5.size := by
        -- Since `i_4` is equal to 100001, the extract is the entire array, and the sum is the same as the sum of the entire array.
        have h_i4_eq_100001 : i_4 = 100001 := by
          exact le_antisymm invariant_rec_cIdx_le done_2
        rw [h_i4_eq_100001] at *; simp_all +decide [ Array.sum ] ;
        rw [ show i_1.extract ( 0 : ℕ ) 100001 = i_1 from ?_ ] ; linarith!;
        simp +decide [ Array.ext_iff, invariant_cnt_size ];
      simp_all +decide [ show i_4 = 100001 by exact le_antisymm invariant_rec_cIdx_le done_2 ];
      -- Apply the invariant_rec_prefix_sorted hypothesis to conclude that i_5 is sorted.
      intros i j hij hlt
      by_cases hlt_i5 : j < i_5.size;
      · convert invariant_rec_prefix_sorted i j hij ( by linarith ) using 1;
        · simp +decide [ ← invariant_rec_out_size ];
        · grind;
      · exact False.elim <| hlt_i5 hlt;
    · intro i hi; specialize invariant_rec_prefix_range i; simp_all +decide [ Array.size_extract ] ;
      simp_all +decide [ show i_4 = 100001 by linarith ];
      by_cases hi' : i < Array.foldl ( fun s x => s + x ) 0 ( i_1.extract 0 100001 ) 0 100001 <;> simp_all +decide [ minVal, maxVal ];
      norm_num [ show i_1.extract 0 100001 = i_1 from by { exact Array.ext ( by aesop ) ( by aesop ) } ] at * ; linarith! [ invariant_cnt_i_le, invariant_rec_outPos_le, invariant_rec_prefix_no_large ] ;
    · intro v
      by_cases hv : -50000 ≤ v ∧ v ≤ 50000;
      · convert invariant_rec_prefix_counts_done ( Int.toNat ( v + 50000 ) ) ( by linarith [ Int.toNat_of_nonneg ( by linarith : 0 ≤ v + 50000 ) ] ) using 1;
        · rw [ show ( -50000 + ( v + 50000 |> Int.toNat |> Nat.cast ) : ℤ ) = v by linarith [ Int.toNat_of_nonneg ( by linarith : 0 ≤ v + 50000 ) ] ] ; simp +decide [ Array.count ] ; ring;
          rw [ show Array.foldl ( fun s x => s + x ) ( 0 : ℕ ) ( i_1.extract ( 0 : ℕ ) i_4 ) ( 0 : ℕ ) ( Min.min i_4 i_1.size ) = Array.foldl ( fun s x => s + x ) ( 0 : ℕ ) i_1 from ?_ ];
          · rw [ show Array.foldl ( fun s x => s + x ) ( 0 : ℕ ) i_1 = nums.size by linarith ] ; simp +decide [ Array.countP ] ; ring;
            simp +decide [ Array.size_extract, invariant_rec_out_size ];
            rw [ show i_5.extract ( 0 : ℕ ) nums.size = i_5 from ?_ ];
            simp +decide [ Array.ext_iff, invariant_rec_out_size ];
          · rw [ show i_4 = 100001 by linarith ] ; simp +decide [ invariant_cnt_size ] ;
            rw [ show i_1.extract 0 100001 = i_1 from ?_ ];
            simp +decide [ Array.ext_iff, invariant_cnt_size ];
        · convert invariant_cnt_hist v hv.1 hv.2 |> Eq.symm using 1;
          rw [ show Array.foldl ( fun s x => s + x ) ( OfNat.ofNat ( OfNat.ofNat 0 ) ) i_1 = nums.size from le_antisymm invariant_cnt_i_le done_1 ] ; simp +decide [ Array.count ] ;
      · rw [ Array.count_eq_zero_of_not_mem, Array.count_eq_zero_of_not_mem ] <;> simp_all +decide [ Array.mem_iff_getElem ];
        · exact fun i hi => fun hi' => by have := require_1 i hi; norm_num at *; linarith [ hv ( by linarith ) ] ;
        · -- Since $v$ is not in the range $[-50000, 50000]$, and $i_5[x]$ is in this range for all $x < nums.size$, it follows that $i_5[x] \neq v$.
          intros x hx
          have h_range : -50000 ≤ i_5[x] ∧ i_5[x] ≤ 50000 := by
            convert invariant_rec_prefix_range x _ hx using 1;
            convert hx using 1;
            -- Since `i_4` is equal to `100001`, and `i_1` has a size of `100001`, the extract of `i_1` up to `i_4` is just the entire array `i_1`.
            have h_extract : i_1.extract (OfNat.ofNat 0) i_4 = i_1 := by
              norm_num [ show i_4 = 100001 by linarith ] at * ; aesop ( simp_config := { singlePass := true } ) ;
            grind +ring
          exact ne_of_apply_ne (fun x => x) (by
          exact fun h => by have := hv ( by linarith ) ; norm_num at * ; linarith;)

end Proof