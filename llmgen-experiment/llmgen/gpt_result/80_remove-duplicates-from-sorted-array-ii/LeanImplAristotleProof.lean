import Lean

import Mathlib.Tactic

set_option maxHeartbeats 10000000

section Specs
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false

def countInPrefix (arr : Array Int) (k : Nat) (x : Int) : Nat :=
  (arr.take k).count x

def sortedPrefix (arr : Array Int) (k : Nat) : Prop :=
  ∀ (i : Nat), i + 1 < k → arr[i]! ≤ arr[i + 1]!

def precondition (nums : Array Int) : Prop :=
  sortedPrefix nums nums.size

def postcondition (nums : Array Int) (result : Nat × Array Int) : Prop :=
  let k : Nat := result.1
  let out : Array Int := result.2
  out.size = nums.size ∧
  k ≤ nums.size ∧
  sortedPrefix out k ∧
  (∀ (x : Int), countInPrefix out k x = Nat.min 2 (countInPrefix nums nums.size x))
end Specs

section Impl
def implementation (nums : Array Int) : Nat × Array Int :=
  let n := nums.size
  let rec go (i : Nat) (write : Nat) (last : Option Int) (cnt : Nat) (out : Array Int) :
      Nat × Array Int :=
    if h : i < n then
      let x : Int := nums[i]
      match last with
      | none =>
          go (i + 1) (write + 1) (some x) 1 (out.set! write x)
      | some l =>
          if x = l then
            if cnt < 2 then
              go (i + 1) (write + 1) (some l) (cnt + 1) (out.set! write x)
            else
              go (i + 1) write (some l) cnt out
          else
            go (i + 1) (write + 1) (some x) 1 (out.set! write x)
    else
      (write, out)
  termination_by nums.size - i
  let (k, out1) := go 0 0 none 0 nums
  let rec fillZero (j : Nat) (out : Array Int) : Array Int :=
    if h : j < n then
      fillZero (j + 1) (out.set! j (0 : Int))
    else
      out
  termination_by nums.size - j
  (k, fillZero k out1)
end Impl

section TestCases
def test1_nums : Array Int := #[1, 1, 1, 2, 2, 3]
def test1_Expected : Nat × Array Int := (5, #[1, 1, 2, 2, 3, 0])
def test2_nums : Array Int := #[0, 0, 1, 1, 1, 1, 2, 3, 3]
def test2_Expected : Nat × Array Int := (7, #[0, 0, 1, 1, 2, 3, 3, 0, 0])
def test3_nums : Array Int := #[]
def test3_Expected : Nat × Array Int := (0, #[])
def test4_nums : Array Int := #[7]
def test4_Expected : Nat × Array Int := (1, #[7])
def test5_nums : Array Int := #[2, 2, 2, 2]
def test5_Expected : Nat × Array Int := (2, #[2, 2, 0, 0])
def test6_nums : Array Int := #[1, 1, 2, 2, 3, 3]
def test6_Expected : Nat × Array Int := (6, #[1, 1, 2, 2, 3, 3])
def test7_nums : Array Int := #[-1, -1, -1, 0, 0, 0, 1]
def test7_Expected : Nat × Array Int := (5, #[-1, -1, 0, 0, 1, 0, 0])
def test8_nums : Array Int := #[0, 1, 2]
def test8_Expected : Nat × Array Int := (3, #[0, 1, 2])
def test9_nums : Array Int := #[0, 0, 0, 1, 1, 2, 2, 2, 2, 3]
def test9_Expected : Nat × Array Int := (7, #[0, 0, 1, 1, 2, 2, 3, 0, 0, 0])
end TestCases

section Helpers

lemma extract_set!_push (out : Array ℤ) (k : ℕ) (v : ℤ) (hk : k < out.size) :
    (out.set! k v).extract 0 (k + 1) = (out.extract 0 k).push v := by
  grind +ring

lemma extract_succ' (arr : Array ℤ) (i : ℕ) (hi : i < arr.size) :
    arr.extract 0 (i + 1) = (arr.extract 0 i).push arr[i] := by
  grind +ring

lemma getElem!_set!_self (out : Array ℤ) (k : ℕ) (v : ℤ) (hk : k < out.size) :
    (out.set! k v)[k]! = v := by
  cases out ; aesop

lemma getElem!_set!_ne (out : Array ℤ) (k j : ℕ) (v : ℤ) (hne : j ≠ k) :
    (out.set! k v)[j]! = out[j]! := by
  grind +ring

lemma sorted_le_of_le (nums : Array ℤ) (j i : ℕ)
    (h_sorted : ∀ k, k + 1 < nums.size → nums[k]! ≤ nums[k + 1]!)
    (hj : j ≤ i) (hi : i < nums.size) :
    nums[j]! ≤ nums[i]! := by
  induction' hj with k hk ih
  · rfl
  · exact le_trans (ih (Nat.lt_of_succ_lt hi)) (h_sorted _ hi)

lemma size_set! (out : Array ℤ) (k : ℕ) (v : ℤ) :
    (out.set! k v).size = out.size := by
  simp +zetaDelta at *

lemma elem_in_prefix_le (nums out : Array ℤ) (i write j : ℕ)
    (h_nums_sorted : ∀ k, k + 1 < nums.size → nums[k]! ≤ nums[k + 1]!)
    (hcounts : ∀ x, Array.count x (out.extract 0 write) = Nat.min 2 (Array.count x (nums.extract 0 i)))
    (hj : j < write)
    (hwrite_le_i : write ≤ i)
    (hi : i < nums.size)
    (hout_size : out.size = nums.size) :
    out[j]! ≤ nums[i]! := by
  have hcount_ge_one : (nums.extract 0 i).count (out[j]!) ≥ 1 := by
    have hcount_ge_one : (out.extract 0 write).count (out[j]!) ≥ 1 := by
      simp +zetaDelta at *
      rw [Array.mem_def, List.mem_iff_get]
      use ⟨j, by grind⟩
      generalize_proofs at *
      grind
    grind +ring
  contrapose! hcount_ge_one
  rw [Array.count_eq_zero.mpr]; aesop
  have h_not_in_range : ∀ k < i, nums[k]! < out[j]! := by
    intro k hk_lt_i; exact lt_of_le_of_lt (sorted_le_of_le nums k i h_nums_sorted (by linarith) (by linarith)) hcount_ge_one
  rw [Array.mem_def, List.mem_iff_get]
  grind

end Helpers

section Proof

/-- The full loop invariant predicate for go -/
structure GoInv (nums : Array ℤ) (i write : ℕ) (last : Option ℤ) (cnt : ℕ) (out : Array ℤ) : Prop where
  hi : i ≤ nums.size
  hout_size : out.size = nums.size
  hwrite_le_i : write ≤ i
  hsorted : ∀ j, j + 1 < write → out[j]! ≤ out[j + 1]!
  hcounts : ∀ x, Array.count x (out.extract 0 write) = Nat.min 2 (Array.count x (nums.extract 0 i))
  hlast_none : last = none → write = 0
  hlast_some : ∀ l, last = some l → write > 0 ∧ out[write - 1]! = l
  hcnt_range : last = none ∧ cnt = 0 ∨ ∃ l, last = some l ∧ 1 ≤ cnt ∧ cnt ≤ 2 ∧
    cnt = Array.count l (out.extract 0 write) ∧
    (∀ j, j < write → out[j]! = l → j ≥ write - cnt)
  hwrite_sorted_last : ∀ l, last = some l → ∀ j, j < write → out[j]! ≤ l

/-
PROBLEM
Case 1: last = none (first element)

PROVIDED SOLUTION
Since last = none, by inv.hlast_none, write = 0. So we're at the start.
After set! 0 nums[i], we have write' = 1, last' = some nums[i], cnt' = 1, out' = out.set! 0 nums[i].

Verify each field of GoInv:
- hi: i + 1 ≤ nums.size follows from h_lt
- hout_size: size_set! preserves size
- hwrite_le_i: 1 ≤ i + 1, trivial
- hsorted: write' = 1, so j + 1 < 1 is impossible, nothing to prove
- hcounts: For any x, count x (out'.extract 0 1) = count x (#[nums[i]]) = (if x = nums[i] then 1 else 0).
  Also nums.extract 0 (i+1) = (nums.extract 0 i).push nums[i] by extract_succ'.
  Since write = 0, count x (out.extract 0 0) = 0 = min(2, count x (nums.extract 0 i)) by inv.hcounts, so count x (nums.extract 0 i) = 0. Then min(2, count x (nums.extract 0 (i+1))) = min(2, 0 + if x=nums[i] then 1 else 0) = if x=nums[i] then 1 else 0. This matches.
  Use extract_set!_push with k=0 to get the extract as push.
- hlast_none: last' = some nums[i], so the implication is vacuously true
- hlast_some: l = nums[i], write' = 1 > 0, out'[0]! = nums[i] by getElem!_set!_self
- hcnt_range: Right disjunct with l = nums[i], cnt' = 1, count nums[i] in out'.extract 0 1 = 1, and for j < 1 with out'[j]! = nums[i], j = 0 ≥ 1 - 1 = 0
- hwrite_sorted_last: for j < 1, out'[j]! = nums[i] ≤ nums[i]
-/
lemma go_case_none (nums : Array ℤ) (i write cnt : ℕ) (out : Array ℤ)
    (h_lt : i < nums.size)
    (h_precond : precondition nums)
    (inv : GoInv nums i write none cnt out) :
    GoInv nums (i + 1) (write + 1) (some nums[i]) 1 (out.set! write nums[i]) := by
  rcases write <;> simp_all +decide [ GoInv ];
  · rcases inv with ⟨ hi, hout_size, hwrite_le_i, hsorted, hcounts, hlast_none, hlast_some, hcnt_range, hwrite_sorted_last ⟩;
    constructor <;> norm_num <;> try linarith;
    · -- Since the extract is just the first element, the count should be 1 if x is nums[i], and 0 otherwise.
      have h_count : ∀ x, Array.count x ((out.setIfInBounds 0 nums[i]).extract 0 1) = if x = nums[i] then 1 else 0 := by
        rcases out with ⟨ ⟨ l ⟩ ⟩ <;> simp_all +decide [ Array.count ];
        · linarith;
        · grind;
      intro x; rw [ h_count ] ; split_ifs <;> simp_all +decide [ Nat.min_eq_left ] ;
      · rw [ show nums.extract 0 ( i + 1 ) = ( nums.extract 0 i ).push nums[i] from ?_, Array.count_push ] ; norm_num [ h_lt ];
        · grind +ring;
        · exact?;
      · rw [ show nums.extract 0 ( i + 1 ) = ( nums.extract 0 i ).push nums[i] from ?_, Array.count_push ] ; aesop;
        exact?;
    · tauto;
    · grind;
    · grind;
    · grind;
  · cases inv ; aesop

/-
PROBLEM
Case 2: last = some (nums[i]), x = l, cnt < 2

PROVIDED SOLUTION
We have last = some nums[i] (i.e., x = l = nums[i]), cnt < 2, and we set out' = out.set! write nums[i], incrementing write and cnt.

From inv, obtain all fields. Since last = some nums[i], by inv.hlast_some we have write > 0 and out[write-1]! = nums[i].

Verify each field:
- hi: i + 1 ≤ nums.size from h_lt
- hout_size: by size_set!
- hwrite_le_i: write + 1 ≤ i + 1 follows from write ≤ i (inv.hwrite_le_i)
- hsorted: For j + 1 < write + 1. If j + 1 < write, use inv.hsorted + getElem!_set!_ne (both indices < write ≤ k). If j + 1 = write (i.e., j = write - 1), then out'[write-1]! = out[write-1]! = nums[i] (by hlast_some and getElem!_set!_ne since write-1 ≠ write), and out'[write]! = nums[i] (by getElem!_set!_self). So out'[write-1]! ≤ out'[write]!.
- hcounts: Use extract_set!_push and extract_succ'. count x (old.push nums[i]) should equal min(2, count x (old_nums.push nums[i])). This follows from inv.hcounts and the fact that we're adding one more copy of nums[i] to both sides. The key is: old_count_out = min(2, old_count_in). If x = nums[i], new_out = old_out + 1 and new_in = old_in + 1. Since cnt < 2 and cnt = count nums[i] in the old out prefix (by hcnt_range), old_out ≤ 1, so old_out = min(2, old_in) ≤ 1, meaning old_in ≤ 1. Then min(2, old_in + 1) = old_in + 1 = old_out + 1. If x ≠ nums[i], both sides unchanged.
- hlast_none: vacuously true
- hlast_some: l = nums[i], write + 1 > 0, out'[(write+1)-1]! = out'[write]! = nums[i] by getElem!_set!_self
- hcnt_range: Right disjunct with l = nums[i], cnt' = cnt + 1. cnt + 1 ≤ 2 (since cnt < 2). count nums[i] in out'.extract 0 (write+1) = count nums[i] in (out.extract 0 write).push nums[i] = count + 1 = cnt + 1. For the position bound: if j < write+1 and out'[j]! = nums[i], then j ≥ (write+1) - (cnt+1) = write - cnt.
- hwrite_sorted_last: for j < write+1, out'[j]! ≤ nums[i]. For j < write, out'[j]! = out[j]! (by getElem!_set!_ne) ≤ nums[i] (by inv.hwrite_sorted_last). For j = write, out'[write]! = nums[i].
-/
lemma go_case_same_lt2 (nums : Array ℤ) (i write cnt : ℕ) (out : Array ℤ)
    (h_lt : i < nums.size)
    (hcnt_lt : cnt < 2)
    (h_precond : precondition nums)
    (inv : GoInv nums i write (some nums[i]) cnt out) :
    GoInv nums (i + 1) (write + 1) (some nums[i]) (cnt + 1) (out.set! write nums[i]) := by
  obtain ⟨ hi, hout_size, hwrite_le_i, hsorted, hcounts, hlast_none, hlast_some, hcnt_range, hwrite_sorted_last ⟩ := inv;
  -- Verify each field of the GoInv structure.
  apply GoInv.mk;
  any_goals simp +arith +decide [ * ];
  · grind +ring;
  · -- By definition of `extract_set!_push`, we can rewrite the left-hand side of the equation.
    have h_extract_push : (out.set! write nums[i]).extract 0 (write + 1) = (out.extract 0 write).push nums[i] := by
      grind;
    simp_all +decide [ Array.count_push ];
    intro x; split_ifs <;> simp_all +decide [ Array.count_push ] ;
    · rw [ show Array.count x ( nums.extract 0 ( i + 1 ) ) = Array.count x ( nums.extract 0 i ) + 1 from ?_ ];
      · interval_cases Array.count x ( nums.extract 0 i ) <;> trivial;
      · rw [ show nums.extract 0 ( i + 1 ) = nums.extract 0 i ++ #[nums[i]] from ?_, Array.count_append ] <;> aesop;
    · rw [ show nums.extract 0 ( i + 1 ) = ( nums.extract 0 i ).push nums[i] from ?_, Array.count_push ] ; aesop;
      exact?;
  · grind +ring;
  · constructor;
    · rw [ show ( out.setIfInBounds write nums[i] ).extract 0 ( write + 1 ) = ( out.extract 0 write ).push nums[i] from ?_, Array.count_push ] ; aesop;
      grind;
    · intro j hj hj'; rcases hj.eq_or_lt with rfl | hj' <;> simp_all +decide [ Array.setIfInBounds ] ;
      grind +ring;
  · intro l hl j hj; rcases lt_or_eq_of_le ( Nat.le_of_lt_succ hj ) with hj' | rfl <;> simp_all +decide ;
    · grind +ring;
    · grind +ring

/-
PROBLEM
Case 3: last = some (nums[i]), x = l, cnt ≥ 2

PROVIDED SOLUTION
We have last = some nums[i] (x = l = nums[i]), cnt ≥ 2, and we skip (no write, no set).

From inv, obtain all fields. Since last = some nums[i], by hcnt_range, cnt = count nums[i] (out.extract 0 write) and cnt ≤ 2, so cnt = 2.

Verify each field:
- hi: i + 1 ≤ nums.size from h_lt
- hout_size: unchanged
- hwrite_le_i: write ≤ i ≤ i + 1
- hsorted: unchanged
- hcounts: For any x, need count x (out.extract 0 write) = min(2, count x (nums.extract 0 (i+1))).
  By extract_succ', nums.extract 0 (i+1) = (nums.extract 0 i).push nums[i].
  count x (push) = count x (old) + if nums[i] == x then 1 else 0.
  Case x = nums[i]: old_count_out = min(2, old_count_in). cnt = 2, so old_count_out = 2 (since cnt = count nums[i] in out prefix). min(2, old_count_in + 1) = 2 since old_count_in ≥ 2 (because min(2, old_count_in) = 2). So 2 = 2.
  Case x ≠ nums[i]: count unchanged, same as before.
- hlast_none: vacuously true
- hlast_some: same as before (out unchanged)
- hcnt_range: same as before (cnt, out, write unchanged, last unchanged to some nums[i])
- hwrite_sorted_last: same as before
-/
lemma go_case_same_ge2 (nums : Array ℤ) (i write cnt : ℕ) (out : Array ℤ)
    (h_lt : i < nums.size)
    (hcnt_ge : ¬ cnt < 2)
    (h_precond : precondition nums)
    (inv : GoInv nums i write (some nums[i]) cnt out) :
    GoInv nums (i + 1) write (some nums[i]) cnt out := by
  obtain ⟨ hi, hout_size, hwrite_le_i, hsorted, hcounts, hlast_none, hlast_some, hcnt_range, hwrite_sorted_last ⟩ := inv;
  refine' ⟨ by linarith, hout_size, by linarith, hsorted, _, _, _, _, _ ⟩;
  · have h_push : nums.extract 0 (i + 1) = (nums.extract 0 i).push nums[i] := by
      exact?;
    grind;
  · tauto;
  · exact hlast_some;
  · exact hcnt_range;
  · exact hwrite_sorted_last

/-
PROBLEM
Case 4: last = some l, x ≠ l

PROVIDED SOLUTION
We have last = some l, nums[i] ≠ l, and we set out' = out.set! write nums[i], with write' = write+1, last' = some nums[i], cnt' = 1.

From inv, obtain all fields. Since last = some l, by inv.hlast_some, write > 0 and out[write-1]! = l.

Key insight: Since nums is sorted and nums[i] ≠ l, and all elements in the output prefix are ≤ l (by hwrite_sorted_last), and l ≤ nums[i] (because l appears in nums.extract 0 i, so l ≤ nums[i] by sortedness), we get l < nums[i].

Also, since the input is sorted and l appears in nums.extract 0 i, every element in the output is ≤ l < nums[i], so nums[i] is strictly greater than all output prefix elements.

Verify each field:
- hi: i + 1 ≤ nums.size from h_lt
- hout_size: by size_set!
- hwrite_le_i: write + 1 ≤ i + 1
- hsorted: For j + 1 < write + 1. If j + 1 < write, use inv.hsorted + getElem!_set!_ne. If j + 1 = write, out'[write-1]! = out[write-1]! = l (using getElem!_set!_ne since write-1 ≠ write when write > 0) and out'[write]! = nums[i] (getElem!_set!_self). Since l ≤ nums[i] (as argued), out'[write-1]! ≤ out'[write]!.
- hcounts: Use extract_set!_push and extract_succ'. For x ≠ nums[i]: both sides get same increment (0). For x = nums[i]: new_out = old_out + 1, new_in = old_in + 1. Since nums[i] > l and all output elements ≤ l, count nums[i] in old output = 0. So old_out = 0 = min(2, old_in), meaning old_in = 0. Then new_out = 1 = min(2, 1) = min(2, old_in + 1).
- hlast_none: vacuously true
- hlast_some: l' = nums[i], write + 1 > 0, out'[write]! = nums[i] by getElem!_set!_self
- hcnt_range: cnt' = 1, count nums[i] in out'.extract 0 (write+1) = count in (out.extract 0 write).push nums[i] = 0 + 1 = 1. Position bound: only j = write has out'[j]! = nums[i], and write ≥ (write+1) - 1 = write.
- hwrite_sorted_last: for j < write+1, out'[j]! ≤ nums[i]. For j < write, out'[j]! = out[j]! ≤ l < nums[i]. For j = write, out'[write]! = nums[i].
-/
lemma go_case_diff (nums : Array ℤ) (i write cnt : ℕ) (l : ℤ) (out : Array ℤ)
    (h_lt : i < nums.size)
    (hne : ¬ nums[i] = l)
    (h_precond : precondition nums)
    (inv : GoInv nums i write (some l) cnt out) :
    GoInv nums (i + 1) (write + 1) (some nums[i]) 1 (out.set! write nums[i]) := by
  -- Let's unfold the definition of `GoInv` to work with the individual components.
  obtain ⟨hwrite_le_i, hsorted, hcounts, hlast_none, hlast_some, hcnt_range, hwrite_sorted_last⟩ := inv;
  -- Since `nums[i]` is greater than all elements in the output prefix, we have `nums[i] > l`.
  have h_gt : nums[i] > l := by
    -- Since `l` is in the output prefix, there exists some `j < write` such that `out[j]! = l`.
    obtain ⟨j, hj₁, hj₂⟩ : ∃ j < write, out[j]! = l := by
      grind +ring;
    -- Since `out[j]! = l` and `out` is a prefix of `nums`, we have `l ≤ nums[i]`.
    have h_le : out[j]! ≤ nums[i] := by
      convert elem_in_prefix_le nums out i write j h_precond hlast_some hj₁ hcounts h_lt hsorted using 1;
      exact?;
    exact lt_of_le_of_ne ( by linarith ) ( Ne.symm hne );
  constructor <;> simp +decide [ * ];
  · grind;
  · intro x
    have h_count_eq : Array.count x ((out.setIfInBounds write nums[i]).extract 0 (write + 1)) = Array.count x ((out.extract 0 write).push nums[i]) := by
      rw [ show ( out.setIfInBounds write nums[i] ).extract 0 ( write + 1 ) = ( out.extract 0 write ).push nums[i] from ?_ ];
      grind +ring
    have h_count_eq' : Array.count x (nums.extract 0 (i + 1)) = Array.count x ((nums.extract 0 i).push nums[i]) := by
      rw [ show nums.extract 0 ( i + 1 ) = ( nums.extract 0 i ).push nums[i] from ?_ ] ; aesop;
    simp [h_count_eq, h_count_eq'] at *;
    by_cases hx : x = nums[i] <;> simp +decide [ hx, Array.count_push ];
    · have h_count_zero : Array.count nums[i] (out.extract 0 write) = 0 := by
        rw [ Array.count_eq_zero ];
        intro H; have := Array.mem_iff_getElem.mp H; obtain ⟨ j, hj ⟩ := this; simp_all +decide [ Array.getElem_extract ] ;
        grind +ring;
      rw [ show nums.extract 0 ( i + 1 ) = ( nums.extract 0 i ).push nums[i] from ?_, Array.count_push ] ; aesop;
      exact?;
    · rw [ show nums.extract 0 ( i + 1 ) = ( nums.extract 0 i ).push nums[i] from ?_, Array.count_push ] ; aesop;
      exact?;
  · grind +ring;
  · constructor;
    · rw [ eq_comm, Array.count ];
      rw [ show ( out.setIfInBounds write nums[i] ).extract 0 ( write + 1 ) = ( out.extract 0 write ).push nums[i] from ?_ ];
      · simp +decide [ Array.countP_push ];
        intro a ha; contrapose! h_gt; simp_all +decide [ Array.mem_iff_getElem ] ;
        grind;
      · grind +ring;
    · grind;
  · intro j hj; by_cases hj' : j < write <;> simp_all +decide [ Array.setIfInBounds ] ;
    · grind;
    · grind

/-
PROBLEM
Main invariant: assembles all cases using implementation.go.induct

PROVIDED SOLUTION
Use implementation.go.induct on nums. In each case:
- case5 (i ≥ n): unfold go, simplify with dif_neg. Return (write, out). Properties follow from inv (hcounts at i = nums.size means nums.extract 0 i = nums).
- case1 (last = none): Apply the IH to go_case_none result.
- case2 (x = l, cnt < 2): Apply the IH to go_case_same_lt2 result.
- case3 (x = l, cnt ≥ 2): Apply the IH to go_case_same_ge2 result.
- case4 (x ≠ l): Apply the IH to go_case_diff result.

The key challenge is that after the induction, the context has let-bound variables from the function definition. Specifically, h_lt is `ℕ := nums.size` (a let binding for `n`), and the hypothesis names from the induction may have inaccessible names. Use `change` or `show` to fix type mismatches.

For unfolding go one step, use `unfold implementation.go` which produces a `let n := nums.size; if h : i < n then ...`. Then use `dsimp only` to beta-reduce let bindings, and `split_ifs` or `dif_pos/dif_neg` to simplify the conditionals.

For each case, the IH has the form `GoInv ... → (result properties)`, so just apply it to the appropriate go_case lemma result.
-/
lemma go_invariant (nums : Array ℤ)
    (h_precond : precondition nums)
    (i write : ℕ) (last : Option ℤ) (cnt : ℕ) (out : Array ℤ)
    (inv : GoInv nums i write last cnt out) :
    let result := implementation.go nums i write last cnt out
    result.2.size = nums.size ∧
    write ≤ result.1 ∧
    result.1 ≤ nums.size ∧
    (∀ j, j + 1 < result.1 → result.2[j]! ≤ result.2[j + 1]!) ∧
    (∀ x, Array.count x (result.2.extract 0 result.1) = Nat.min 2 (Array.count x nums)) := by
  induction' n : nums.size - i using Nat.strong_induction_on with n ih generalizing i write last cnt out inv h_precond;
  by_cases hi : i < nums.size;
  · rcases last with ( _ | l ) <;> simp_all +decide [ Nat.sub_add_cancel hi.le ];
    · -- Apply the go_case_none lemma to handle the case where the last element is none.
      have h_case_none : GoInv nums (i + 1) (write + 1) (some nums[i]) 1 (out.set! write nums[i]) := by
        exact?;
      rw [ show ( implementation.go nums i write none cnt out ) = ( implementation.go nums ( i + 1 ) ( write + 1 ) ( some nums[i] ) 1 ( out.set! write nums[i] ) ) from ?_ ];
      · grind;
      · rw [ implementation.go ];
        aesop;
    · by_cases hne : nums[i] = l;
      · by_cases hcnt : cnt < 2;
        · specialize ih ( nums.size - ( i + 1 ) ) ( by omega ) ( i + 1 ) ( write + 1 ) ( some l ) ( cnt + 1 ) ( out.set! write l ) ; simp_all +decide [ Nat.sub_add_comm hi.le ];
          unfold implementation.go; simp +decide [ * ] ;
          exact ⟨ ih ( by
            convert go_case_same_lt2 nums i write cnt out hi hcnt h_precond _ using 1;
            · rw [ hne ];
            · grind;
            · aesop ) |>.1, by linarith [ ih ( by
            convert go_case_same_lt2 nums i write cnt out hi hcnt h_precond _ using 1;
            · rw [ hne ];
            · grind;
            · aesop ) |>.2.1 ], by linarith [ ih ( by
            convert go_case_same_lt2 nums i write cnt out hi hcnt h_precond _ using 1;
            · rw [ hne ];
            · grind;
            · aesop ) |>.2.2.1 ], by simpa using ih ( by
            convert go_case_same_lt2 nums i write cnt out hi hcnt h_precond _ using 1;
            · rw [ hne ];
            · grind;
            · aesop ) |>.2.2.2.1, by simpa using ih ( by
            convert go_case_same_lt2 nums i write cnt out hi hcnt h_precond _ using 1;
            · rw [ hne ];
            · grind;
            · aesop ) |>.2.2.2.2 ⟩;
        · convert ih ( nums.size - ( i + 1 ) ) _ ( i + 1 ) write ( some l ) cnt out _ _ using 1;
          · rw [ implementation.go ];
            grind;
          · rw [ show implementation.go nums i write ( some l ) cnt out = ( implementation.go nums ( i + 1 ) write ( some l ) cnt out ) from ?_ ];
            rw [ implementation.go ];
            aesop;
          · omega;
          · convert go_case_same_ge2 nums i write cnt out hi hcnt h_precond _ using 1;
            · rw [ hne ];
            · aesop;
          · rfl;
      · have := go_case_diff nums i write cnt l out hi hne h_precond inv;
        unfold implementation.go; simp +decide [ hi, this ] ;
        grind;
  · unfold implementation.go; simp +decide [ hi ] ;
    refine' ⟨ inv.hout_size, _, _, _ ⟩;
    · linarith [ inv.hwrite_le_i, inv.hi ];
    · exact inv.hsorted;
    · convert inv.hcounts using 1;
      rw [ show nums.extract 0 i = nums from _ ];
      grind

theorem correctness_goal_0_2 (nums : Array ℤ) (h_precond : precondition nums) (k : ℕ) (out1 : Array ℤ) (hgo_res : implementation.go nums 0 0 none 0 nums = (k, out1)) (h_size : out1.size = nums.size) (h_k_le : k ≤ nums.size) : ∀ (i : ℕ), i + 1 < k → out1[i]! ≤ out1[i + 1]! := by
    have hinv : GoInv nums 0 0 none 0 nums := ⟨by omega, rfl, le_refl _, by omega, by simp, by simp, by simp, by left; exact ⟨rfl, rfl⟩, by simp⟩
    have := go_invariant nums h_precond 0 0 none 0 nums hinv
    simp [hgo_res] at this
    exact this.2.2.1

theorem correctness_goal_0_3 (nums : Array ℤ) (h_precond : precondition nums) (k : ℕ) (out1 : Array ℤ) (hgo_res : implementation.go nums 0 0 none 0 nums = (k, out1)) (h_size : out1.size = nums.size) (h_k_le : k ≤ nums.size) (h_sorted : ∀ (i : ℕ), i + 1 < k → out1[i]! ≤ out1[i + 1]!) : ∀ (x : ℤ), Array.count x (out1.extract 0 k) = Nat.min 2 (Array.count x nums) := by
    have hinv : GoInv nums 0 0 none 0 nums := ⟨by omega, rfl, le_refl _, by omega, by simp, by simp, by simp, by left; exact ⟨rfl, rfl⟩, by simp⟩
    have := go_invariant nums h_precond 0 0 none 0 nums hinv
    simp [hgo_res] at this
    exact this.2.2.2

end Proof