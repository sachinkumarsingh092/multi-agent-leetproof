/- This file type checks in Lean 4.28 -/

import Lean

import Mathlib

set_option maxHeartbeats 10000000

section Specs
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false

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
def implementation (nums : Array Int) : Int :=
  -- Kadane's algorithm: O(n) time, O(1) space
  -- We use foldl with accumulator (currentEndingHere, maxSoFar)
  -- Initialize with the first element
  let first := nums[0]!
  let (_, globalMax) := nums.foldl (fun (acc : Int × Int) (x : Int) =>
    let (currentMax, globalMax) := acc
    let newCurrent := max x (currentMax + x)
    let newGlobal := max globalMax newCurrent
    (newCurrent, newGlobal)
  ) (first, first) 1
  globalMax
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

section Proof

lemma foldl_add_shift (arr : Array ℤ) (init : ℤ) : arr.foldl (fun acc x => acc + x) init = init + arr.foldl (fun acc x => acc + x) 0 := by
  have h := @Array.foldl_toList ℤ ℤ (fun acc x => acc + x) init arr
  rw [← h]
  have h2 := @Array.foldl_toList ℤ ℤ (fun acc x => acc + x) 0 arr
  rw [← h2]
  have h_assoc : ∀ (l : List ℤ) (init : ℤ), List.foldl (fun acc x => acc + x) init l = init + List.foldl (fun acc x => acc + x) 0 l := by
    intro l init; induction' l using List.reverseRecOn with l ih; aesop;
    grind +ring;
  apply h_assoc

/-! ## Helper definitions and lemmas for Kadane's algorithm correctness -/

/-- The Kadane step function: given (currentMax, globalMax) and a new element x,
    compute the new (currentMax, globalMax). -/
def kadStep (p : ℤ × ℤ) (x : ℤ) : ℤ × ℤ :=
  (max x (p.1 + x), max p.2 (max x (p.1 + x)))

/-
PROBLEM
The fold function used in the theorem is definitionally equal to kadStep.

PROVIDED SOLUTION
Destruct p as (a, b), then unfold kadStep and simplify. The two expressions are definitionally equal.
-/
lemma fold_fn_eq_kadStep (p : ℤ × ℤ) (x : ℤ) :
    (Prod.casesOn p fun fst snd =>
      (fun currentMax globalMax =>
          let newCurrent := max x (currentMax + x);
          let newGlobal := max globalMax newCurrent;
          (newCurrent, newGlobal))
        fst snd) = kadStep p x := by
  rfl

/-- Sum of a segment of a list: segSum l i j = sum of l[i..j). -/
def segSum (l : List ℤ) (i j : Nat) : ℤ :=
  ((l.drop i).take (j - i)).sum

/-
PROBLEM
arraySum equals List.sum of the underlying list.

PROVIDED SOLUTION
Unfold arraySum, use Array.foldl_toList to convert to list foldl, then show List.foldl (fun acc x => acc + x) 0 l = l.sum by induction on l (or use foldl_add_shift and List.sum definition).
-/
lemma arraySum_eq_list_sum (arr : Array ℤ) :
    arraySum arr = arr.toList.sum := by
  unfold arraySum;
  rw [ List.sum_eq_foldl ];
  exact?

/-
PROBLEM
rangeSum equals segSum on the underlying list.

PROVIDED SOLUTION
Unfold rangeSum, segSum, arraySum. Use arraySum_eq_list_sum and the fact that Array.extract corresponds to List.drop/take. Specifically, (nums.extract i j).toList = (nums.toList.drop i).take (j - i).
-/
lemma rangeSum_eq_segSum (nums : Array ℤ) (i j : Nat) :
    rangeSum nums i j = segSum nums.toList i j := by
  unfold rangeSum segSum;
  rw [ arraySum_eq_list_sum, Array.toList_extract ]

/-
PROBLEM
Extending a segment sum by one element.
    segSum l j (n+2) = segSum l j (n+1) + segSum l (n+1) (n+2)
    when j ≤ n+1.

PROVIDED SOLUTION
Unfold segSum. We need to show that (l.drop j).take (n+2-j) has sum equal to (l.drop j).take (n+1-j) sum + (l.drop (n+1)).take 1 sum. Since j ≤ n+1 and n+1 < l.length, we have n+2-j = (n+1-j) + 1. The key is that (l.drop j).take ((n+1-j)+1) = (l.drop j).take (n+1-j) ++ [(l.drop j)[n+1-j]] when n+1-j < (l.drop j).length. And (l.drop j)[n+1-j] = l[n+1]. Then use List.sum_append. Also note that segSum l (n+1) (n+2) = ((l.drop (n+1)).take 1).sum.
-/
lemma segSum_append (l : List ℤ) (j n : Nat) (hj : j ≤ n + 1) (hn : n + 1 < l.length) :
    segSum l j (n + 2) = segSum l j (n + 1) + segSum l (n + 1) (n + 2) := by
  -- By definition of `segSum`, we can split the sum into two parts.
  simp [segSum];
  simp +arith +decide [ Nat.succ_sub hj, List.take_add_one ];
  rw [ add_tsub_cancel_of_le hj ]

/-
PROBLEM
A single-element segment sum.

PROVIDED SOLUTION
Unfold segSum. We need ((l.drop i).take 1).sum = l[i]. Since i < l.length, l.drop i is non-empty, so (l.drop i).take 1 = [(l.drop i).head] = [l[i]]. Then the sum of a singleton list is just that element.
-/
lemma segSum_single (l : List ℤ) (i : Nat) (hi : i < l.length) :
    segSum l i (i + 1) = l[i] := by
  unfold segSum; aesop;

/-
PROBLEM
The Array.foldl over an array equals List.foldl over its list.

PROVIDED SOLUTION
Use Array.foldl_toList.
-/
lemma array_foldl_eq_list_foldl (f : ℤ × ℤ → ℤ → ℤ × ℤ) (init : ℤ × ℤ) (arr : Array ℤ) :
    Array.foldl f init arr = arr.toList.foldl f init := by
  grind

/-
PROBLEM
nums[0]! equals nums.toList.head! for a non-empty array

PROVIDED SOLUTION
For a non-empty array, nums[0]! = nums.toList[0]! = nums.toList.head!. Use the relationship between Array.get!, List.get!, and List.head!.
-/
lemma array_get_zero_eq_head (nums : Array ℤ) (h : nums.size > 0) :
    nums[0]! = nums.toList.head! := by
  rcases nums with ⟨ ⟨ l ⟩ ⟩ <;> aesop

/-
PROBLEM
The extract of an array starting at index 1 corresponds to the tail of the list.

PROVIDED SOLUTION
Show that (nums.extract 1).toList = nums.toList.drop 1 = nums.toList.tail. Use Array.toList_extract and the fact that List.drop 1 = List.tail.
-/
lemma array_extract_one_eq_tail (nums : Array ℤ) :
    (nums.extract 1).toList = nums.toList.tail := by
  cases nums ; aesop

/-
PROBLEM
The Kadane invariant.
    For a non-empty list l, after folding kadStep over the first n elements
    of l.tail starting from (l.head!, l.head!), the state satisfies:
    1. All segment sums ending at position n are ≤ state.1 (ending-here bound)
    2. Some segment sum ending at position n equals state.1 (ending-here achieve)
    3. All segment sums within [0, n+1) are ≤ state.2 (overall bound)
    4. Some segment sum equals state.2 (overall achieve)
    5. state.1 ≤ state.2

PROVIDED SOLUTION
Prove by induction on n.

Base case (n = 0): state = (l.head!, l.head!). Since l.tail.take 0 = [], the fold returns the init.
- Ending bound: j ≤ 0 means j = 0, segSum l 0 1 = l[0] = l.head! ≤ l.head! ✓
- Ending achieve: j = 0 works ✓
- Overall bound: i < j and j ≤ 1 means i = 0, j = 1, segSum l 0 1 = l.head! ≤ l.head! ✓
- Overall achieve: i = 0, j = 1 works ✓
- state.1 ≤ state.2: l.head! ≤ l.head! ✓

Inductive step (n → n+1): Assume hn1 : n + 1 < l.length (so n + 2 ≤ l.length, meaning n < l.length - 1).
The state at n+1 is: (l.tail.take (n+1)).foldl kadStep (l.head!, l.head!)
= ((l.tail.take n ++ [l.tail[n]]).foldl kadStep (l.head!, l.head!))
= kadStep (prev_state) (l.tail[n])
where prev_state = (l.tail.take n).foldl kadStep (l.head!, l.head!).

Note l.tail[n] = l[n+1] (since l.tail is l with the first element removed).

Let cm = prev_state.1, gm = prev_state.2.
new_cm = max (l[n+1]) (cm + l[n+1])
new_gm = max gm new_cm

By IH at n (using hn : n + 1 < l.length which gives n < l.length):
- (IH1) ∀ j ≤ n, segSum l j (n+1) ≤ cm
- (IH2) ∃ j ≤ n, segSum l j (n+1) = cm
- (IH3) ∀ i j, i < j → j ≤ n+1 → segSum l i j ≤ gm
- (IH4) ∃ i j, i < j ∧ j ≤ n+1 ∧ segSum l i j = gm
- (IH5) cm ≤ gm

Prove ending bound at n+1: ∀ j ≤ n+1, segSum l j (n+2) ≤ new_cm
- If j ≤ n: segSum l j (n+2) = segSum l j (n+1) + segSum l (n+1) (n+2)  [by segSum_append]
  = segSum l j (n+1) + l[n+1]  [by segSum_single]
  ≤ cm + l[n+1]  [by IH1]
  ≤ max (l[n+1]) (cm + l[n+1]) = new_cm
- If j = n+1: segSum l (n+1) (n+2) = l[n+1] [by segSum_single] ≤ max (l[n+1]) (cm + l[n+1]) = new_cm

Prove ending achieve at n+1: ∃ j ≤ n+1, segSum l j (n+2) = new_cm
- Case new_cm = l[n+1]: j = n+1 works, segSum l (n+1) (n+2) = l[n+1] = new_cm
- Case new_cm = cm + l[n+1]: By IH2, ∃ j₀ ≤ n, segSum l j₀ (n+1) = cm.
  Then segSum l j₀ (n+2) = segSum l j₀ (n+1) + l[n+1] = cm + l[n+1] = new_cm. Use j = j₀.

Prove overall bound at n+1: ∀ i j, i < j → j ≤ n+2 → segSum l i j ≤ new_gm
- If j ≤ n+1: segSum l i j ≤ gm [by IH3] ≤ max gm new_cm = new_gm
- If j = n+2: segSum l i (n+2) ≤ new_cm [by ending bound] ≤ max gm new_cm = new_gm

Prove overall achieve at n+1: ∃ i j, i < j ∧ j ≤ n+2 ∧ segSum l i j = new_gm
- Case new_gm = gm: By IH4, ∃ i₀ j₀ with i₀ < j₀ ∧ j₀ ≤ n+1 ∧ segSum l i₀ j₀ = gm.
  Use these with j₀ ≤ n+1 ≤ n+2. ✓
- Case new_gm = new_cm: By ending achieve, ∃ j₀ ≤ n+1, segSum l j₀ (n+2) = new_cm.
  Use i = j₀, j = n+2. Then j₀ < n+2 (since j₀ ≤ n+1). ✓

Prove state.1 ≤ state.2: new_cm ≤ max gm new_cm = new_gm ✓
-/
lemma kadane_invariant (l : List ℤ) (hl : l.length > 0) (n : Nat) (hn : n < l.length) :
    let state := (l.tail.take n).foldl kadStep (l.head!, l.head!)
    (∀ j, j ≤ n → segSum l j (n + 1) ≤ state.1) ∧
    (∃ j, j ≤ n ∧ segSum l j (n + 1) = state.1) ∧
    (∀ i j, i < j → j ≤ n + 1 → segSum l i j ≤ state.2) ∧
    (∃ i j, i < j ∧ j ≤ n + 1 ∧ segSum l i j = state.2) ∧
    state.1 ≤ state.2 := by
  induction' n with n ih generalizing l <;> simp_all +decide [ List.take_add_one ];
  · rcases l <;> simp_all +decide [ segSum ];
    exact ⟨ fun i j hij hj => by interval_cases j <;> interval_cases i ; norm_num, 0, 1, by norm_num, by norm_num, by norm_num ⟩;
  · specialize ih l hl ( by linarith ) ; simp_all +decide [ List.take_add_one ] ;
    refine' ⟨ _, _, _, _ ⟩ <;> simp_all +decide [ kadStep ] ; (
    intro j hj; by_cases hj' : j ≤ n <;> simp_all +decide [ segSum ] ;
    · rw [ show n + 1 + 1 - j = ( n + 1 - j ) + 1 by omega, List.take_add_one ] ; aesop;
    · cases hj.eq_or_lt <;> first | linarith | aesop;);
    · by_cases h : max l[n + 1] ((List.foldl kadStep (l.head!, l.head!) (List.take n l.tail)).1 + l[n + 1]) = l[n + 1] <;> simp_all +decide [ segSum ];
      · use n + 1; simp +decide [ Nat.succ_eq_add_one, List.take_add_one ] ;
        grind +ring;
      · obtain ⟨ j, hj₁, hj₂ ⟩ := ih.2.1; use j; simp_all +decide [ Nat.succ_sub ] ;
        rw [ show n + 1 + 1 - j = ( n - j + 1 ) + 1 by omega ] ; simp_all +decide [ List.take_add_one ] ;
        grind;
    · intro i j hij hj; rcases hj with ( _ | hj ) <;> simp_all +decide [ segSum ] ;
      rw [ show n + 1 + 1 - i = ( n + 1 - i ) + 1 by omega, List.take_add_one ] ; simp +decide [ List.sum_append ] ; (
            grind +ring);
    · cases max_cases ( List.foldl kadStep ( l.head!, l.head! ) ( List.take n l.tail ) |> Prod.snd ) ( max l[n + 1] ( ( List.foldl kadStep ( l.head!, l.head! ) ( List.take n l.tail ) |> Prod.fst ) + l[n + 1] ) ) <;> cases max_cases l[n + 1] ( ( List.foldl kadStep ( l.head!, l.head! ) ( List.take n l.tail ) |> Prod.fst ) + l[n + 1] ) <;> simp_all +decide only [ ] ; (
      exact ⟨ _, _, ih.2.2.2.1.choose_spec.choose_spec.1, by linarith [ ih.2.2.2.1.choose_spec.choose_spec.2.1 ], ih.2.2.2.1.choose_spec.choose_spec.2.2 ⟩);
      · exact ⟨ _, _, ih.2.2.2.1.choose_spec.choose_spec.1, by linarith [ ih.2.2.2.1.choose_spec.choose_spec.2.1 ], ih.2.2.2.1.choose_spec.choose_spec.2.2 ⟩;
      · use n + 1, n + 2 ; simp_all +decide [ List.get ] ; (
        convert segSum_single l ( n + 1 ) ( by linarith ) using 1);
      · obtain ⟨ j, hj₁, hj₂ ⟩ := ih.2.1; use j, n + 2; simp_all +decide [ segSum_append ] ; (
        exact ⟨ by linarith, by rw [ ← hj₂, segSum_append _ _ _ ( by linarith ) ( by linarith ), segSum_single _ _ ( by linarith ) ] ⟩ ;)

/-
PROBLEM
When n = l.length - 1, l.tail.take n = l.tail

PROVIDED SOLUTION
For a non-empty list l, l.tail.length = l.length - 1. So l.tail.take (l.length - 1) = l.tail.take l.tail.length = l.tail by List.take_length.
-/
lemma tail_take_full (l : List ℤ) (hl : l.length > 0) :
    l.tail.take (l.length - 1) = l.tail := by
  cases l <;> aesop

/-
PROVIDED SOLUTION
The proof connects the array-based theorem to the list-based Kadane invariant.

1. Let l = nums.toList. Note l.length = nums.size > 0.
2. Rewrite the fold using fold_fn_eq_kadStep, array_foldl_eq_list_foldl, and array_get_zero_eq_head.
3. The fold result equals l.tail.foldl kadStep (l.head!, l.head!).
4. By tail_take_full, l.tail = l.tail.take (l.length - 1).
5. Apply kadane_invariant at n = l.length - 1 (so n + 1 = l.length).
6. This gives:
   - ∃ i j, i < j ∧ j ≤ l.length ∧ segSum l i j = state.2  (existence)
   - ∀ i j, i < j → j ≤ l.length → segSum l i j ≤ state.2  (bound)
7. Convert segSum back to rangeSum using rangeSum_eq_segSum.
8. Convert l.length back to nums.size.

For the existential part: from the invariant's ∃ i j, get the witnesses and use rangeSum_eq_segSum.
For the universal part: given start < stop ∧ stop ≤ nums.size, apply the invariant's bound and use rangeSum_eq_segSum.

Note: h_fold_eq might be useful to rewrite the fold with start index 1 to the fold over nums.extract 1, which then converts to the list tail fold.
-/
theorem correctness_goal_0_1 (nums : Array ℤ) (h_precond : precondition nums) (h_sz : nums.size > 0) (h_fold_eq : Array.foldl
    (fun acc x =>
      Prod.casesOn acc fun fst snd =>
        (fun currentMax globalMax =>
            let newCurrent := max x (currentMax + x);
            let newGlobal := max globalMax newCurrent;
            (newCurrent, newGlobal))
          fst snd)
    (nums[0]!, nums[0]!) nums 1 =
  Array.foldl
    (fun acc x =>
      Prod.casesOn acc fun fst snd =>
        (fun currentMax globalMax =>
            let newCurrent := max x (currentMax + x);
            let newGlobal := max globalMax newCurrent;
            (newCurrent, newGlobal))
          fst snd)
    (nums[0]!, nums[0]!) (nums.extract 1)) : (∃ start stop,
    start < stop ∧
      stop ≤ nums.size ∧
        rangeSum nums start stop =
          (Array.foldl
              (fun acc x =>
                Prod.casesOn acc fun fst snd =>
                  (fun currentMax globalMax =>
                      let newCurrent := max x (currentMax + x);
                      let newGlobal := max globalMax newCurrent;
                      (newCurrent, newGlobal))
                    fst snd)
              (nums[0]!, nums[0]!) nums 1).2) ∧
  ∀ (start stop : ℕ),
    start < stop ∧ stop ≤ nums.size →
      rangeSum nums start stop ≤
        (Array.foldl
            (fun acc x =>
              Prod.casesOn acc fun fst snd =>
                (fun currentMax globalMax =>
                    let newCurrent := max x (currentMax + x);
                    let newGlobal := max globalMax newCurrent;
                    (newCurrent, newGlobal))
                  fst snd)
            (nums[0]!, nums[0]!) nums 1).2 := by
  -- Apply the Kadane invariant to the list `nums.toList`.
  have h_kadane_invariant : let l := nums.toList; let state := l.tail.foldl kadStep (l.head!, l.head!); (∃ i j, i < j ∧ j ≤ l.length ∧ segSum l i j = state.2) ∧ (∀ i j, i < j → j ≤ l.length → segSum l i j ≤ state.2) := by
    have h_kadane_invariant : ∀ (l : List ℤ), l.length > 0 → let state := l.tail.foldl kadStep (l.head!, l.head!); (∃ i j, i < j ∧ j ≤ l.length ∧ segSum l i j = state.2) ∧ (∀ i j, i < j → j ≤ l.length → segSum l i j ≤ state.2) := by
      intro l hl;
      have := kadane_invariant l hl ( l.length - 1 ) ( Nat.sub_lt hl zero_lt_one );
      rcases l <;> aesop;
    exact h_kadane_invariant _ ( by simpa );
  convert h_kadane_invariant using 1;
  · rw [ h_fold_eq, array_foldl_eq_list_foldl ];
    rw [ array_extract_one_eq_tail ];
    rw [ array_get_zero_eq_head nums h_sz ];
    simp +decide [ rangeSum_eq_segSum ];
    rfl;
  · rw [ h_fold_eq, array_foldl_eq_list_foldl ];
    unfold kadStep; simp +decide [ array_extract_one_eq_tail ] ;
    rw [ show nums.toList.head! = nums[0]! from ?_, show List.take ( nums.size - 1 ) nums.toList.tail = nums.toList.tail from ?_ ];
    · simp +decide only [rangeSum_eq_segSum];
    · cases nums ; aesop;
    · exact?

end Proof
