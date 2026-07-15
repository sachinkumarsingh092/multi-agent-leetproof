import Lean

import Mathlib.Tactic

set_option maxHeartbeats 10000000

section Specs
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false
set_option pp.funBinderTypes true

/- Problem Description
    ProductOfArrayExceptSelf: for each index i, return the product of all input elements except the one at i.
    **Important: complexity should be O(n)**
    Natural language breakdown:
    1. Input is an array of integers `nums`.
    2. Output is an array `answer` of the same length as `nums`.
    3. For every valid index i, `answer[i]` equals the product of all `nums[j]` with j ≠ i.
    4. The relative order of indices is preserved: output position i corresponds to input position i.
    5. Multiplication uses the integer multiplicative identity 1 for the excluded element.
    6. Edge cases:
       - If the array is empty, the output is empty.
       - If the array has one element, the only output value is 1 (product over an empty set).
       - Zeros and negative values must be handled correctly.
    7. The problem statement guarantees that any prefix or suffix product fits in a 32-bit signed integer; we capture this as an input precondition.
    8. The algorithmic requirement "no division" is an implementation constraint; the mathematical result is uniquely determined by the product definition.
-/

-- Signed 32-bit integer bounds expressed as Int.
def int32Min : Int := (-2147483648)
def int32Max : Int := (2147483647)

def InInt32 (z : Int) : Prop := int32Min ≤ z ∧ z ≤ int32Max

-- Product of the first k elements (a prefix), where k is intended to satisfy k ≤ nums.size.
def prefixProd (nums : Array Int) (k : Nat) : Int :=
  (Finset.range k).prod (fun (j : Nat) => nums[j]!)

-- Product of the suffix starting at index k, where k is intended to satisfy k ≤ nums.size.
def suffixProd (nums : Array Int) (k : Nat) : Int :=
  (Finset.range (nums.size - k)).prod (fun (t : Nat) => nums[k + t]!)

-- Product of all elements except the element at index i.
def prodExcept (nums : Array Int) (i : Nat) : Int :=
  (Finset.range nums.size).prod (fun (j : Nat) => if j = i then (1 : Int) else nums[j]!)

-- Preconditions
-- We encode the stated 32-bit safety guarantee for any prefix and suffix product.
def precondition (nums : Array Int) : Prop :=
  (∀ (k : Nat), k ≤ nums.size → InInt32 (prefixProd nums k)) ∧
  (∀ (k : Nat), k ≤ nums.size → InInt32 (suffixProd nums k))

-- Postconditions
-- 1) Output length matches input length.
-- 2) For each valid index i, result[i] is the product of all input elements except nums[i].
def postcondition (nums : Array Int) (answer : Array Int) : Prop :=
  answer.size = nums.size ∧
  (∀ (i : Nat), i < nums.size → answer[i]! = prodExcept nums i)
end Specs

section Impl
def implementation (nums : Array Int) : Array Int :=
  let n := nums.size

  -- prefixRev.1 accumulates exclusive prefix products in reverse order
  -- prefixRev.2 is the running product of elements processed so far.
  let prefixRev : List Int × Int :=
    (List.range n).foldl
      (fun (st : List Int × Int) (i : Nat) =>
        let outRev := st.1
        let prod := st.2
        let outRev' := prod :: outRev
        let prod' := prod * nums[i]!
        (outRev', prod'))
      (([] : List Int), (1 : Int))

  let prefixL : List Int := prefixRev.1.reverse

  -- Build suffix-exclusive products by traversing indices right-to-left.
  -- We build them directly in the correct (left-to-right) order by cons-ing
  -- onto the front while iterating from right to left, so no final reverse is needed.
  let suffixL : List Int :=
    (List.range n).foldl
      (fun (st : List Int × Int) (t : Nat) =>
        let out := st.1
        let prod := st.2
        let i := n - 1 - t
        let out' := prod :: out
        let prod' := nums[i]! * prod
        (out', prod'))
      (([] : List Int), (1 : Int))
    |>.1

  (prefixL.zipWith (fun a b => a * b) suffixL).toArray
end Impl

section TestCases
-- Test case 1: Example 1
def test1_nums : Array Int := #[1, 2, 3, 4]
def test1_Expected : Array Int := #[24, 12, 8, 6]

-- Test case 2: Example 2
def test2_nums : Array Int := #[-1, 1, 0, -3, 3]
def test2_Expected : Array Int := #[0, 0, 9, 0, 0]

-- Test case 3: Empty array
def test3_nums : Array Int := (#[] : Array Int)
def test3_Expected : Array Int := (#[] : Array Int)

-- Test case 4: Singleton array
def test4_nums : Array Int := #[7]
def test4_Expected : Array Int := #[1]

-- Test case 5: Two elements
def test5_nums : Array Int := #[5, 6]
def test5_Expected : Array Int := #[6, 5]

-- Test case 6: Contains exactly one zero
def test6_nums : Array Int := #[0, 2, 3, 4]
def test6_Expected : Array Int := #[24, 0, 0, 0]

-- Test case 7: Contains two zeros
def test7_nums : Array Int := #[0, 2, 0, 4]
def test7_Expected : Array Int := #[0, 0, 0, 0]

-- Test case 8: All negative values
def test8_nums : Array Int := #[-1, -2, -3]
def test8_Expected : Array Int := #[6, 3, 2]

-- Test case 9: Mixed signs, no zeros
def test9_nums : Array Int := #[-2, 3, -4, 5]
def test9_Expected : Array Int := #[-60, 40, -30, 24]
end TestCases

section Proof

-- Helper definitions for the foldl states
private def prefixFoldState (nums : Array Int) (k : Nat) : List Int × Int :=
  (List.range k).foldl
    (fun (st : List Int × Int) (i : Nat) =>
      (st.2 :: st.1, st.2 * nums[i]!))
    ([], 1)

private def suffixFoldState (nums : Array Int) (k : Nat) : List Int × Int :=
  (List.range k).foldl
    (fun (st : List Int × Int) (t : Nat) =>
      let i := nums.size - 1 - t
      (st.2 :: st.1, nums[i]! * st.2))
    ([], 1)

/-
PROBLEM
Key mathematical lemma: prodExcept splits as prefix * suffix

PROVIDED SOLUTION
Split Finset.range nums.size into three disjoint parts: Finset.range i, {i}, and Finset.Ico (i+1) nums.size. The product over {i} gives 1 (since the function maps i to 1). The product over Finset.range i gives prefixProd nums i (since for j < i, j ≠ i so the if-else gives nums[j]!). The product over Finset.Ico (i+1) nums.size gives suffixProd nums (i+1) after reindexing with Finset.prod_Ico_eq_prod_range.
-/
lemma prodExcept_eq_prefix_mul_suffix (nums : Array Int) (i : Nat) (hi : i < nums.size) :
    prodExcept nums i = prefixProd nums i * suffixProd nums (i + 1) := by
  unfold prodExcept prefixProd suffixProd;
  rw [ ← Nat.add_sub_of_le hi.nat_succ_le ];
  rw [ Finset.prod_range_add _ _ ];
  simp +arith +decide [ Finset.prod_range_succ, Nat.add_sub_add_left ];
  exact Or.inl ( Finset.prod_congr rfl fun x hx => if_neg ( ne_of_lt ( Finset.mem_range.mp hx ) ) )

/-
PROBLEM
Prefix fold lemmas

PROVIDED SOLUTION
Induction on k. Base: both sides are 1. Step: use List.foldl_append or List.range_succ to extend the foldl by one step. The new snd = old_snd * nums[k]!. By IH, old_snd = prefixProd nums k. And prefixProd nums (k+1) = (Finset.range (k+1)).prod ... = (Finset.range k).prod ... * nums[k]! = prefixProd nums k * nums[k]! by Finset.prod_range_succ.

Induction on k. Base: both sides are 1 (empty product and initial state). Step: List.range (k+1) = List.range k ++ [k], so foldl processes one more step. The new snd = old_snd * nums[k]!. By IH, old_snd = prefixProd nums k. And prefixProd nums (k+1) = prefixProd nums k * nums[k]! by Finset.prod_range_succ.
-/
lemma prefixFold_snd_eq (nums : Array Int) (k : Nat) (hk : k ≤ nums.size) :
    (prefixFoldState nums k).2 = prefixProd nums k := by
  unfold prefixProd prefixFoldState;
  induction' k with k ih;
  · rfl;
  · simp_all +decide [ Finset.prod_range_succ, List.range_succ ];
    exact Or.inl <| ih <| Nat.le_of_succ_le ‹_›

/-
PROVIDED SOLUTION
Induction on k. Base: both sides are []. Step: after k+1 iterations, the fst has (prefixProd nums k) prepended to the old list. Reversing gives old_reverse ++ [prefixProd nums k]. By IH the old_reverse = (List.range k).map (fun i => prefixProd nums i). And (List.range (k+1)).map ... = (List.range k).map ... ++ [prefixProd nums k]. Use prefixFold_snd_eq to know the second component equals prefixProd nums k.

Induction on k. Base: both sides are []. Step: List.range (k+1) = List.range k ++ [k], so foldl processes one more step. The new fst = old_snd :: old_fst. Reversing: (old_snd :: old_fst).reverse = old_fst.reverse ++ [old_snd]. By IH, old_fst.reverse = (List.range k).map (prefixProd nums). By prefixFold_snd_eq, old_snd = prefixProd nums k. So the reverse = (List.range k).map (prefixProd nums) ++ [prefixProd nums k] = (List.range (k+1)).map (prefixProd nums) by List.range_succ and List.map_append.
-/
lemma prefixFold_fst_eq (nums : Array Int) (k : Nat) (hk : k ≤ nums.size) :
    (prefixFoldState nums k).1.reverse = (List.range k).map (fun i => prefixProd nums i) := by
  induction' k with k ih generalizing nums <;> simp_all +decide [ List.range_succ ];
  · rfl;
  · unfold prefixFoldState;
    simp +decide [ ← ih nums (Nat.le_of_succ_le hk), List.range_succ ];
    exact ⟨ prefixFold_snd_eq nums k (Nat.le_of_succ_le hk), rfl ⟩

/-
PROBLEM
Suffix fold lemmas

PROVIDED SOLUTION
Induction on k. Base k=0: snd = 1, and suffixProd nums nums.size = (Finset.range 0).prod ... = 1. Step: the new snd = nums[n-1-k]! * old_snd. By IH old_snd = suffixProd nums (n-k). Need: nums[n-1-k]! * suffixProd nums (n-k) = suffixProd nums (n-k-1). Unfold suffixProd: suffixProd nums (n-k-1) = (Finset.range (k+1)).prod (fun t => nums[n-k-1+t]!) = nums[n-k-1]! * (Finset.range k).prod (fun t => nums[n-k+t]!) by Finset.prod_range_succ' (or by rewriting the range). The second factor is suffixProd nums (n-k). Note n-1-k = n-k-1 when k < n.
-/
lemma suffixFold_snd_eq (nums : Array Int) (k : Nat) (hk : k ≤ nums.size) :
    (suffixFoldState nums k).2 = suffixProd nums (nums.size - k) := by
  unfold suffixProd suffixFoldState;
  rw [ Nat.sub_sub_self hk ];
  induction' k with k ih;
  · rfl;
  · simp +decide [ List.range_succ, ih ( Nat.le_of_succ_le hk ) ];
    rw [ Finset.prod_range_succ' ];
    grind +ring

/-
PROVIDED SOLUTION
Induction on k. Base k=0: both sides are []. Step: the new fst = old_snd :: old_fst. By IH old_fst = (List.range k).map (fun t => suffixProd nums (n - k + 1 + t)). By suffixFold_snd_eq, old_snd = suffixProd nums (n - k). The new list = suffixProd(n-k) :: (List.range k).map(fun t => suffixProd(n-k+1+t)). The RHS is (List.range (k+1)).map (fun t => suffixProd nums (n - (k+1) + 1 + t)) = (List.range (k+1)).map (fun t => suffixProd nums (n - k + t)). For t=0 this is suffixProd(n-k), and for t=1..k this is suffixProd(n-k+1)..suffixProd(n). This matches since List.range (k+1) = 0 :: (List.range k).map (·+1), so the map gives suffixProd(n-k) :: (List.range k).map (fun t => suffixProd(n-k+t+1)) = suffixProd(n-k) :: (List.range k).map (fun t => suffixProd(n-k+1+t)).

Induction on k. Base k=0: both sides are []. Step k → k+1: the foldl processes one more step t=k. The new fst = old_snd :: old_fst. By suffixFold_snd_eq, old_snd = suffixProd nums (nums.size - k). By IH, old_fst = (List.range k).map (fun t => suffixProd nums (nums.size - k + 1 + t)). The new list = suffixProd(nums.size - k) :: (List.range k).map (fun t => suffixProd(nums.size - k + 1 + t)). The RHS is (List.range (k+1)).map (fun t => suffixProd nums (nums.size - (k+1) + 1 + t)) = (List.range (k+1)).map (fun t => suffixProd nums (nums.size - k + t)). Use List.range_succ_eq_map or List.range_succ to split this into the head (t=0 gives suffixProd(nums.size - k)) and the tail (t=1..k gives the same as old_fst after shifting). Note nums.size - (k+1) + 1 = nums.size - k when k < nums.size, so use omega for the arithmetic.
-/
lemma suffixFold_fst_eq (nums : Array Int) (k : Nat) (hk : k ≤ nums.size) :
    (suffixFoldState nums k).1 = (List.range k).map (fun t => suffixProd nums (nums.size - k + 1 + t)) := by
  induction' k with k ih generalizing nums;
  · rfl;
  · convert congr_arg ( fun l => ( suffixProd nums ( nums.size - k ) ) :: l ) ( ih nums ( Nat.le_of_succ_le hk ) ) using 1;
    · unfold suffixFoldState;
      simp +decide [ List.range_succ ];
      convert suffixFold_snd_eq nums k ( Nat.le_of_succ_le hk ) using 1;
    · simp +arith +decide [ List.range_succ_eq_map, Nat.sub_add_comm ( by linarith : k ≤ nums.size ) ];
      grind

/-
PROBLEM
Size and element lemmas for the implementation

PROVIDED SOLUTION
Unfold implementation. The result is (prefixL.zipWith (*) suffixL).toArray. We need List.toArray size = List.length. prefixL = (prefixFoldState nums n).1.reverse, so its length = (prefixFoldState nums n).1.length. By prefixFold_fst_eq, (prefixFoldState nums n).1.reverse has length = (List.range n).map(...).length = n. So prefixL has length n. Similarly, by suffixFold_fst_eq, suffixL = (suffixFoldState nums n).1 has length = (List.range n).map(...).length = n. Then zipWith on two lists of length n produces a list of length n. So toArray gives an array of size n = nums.size.
-/
lemma implementation_size (nums : Array Int) :
    (implementation nums).size = nums.size := by
  unfold implementation; simp +decide [ List.length_zipWith ];
  have h_len : ∀ (l: List Nat), (List.foldl (fun st i => (st.2 :: st.1, st.2 * nums[i]!)) ([], 1) l).1.length = l.length ∧ (List.foldl (fun st t => (st.2 :: st.1, nums[nums.size - 1 - t]! * st.2)) ([], 1) l).1.length = l.length := by
    intro l; induction l using List.reverseRecOn <;> aesop;
  grind

/-
PROVIDED SOLUTION
Unfold implementation. The result is (prefixL.zipWith (*) suffixL).toArray. By prefixFold_fst_eq, prefixL = (List.range n).map (fun i => prefixProd nums i). By suffixFold_fst_eq with k=n, suffixL = (List.range n).map (fun t => suffixProd nums (n - n + 1 + t)) = (List.range n).map (fun t => suffixProd nums (1 + t)) = (List.range n).map (fun t => suffixProd nums (t + 1)). The zipWith of these lists at index i gives prefixProd nums i * suffixProd nums (i + 1). Then toArray preserves elements, and getElem! on the array at index i gives the same value.
-/
lemma implementation_getElem (nums : Array Int) (i : Nat) (hi : i < nums.size) :
    (implementation nums)[i]! = prefixProd nums i * suffixProd nums (i + 1) := by
  unfold implementation; simp_all +decide [ List.getElem?_append, hi ] ;
  -- By definition of `prefixFoldState` and `suffixFoldState`, we know that their first components are the lists of prefix and suffix products, respectively.
  have h_prefix_suffix : (List.foldl (fun st i => (st.2 :: st.1, st.2 * nums[i]!)) ([], 1) (List.range nums.size)).1.reverse = List.map (fun i => prefixProd nums i) (List.range nums.size) ∧ (List.foldl (fun st t => (st.2 :: st.1, nums[nums.size - 1 - t]! * st.2)) ([], 1) (List.range nums.size)).1 = List.map (fun t => suffixProd nums (nums.size - nums.size + 1 + t)) (List.range nums.size) := by
    exact ⟨ by simpa using prefixFold_fst_eq nums _ le_rfl, by simpa using suffixFold_fst_eq nums _ le_rfl ⟩;
  grind +ring

theorem correctness_goal (nums : Array Int) (h_precond : precondition nums) : postcondition nums (implementation nums) := by
  unfold postcondition
  constructor
  · exact implementation_size nums
  · intro i hi
    rw [implementation_getElem nums i hi]
    rw [prodExcept_eq_prefix_mul_suffix nums i hi]

end Proof