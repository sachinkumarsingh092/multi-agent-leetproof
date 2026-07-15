import Mathlib.Tactic
set_option maxHeartbeats 10000000

section Specs
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

section Impl
def implementation (nums : Array Int) : Array Int :=
  -- Counting sort over the fixed constraints range [-50000, 50000].
  -- Time: O(n + k), Space: O(k), where k = 100001.
  let minV : Int := -50000
  let maxV : Int := 50000
  let offset : Int := -minV
  let k : Nat := Int.toNat (maxV - minV + 1)

  let idxOf (v : Int) : Nat :=
    -- Input is assumed to be within range by the precondition.
    Int.toNat (v + offset)

  let incAt (counts : Array Nat) (i : Nat) : Array Nat :=
    -- Defensive: if out-of-range, leave counts unchanged.
    if h : i < counts.size then
      counts.set! i (counts[i]! + 1)
    else
      counts

  let counts0 : Array Nat := Array.replicate k 0
  let counts : Array Nat :=
    nums.foldl (fun cs v => incAt cs (idxOf v)) counts0

  let rec pushMany (v : Int) (n : Nat) (acc : Array Int) : Array Int :=
    match n with
    | 0 => acc
    | n + 1 => pushMany v n (acc.push v)

  let rec emit (i : Nat) (out : Array Int) : Array Int :=
    if h : i < counts.size then
      let c : Nat := counts[i]!
      let v : Int := minV + Int.ofNat i
      emit (i + 1) (pushMany v c out)
    else
      out

  emit 0 #[]
end Impl

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


-- Top-level helper definitions mirroring the local ones
section Helpers

def kSize : Nat := 100001

def idxOf (v : Int) : Nat := Int.toNat (v + 50000)

def valOf (i : Nat) : Int := -50000 + Int.ofNat i

def incAt (counts : Array Nat) (i : Nat) : Array Nat :=
  if i < counts.size then
    counts.set! i (counts[i]! + 1)
  else
    counts

def buildCounts (nums : Array Int) : Array Nat :=
  nums.foldl (fun cs v => incAt cs (idxOf v)) (Array.replicate kSize 0)

def pushMany (v : Int) (n : Nat) (acc : Array Int) : Array Int :=
  match n with
  | 0 => acc
  | n + 1 => pushMany v n (acc.push v)

def emit (counts : Array Nat) (i : Nat) (out : Array Int) : Array Int :=
  if h : i < counts.size then
    let c := counts[i]!
    let v := -50000 + Int.ofNat i
    emit counts (i + 1) (pushMany v c out)
  else out
termination_by counts.size - i

/-
PROBLEM
Key equivalence: implementation equals our top-level version

PROVIDED SOLUTION
Unfold implementation. The body is:
let minV := -50000; let maxV := 50000; let offset := -minV; let k := 100001;
let idxOf v := Int.toNat (v + offset);
let incAt cs i := if i < cs.size then cs.set! i (cs[i]! + 1) else cs;
let counts0 := Array.replicate k 0;
let counts := nums.foldl (fun cs v => incAt cs (idxOf v)) counts0;
implementation.emit (-50000) counts 0 #[]

The key steps:
1. Show implementation.pushMany = pushMany (by induction)
2. Show implementation.emit minV counts i out = emit counts i out (by well-founded induction, using step 1)
3. Show the counts computed inside implementation equal buildCounts nums (they use the same incAt and idxOf)
4. Combine: implementation nums = emit (buildCounts nums) 0 #[]

For the emit equivalence, we need to unfold both definitions and show they agree step by step. Both check i < counts.size, compute c = counts[i]!, v = -50000 + i, recurse with i+1 and pushMany v c out.
-/
lemma implementation_eq (nums : Array Int) :
    implementation nums = emit (buildCounts nums) 0 #[] := by
      -- The two functions are equivalent because they are defined in the same way and use the same recursive structure.
      have h_emit_eq : ∀ (counts : Array Nat) (i : Nat) (out : Array Int), implementation.emit (-50000) counts i out = emit counts i out := by
        intros counts i out;
        induction' h : counts.size - i using Nat.strong_induction_on with m ih generalizing i out counts
        generalize_proofs at *; (
        unfold emit implementation.emit;
        -- By definition of `implementation.pushMany`, we know that it is equivalent to `pushMany`.
        have h_pushMany_eq : ∀ (v : Int) (n : Nat) (acc : Array Int), implementation.pushMany v n acc = pushMany v n acc := by
          intros v n acc; induction' n with n ih generalizing acc <;> aesop;
        generalize_proofs at *; (
        split_ifs <;> simp_all +decide [ Nat.sub_add_comm ];
        exact ih _ ( by omega ) _ _ _ rfl));
      exact h_emit_eq _ _ _

end Helpers

section PushManyLemmas

@[simp] lemma pushMany_zero (v : Int) (acc : Array Int) :
    pushMany v 0 acc = acc := by rfl

@[simp] lemma pushMany_succ (v : Int) (n : Nat) (acc : Array Int) :
    pushMany v (n + 1) acc = pushMany v n (acc.push v) := by rfl

/-
PROVIDED SOLUTION
Simple induction on n. Base case: pushMany v 0 acc = acc, so size = acc.size = acc.size + 0. Inductive step: pushMany v (n+1) acc = pushMany v n (acc.push v), by IH this has size (acc.push v).size + n = (acc.size + 1) + n = acc.size + (n+1).
-/
lemma pushMany_size (v : Int) (n : Nat) (acc : Array Int) :
    (pushMany v n acc).size = acc.size + n := by
      induction' n with n ih generalizing acc <;> simp +arith +decide [ * ]

/-
PROVIDED SOLUTION
Induction on n. Base: pushMany v 0 acc = acc, and acc.toList ++ [] = acc.toList. Inductive: pushMany v (n+1) acc = pushMany v n (acc.push v), by IH = (acc.push v).toList ++ List.replicate n v = (acc.toList ++ [v]) ++ List.replicate n v = acc.toList ++ (v :: List.replicate n v) = acc.toList ++ List.replicate (n+1) v.
-/
lemma pushMany_toList (v : Int) (n : Nat) (acc : Array Int) :
    (pushMany v n acc).toList = acc.toList ++ List.replicate n v := by
      induction' n with n ih generalizing acc <;> simp_all +decide [ List.replicate_succ ]

/-
PROVIDED SOLUTION
Induction on n. Base: pushMany v 0 acc = acc, count = acc.count w + 0. Inductive: pushMany v (n+1) acc = pushMany v n (acc.push v). By IH, count w = (acc.push v).count w + (if v == w then n else 0). We need (acc.push v).count w = acc.count w + if v == w then 1 else 0. Then the total is acc.count w + (if v == w then 1 else 0) + (if v == w then n else 0) = acc.count w + if v == w then n+1 else 0. Use Array.count and Array.push properties.
-/
lemma pushMany_count (v : Int) (n : Nat) (acc : Array Int) (w : Int) :
    (pushMany v n acc).count w = acc.count w + if v == w then n else 0 := by
      induction' n with n ih generalizing acc <;> simp_all +decide [ pushMany ];
      grind +ring

end PushManyLemmas

section IncAtLemmas

/-
PROVIDED SOLUTION
Unfold incAt. If i < counts.size, then we use set! which preserves size (Array.size_set!). Otherwise counts is unchanged.
-/
lemma incAt_size (counts : Array Nat) (i : Nat) :
    (incAt counts i).size = counts.size := by
      unfold incAt; aesop;

/-
PROVIDED SOLUTION
Unfold buildCounts. It's nums.foldl (fun cs v => incAt cs (idxOf v)) (Array.replicate kSize 0). We need to show the result has size kSize. The initial array has size kSize (by Array.size_replicate). Each step applies incAt which preserves size (by incAt_size). So by Array.foldl induction, the size is preserved throughout.
-/
lemma buildCounts_size (nums : Array Int) :
    (buildCounts nums).size = kSize := by
      unfold buildCounts;
      -- The size of the array is preserved under the foldl operation since each step applies incAt which preserves size.
      have h_size_fold : ∀ (cs : Array Nat) (vs : List ℤ), cs.size = kSize → (List.foldl (fun cs v => incAt cs (idxOf v)) cs vs).size = kSize := by
        intros cs vs hcs;
        induction' vs using List.reverseRecOn with v vs ih;
        · exact hcs;
        · simp_all +decide [ List.foldl_append ];
          rw [ ← ih, incAt_size ];
      cases nums ; aesop

end IncAtLemmas

section BuildCountsLemmas

/-
PROVIDED SOLUTION
idxOf v = Int.toNat (v + 50000). Since minVal = -50000 ≤ v ≤ 50000 = maxVal, we have 0 ≤ v + 50000 ≤ 100000. So Int.toNat (v + 50000) ≤ 100000 < 100001 = kSize. Use omega after unfolding.
-/
lemma idxOf_lt_kSize (v : Int) (hv : minVal ≤ v ∧ v ≤ maxVal) :
    idxOf v < kSize := by
      exact Int.toNat_lt ( by linarith! [ hv.1, hv.2, show minVal = -50000 from rfl, show maxVal = 50000 from rfl ] ) |>.2 ( by linarith! [ hv.1, hv.2, show minVal = -50000 from rfl, show maxVal = 50000 from rfl, show kSize = 100001 from rfl ] )

/-
PROVIDED SOLUTION
idxOf a = Int.toNat (a + 50000) and idxOf b = Int.toNat (b + 50000). Since a, b ∈ [-50000, 50000], both a + 50000 and b + 50000 are ≥ 0. Int.toNat is injective on nonneg integers. So a + 50000 = b + 50000, hence a = b. Use omega after unfolding idxOf, minVal, maxVal and using Int.toNat_eq_toNat or Int.toNat injectivity on nonneg values.
-/
lemma idxOf_injective (a b : Int)
    (ha : minVal ≤ a ∧ a ≤ maxVal) (hb : minVal ≤ b ∧ b ≤ maxVal)
    (h : idxOf a = idxOf b) : a = b := by
      unfold idxOf at h; unfold minVal maxVal at *; omega;

/-
PROVIDED SOLUTION
Unfold incAt. Since i < counts.size, we enter the then branch: (counts.set! i (counts[i]! + 1))[i]!. Since set! at index i sets that index, we get counts[i]! + 1. Use Array.getElem!_set! or similar lemma for set! at the same index.
-/
lemma incAt_same (counts : Array Nat) (i : Nat) (hi : i < counts.size) :
    (incAt counts i)[i]! = counts[i]! + 1 := by
      unfold incAt; aesop;

/-
PROVIDED SOLUTION
Unfold incAt. Case split on whether i < counts.size. If yes, (counts.set! i (counts[i]! + 1))[j]!. Since i ≠ j and j < counts.size, the set! at position i doesn't affect position j. If i ≥ counts.size, incAt returns counts unchanged, so counts[j]! = counts[j]!.
-/
lemma incAt_diff (counts : Array Nat) (i j : Nat) (hij : i ≠ j) (hj : j < counts.size) :
    (incAt counts i)[j]! = counts[j]! := by
      unfold incAt; aesop;

/-
PROBLEM
General foldl invariant for building counts

PROVIDED SOLUTION
Induction on xs (as a list).

Base case: foldl [] init = init, and List.count v [] = 0. So init[idxOf v]! = init[idxOf v]! + 0. Done.

Inductive step: xs = x :: xs'.
List.foldl f (x :: xs') init = List.foldl f xs' (f init x) = List.foldl f xs' (incAt init (idxOf x)).

The new init is init' = incAt init (idxOf x).
- init'.size = incAt_size ... = init.size = kSize
- All elements of xs' are in range (subset of x :: xs').

By IH: result[idxOf v]! = init'[idxOf v]! + xs'.count v.

Case v = x: Then idxOf x = idxOf v.
init'[idxOf v]! = (incAt init (idxOf v))[idxOf v]! = init[idxOf v]! + 1 (by incAt_same, using idxOf_lt_kSize hv and h_init_size).
List.count v (x :: xs') = 1 + List.count v xs' (since x = v).
So result = init[idxOf v]! + 1 + xs'.count v = init[idxOf v]! + (1 + xs'.count v). ✓

Case v ≠ x: Since both v and x are in range (x ∈ x :: xs', so h_range gives x in range), idxOf_injective gives idxOf x ≠ idxOf v.
init'[idxOf v]! = (incAt init (idxOf x))[idxOf v]! = init[idxOf v]! (by incAt_diff, since idxOf x ≠ idxOf v and idxOf v < init.size by idxOf_lt_kSize and h_init_size).
List.count v (x :: xs') = List.count v xs' (since x ≠ v).
So result = init[idxOf v]! + xs'.count v. ✓
-/
lemma foldl_incAt_spec (xs : List Int) (init : Array Nat) (v : Int)
    (hv : minVal ≤ v ∧ v ≤ maxVal)
    (h_init_size : init.size = kSize)
    (h_range : ∀ w, w ∈ xs → minVal ≤ w ∧ w ≤ maxVal) :
    (List.foldl (fun cs w => incAt cs (idxOf w)) init xs)[idxOf v]! =
      init[idxOf v]! + xs.count v := by
        induction' xs using List.reverseRecOn with xs x ih generalizing init v;
        · rfl;
        · by_cases h : idxOf x = idxOf v <;> simp_all +decide [ List.count_cons ];
          · rw [ incAt_same ];
            · rw [ ih init v hv.1 hv.2 h_init_size ] ; split_ifs <;> simp_all +decide [ add_comm, add_left_comm, add_assoc ];
              exact ‹¬x = v› ( idxOf_injective x v ( h_range x ( Or.inr rfl ) ) hv h );
            · -- By definition of `incAt`, the size of the array remains the same after each step.
              have h_size : ∀ (xs : List ℤ) (init : Array ℕ), (List.foldl (fun cs w => incAt cs (idxOf w)) init xs).size = init.size := by
                intros xs init; induction' xs using List.reverseRecOn with xs x ih generalizing init; aesop;
                simp +decide [ *, List.foldl_append ];
                rw [ incAt_size, ih ];
              rw [ h_size, h_init_size ] ; exact idxOf_lt_kSize v hv;
          · rw [ if_neg ( by rintro rfl; exact h rfl ), incAt_diff ] <;> simp_all +decide [ add_comm, add_left_comm, add_assoc ];
            -- By definition of `foldl`, the size of the array remains `kSize` throughout the process.
            have h_foldl_size : ∀ (xs : List ℤ) (init : Array ℕ), init.size = kSize → (List.foldl (fun cs w => incAt cs (idxOf w)) init xs).size = kSize := by
              intros xs init h_init_size; induction' xs using List.reverseRecOn with xs x ih generalizing init; aesop;
              simp_all +decide [ List.foldl_append ];
              rw [ incAt_size, ih init h_init_size ];
            rw [ h_foldl_size xs init h_init_size ] ; exact idxOf_lt_kSize v hv

/-
PROBLEM
Core counting invariant: the count array correctly represents frequencies

PROVIDED SOLUTION
Unfold buildCounts. It equals nums.foldl (fun cs v => incAt cs (idxOf v)) (Array.replicate kSize 0).

Use the fact that Array.foldl f init arr = List.foldl f init arr.toList (or however Array.foldl relates to List.foldl).

Apply foldl_incAt_spec with xs = nums.toList, init = Array.replicate kSize 0:
- hv: given
- h_init_size: Array.size_replicate gives size = kSize
- h_range: from h_precond (precondition nums = allInRange nums), for any element w at index i in nums, minVal ≤ w ∧ w ≤ maxVal. Need to convert this to: for all w ∈ nums.toList, minVal ≤ w ∧ w ≤ maxVal. This follows from allInRange.

This gives: result[idxOf v]! = (Array.replicate kSize 0)[idxOf v]! + nums.toList.count v.

(Array.replicate kSize 0)[idxOf v]! = 0 since idxOf v < kSize (by idxOf_lt_kSize).
nums.toList.count v = nums.count v (by definition, Array.count is defined via toList).

So result = 0 + nums.count v = nums.count v. ✓
-/
lemma buildCounts_spec (nums : Array Int) (v : Int)
    (hv : minVal ≤ v ∧ v ≤ maxVal)
    (h_precond : precondition nums) :
    (buildCounts nums)[idxOf v]! = nums.count v := by
      convert foldl_incAt_spec nums.toList _ _ _ _ _ using 1;
      simp +zetaDelta at *;
      convert rfl;
      · -- Since `idxOf v` is within the bounds of the array, we can apply `Array.getElem!_replicate` to conclude that the element at `idxOf v` is 0.
        have h_bounds : idxOf v < kSize := by
          exact?;
        grind +ring;
      · exact hv;
      · norm_num;
      · intros w hw
        have h_range : ∀ i, i < nums.size → minVal ≤ nums[i]! ∧ nums[i]! ≤ maxVal := by
          exact h_precond;
        obtain ⟨ i, hi ⟩ := List.mem_iff_get.mp hw; aesop;

/-
PROBLEM
Values outside the valid index range have count 0

PROVIDED SOLUTION
If i >= kSize, then for any array arr, arr[i]! = arr.getD i default. If i >= arr.size, this is the default value (0 for Nat). Since buildCounts nums has size kSize (by buildCounts_size), and i >= kSize, we have i >= (buildCounts nums).size, so (buildCounts nums)[i]! = default = 0.
-/
lemma buildCounts_zero (nums : Array Int) (i : Nat)
    (hi : kSize ≤ i) :
    (buildCounts nums)[i]! = 0 := by
      -- Since i is at least the size of the array, the ! operator returns the default value, which is zero for Nat.
      have h_out_of_bounds : i ≥ (buildCounts nums).size := by
        rw [ buildCounts_size ] ; exact hi;
      cases h : buildCounts nums ; aesop

end BuildCountsLemmas

section EmitLemmas

/-
PROVIDED SOLUTION
Induction on counts.size - i (well-founded recursion matching the definition of emit).

Base case: i ≥ counts.size. Then emit returns out. Finset.Ico i counts.size = ∅, so sum = 0. result.size = out.size = out.size + 0. ✓

Inductive step: i < counts.size. emit counts i out = emit counts (i+1) (pushMany v c out) where c = counts[i]! and v = -50000 + i.
By IH: (emit counts (i+1) (pushMany v c out)).size = (pushMany v c out).size + ∑ j ∈ Finset.Ico (i+1) counts.size, counts[j]!.
By pushMany_size: (pushMany v c out).size = out.size + c = out.size + counts[i]!.
So result = out.size + counts[i]! + ∑ j ∈ Finset.Ico (i+1) counts.size, counts[j]!.
And Finset.Ico i counts.size = {i} ∪ Finset.Ico (i+1) counts.size, so the sum splits as counts[i]! + ∑ j ∈ Finset.Ico (i+1) counts.size, counts[j]!.
Therefore result = out.size + ∑ j ∈ Finset.Ico i counts.size, counts[j]!. ✓

Use Finset.sum_Ico_eq_add_neg or Finset.Ico_insert_right or Finset.sum_Ico_succ_top. Actually the right lemma is Finset.Ico i n when i < n: ∑ j ∈ Finset.Ico i n = f i + ∑ j ∈ Finset.Ico (i+1) n.
-/
lemma emit_size (counts : Array Nat) (i : Nat) (out : Array Int) :
    (emit counts i out).size = out.size + ∑ j ∈ Finset.Ico i counts.size, counts[j]! := by
      induction' h : counts.size - i with n ih generalizing i out;
      · unfold emit;
        split_ifs <;> simp_all +decide [ Nat.sub_eq_zero_iff_le ];
        grind;
      · rw [ show emit counts i out = emit counts ( i + 1 ) ( pushMany ( -50000 + Int.ofNat i ) ( counts[i]! ) out ) from ?_ ];
        · rw [ Finset.Ico_eq_cons_Ioo ];
          · rw [ Finset.sum_cons, ih ];
            · rw [ pushMany_size ] ; ring!;
            · omega;
          · omega;
        · rw [ emit ];
          split_ifs <;> simp_all +decide [ Nat.sub_succ ]

/-
PROVIDED SOLUTION
Induction on counts.size - i (well-founded, matching emit's definition).

Base case: i ≥ counts.size. emit returns out. Finset.Ico i counts.size = ∅, sum = 0.
result.count w = out.count w = out.count w + 0. ✓

Inductive step: i < counts.size. emit counts i out = emit counts (i+1) (pushMany v c out) where c = counts[i]!, v = -50000 + i.
By IH: (emit counts (i+1) ...).count w = (pushMany v c out).count w + ∑ j ∈ Ico (i+1) counts.size, (if (-50000 + j) == w then counts[j]! else 0).
By pushMany_count: (pushMany v c out).count w = out.count w + (if v == w then c else 0) = out.count w + (if (-50000 + i) == w then counts[i]! else 0).
So result = out.count w + (if (-50000 + i) == w then counts[i]! else 0) + ∑ j ∈ Ico (i+1) counts.size, ....
And Finset.Ico i counts.size splits as {i} ∪ Ico (i+1) counts.size, giving the sum = (if (-50000+i)==w then counts[i]! else 0) + ∑ j ∈ Ico (i+1) counts.size, .... ✓
-/
lemma emit_count (counts : Array Nat) (i : Nat) (out : Array Int) (w : Int) :
    (emit counts i out).count w = out.count w +
      ∑ j ∈ Finset.Ico i counts.size,
        if (-50000 + Int.ofNat j) == w then counts[j]! else 0 := by
          -- We'll use induction on the number of steps from `i` to the end of the counts array.
          induction' h : counts.size - i with k ih generalizing i out;
          · unfold emit;
            split_ifs <;> simp_all +decide [ Nat.sub_eq_iff_eq_add ];
            omega;
          · unfold emit;
            split_ifs <;> simp_all +decide [ Nat.sub_succ, Finset.sum_Ico_eq_sum_range ];
            rw [ Finset.sum_range_succ' ];
            simp +decide [ add_comm, add_left_comm, add_assoc, pushMany_count ];
            grind

/-
PROVIDED SOLUTION
Induction on counts.size - i (well-founded, matching emit's definition).

Base case: i ≥ counts.size. emit returns out. out is sorted by h_sorted. ✓

Inductive step: i < counts.size. emit counts i out = emit counts (i+1) (pushMany v c out) where c = counts[i]!, v = -50000 + i.

Apply IH with out' = pushMany v c out. Need:
1. isSortedNondecreasing out': pushMany appends c copies of v to out. Since out is sorted and all elements of out are ≤ v (by h_bound, since v = -50000 + i), appending v's preserves sorting. Formally: for any indices p < q < out'.size, out'[p]! ≤ out'[q]!. If both p, q < out.size, use h_sorted. If p < out.size ≤ q, then out'[p]! = out[p]! ≤ v (by h_bound) and out'[q]! = v. If both ≥ out.size, both equal v.

2. All elements of out' are ≤ -50000 + (i+1): elements from out are ≤ -50000 + i < -50000 + (i+1). New elements equal v = -50000 + i ≤ -50000 + (i+1).

Actually, we need ≤ not <. So elements from out are ≤ -50000 + i ≤ -50000 + (i+1). New elements = -50000 + i ≤ -50000 + (i+1). ✓

This requires a helper lemma about pushMany preserving sortedness when appending a value ≥ all existing elements. We can inline this or prove it separately.

Key insight: pushMany v c out has toList = out.toList ++ List.replicate c v (by pushMany_toList). Use this to reason about indices.
-/
lemma emit_sorted (counts : Array Nat) (i : Nat) (out : Array Int)
    (h_sorted : isSortedNondecreasing out)
    (h_bound : ∀ k, k < out.size → out[k]! ≤ -50000 + Int.ofNat i) :
    isSortedNondecreasing (emit counts i out) := by
      -- By definition of emit, we know that emit counts i out is the result of appending some elements to out.
      induction' k : counts.size - i with k ih generalizing i out;
      · unfold emit;
        grind;
      · convert ih ( i + 1 ) ( pushMany ( -50000 + Int.ofNat i ) ( counts[i]! ) out ) _ _ _ using 1;
        · rw [ emit ];
          aesop;
        · -- Since pushMany appends the same value to the end of the array, and the original array is sorted, the new array is also sorted.
          have h_pushMany_sorted : ∀ (out : Array ℤ) (v : ℤ) (n : ℕ), isSortedNondecreasing out → (∀ k < out.size, out[k]! ≤ v) → isSortedNondecreasing (pushMany v n out) := by
            intros out v n h_sorted h_bound
            induction' n with n ih generalizing out v;
            · exact h_sorted;
            · convert ih ( out.push v ) v _ _ using 1;
              · intro i j hij hj; by_cases hi : i < out.size <;> by_cases hj : j < out.size <;> simp_all +decide [ Array.getElem_push ] ;
                · convert h_sorted i j hij hj using 1;
                  · grind;
                  · exact?;
                · grind;
                · linarith;
                · linarith;
              · intro k hk; by_cases hk' : k < out.size <;> simp_all +decide [ Array.push ] ;
          exact h_pushMany_sorted out _ _ h_sorted h_bound;
        · intro k hk; by_cases hk' : k < out.size <;> simp_all +decide [ pushMany_toList ] ;
          · convert le_trans ( h_bound _ hk' ) ( le_add_of_nonneg_right zero_le_one ) using 1;
            -- By definition of pushMany, the element at position k in the pushMany array is the same as the element at position k in out.
            have h_pushMany_eq : ∀ (v : ℤ) (n : ℕ) (acc : Array ℤ) (k : ℕ), k < acc.size → (pushMany v n acc)[k]! = acc[k]! := by
              intros v n acc k hk; induction' n with n ih generalizing acc k <;> simp_all +decide [ pushMany ] ;
              convert ih ( acc.push v ) k _ using 1;
              exact?;
              simpa using hk.trans_le ( Nat.le_succ _ );
            convert congr_arg _ ( h_pushMany_eq _ _ _ _ hk' ) using 1;
            any_goals exact fun x => 50000 + x;
            any_goals exact counts[i]!;
            any_goals exact -50000 + i;
            · exact congr_arg _ ( by exact? );
            · exact congr_arg _ ( by exact? );
          · -- Since `pushMany` appends elements to the array, the element at position `k` in the new array is either in the original `out` or is one of the appended elements.
            have h_append : (pushMany (-50000 + Int.ofNat i) counts[i]! out)[‹ℕ›]! = -50000 + Int.ofNat i := by
              have h_append : (pushMany (-50000 + Int.ofNat i) counts[i]! out).toList = out.toList ++ List.replicate counts[i]! (-50000 + Int.ofNat i) := by
                exact?;
              cases h : pushMany ( -50000 + Int.ofNat i ) counts[i]! out ; aesop;
            cases out ; aesop;
        · omega

/-
PROVIDED SOLUTION
Induction on counts.size - i (well-founded, matching emit's definition).

Base case: i ≥ counts.size. emit returns out. out satisfies allInRange by h_inRange. ✓

Inductive step: i < counts.size. emit counts i out = emit counts (i+1) (pushMany v c out) where c = counts[i]!, v = -50000 + i.
Since h_counts_size: counts.size = kSize = 100001 and i < 100001, we have i ≤ 100000, so v = -50000 + i ∈ [-50000, 50000] = [minVal, maxVal].

Apply IH with out' = pushMany v c out. Need:
1. allInRange out': pushMany appends copies of v to out. All original elements are in range by h_inRange. New elements equal v which is in [minVal, maxVal]. So allInRange out'. Use pushMany_toList to reason about elements.
2. i + 1 ≤ kSize: since i < kSize.
3. counts.size = kSize: unchanged.

Key: allInRange (pushMany v c out) when allInRange out and minVal ≤ v ≤ maxVal. This follows from the fact that pushMany appends v's to out, and getElem! on the extended array returns either an existing element (in range) or v (in range).
-/
lemma emit_inRange (counts : Array Nat) (i : Nat) (out : Array Int)
    (h_inRange : allInRange out)
    (h_i : i ≤ kSize)
    (h_counts_size : counts.size = kSize) :
    allInRange (emit counts i out) := by
      -- By induction on counts.size - i, we can show that all elements in the emitted array are within the range.
      induction' h : counts.size - i with m ih generalizing counts i out;
      · unfold emit;
        grind;
      · convert ih counts ( i + 1 ) ( pushMany ( -50000 + Int.ofNat i ) ( counts[i]! ) out ) _ _ _ _ using 1;
        · rw [ emit ] ; aesop;
        · intro j hj
          by_cases hj' : j < out.size;
          · -- Since $j < \text{out.size}$, the element at position $j$ in the new array is the same as the element at position $j$ in the original array.
            have h_eq : (pushMany (-50000 + Int.ofNat i) counts[i]! out)[j]! = out[j]! := by
              have h_eq : (pushMany (-50000 + Int.ofNat i) counts[i]! out).toList = out.toList ++ List.replicate counts[i]! (-50000 + Int.ofNat i) := by
                exact?;
              cases h : pushMany ( -50000 + Int.ofNat i ) counts[i]! out ; aesop;
            exact h_eq.symm ▸ h_inRange j hj';
          · -- Since $j \geq \text{out.size}$, we have $(pushMany (-50000 + Int.ofNat i) counts[i]! out)[j]! = -50000 + Int.ofNat i$.
            have h_pushMany : (pushMany (-50000 + Int.ofNat i) counts[i]! out)[j]! = -50000 + Int.ofNat i := by
              have h_pushMany : (pushMany (-50000 + Int.ofNat i) counts[i]! out).toList = out.toList ++ List.replicate counts[i]! (-50000 + Int.ofNat i) := by
                exact?;
              cases h : pushMany ( -50000 + Int.ofNat i ) counts[i]! out ; aesop;
            simp_all +decide [ minVal, maxVal ];
            exact Nat.le_of_lt_succ ( Nat.lt_of_sub_eq_succ h );
        · omega;
        · exact h_counts_size;
        · omega

end EmitLemmas

section Proof

/-
PROBLEM
Count array total equals input size

PROVIDED SOLUTION
We need: ∑ j ∈ Finset.range kSize, (buildCounts nums)[j]! = nums.size.

Since precondition nums holds (all elements are in range), every element v of nums has idxOf v < kSize and contributes exactly 1 to the count at index idxOf v. The total sum of all counts equals the total number of elements.

More formally: buildCounts_spec tells us that for each v in range, (buildCounts nums)[idxOf v]! = nums.count v.

The sum ∑ j ∈ range kSize, (buildCounts nums)[j]! can be rewritten. For each j, (buildCounts nums)[j]! counts how many elements of nums map to index j. The total sum counts every element exactly once, so it equals nums.size.

Alternative approach: prove this by induction on nums (via foldl), showing the sum is preserved. Initial sum = ∑ j, 0 = 0 = #[].size. Each step adds one element, incrementing one count by 1, so the sum increases by 1, matching the size increase.

Actually, the cleanest approach: induction on nums.toList.
- Base: foldl over [] gives Array.replicate kSize 0. Sum = 0 = 0.
- Step: foldl over (x :: xs) = foldl over xs starting from incAt init (idxOf x). Sum of incAt cs i = sum of cs + (if i < cs.size then 1 else 0). Since precondition ensures x is in range, idxOf x < kSize = cs.size, so sum increases by 1. And nums.size increases by 1.
-/
lemma buildCounts_total (nums : Array Int) (h : precondition nums) :
    ∑ j ∈ Finset.range kSize, (buildCounts nums)[j]! = nums.size := by
      have h_sum : ∀ (xs : List ℤ), (∀ x ∈ xs, minVal ≤ x ∧ x ≤ maxVal) → ∑ j ∈ Finset.range kSize, (List.foldl (fun cs w => incAt cs (idxOf w)) (Array.replicate kSize 0) xs)[j]! = xs.length := by
        intro xs hxs;
        induction' xs using List.reverseRecOn with xs ih <;> norm_num at *;
        · grind;
        · rename_i h; specialize h ( fun x hx => hxs x ( Or.inl hx ) ) ; rw [ ← h ] ; rw [ Finset.sum_eq_add_sum_diff_singleton ( show idxOf ih ∈ Finset.range kSize from Finset.mem_range.mpr <| idxOf_lt_kSize _ <| hxs _ <| Or.inr rfl ) ] ; simp +decide [ incAt ] ;
          split_ifs <;> simp_all +decide [ Finset.sum_eq_add_sum_diff_singleton ( show idxOf ih ∈ Finset.range kSize from Finset.mem_range.mpr <| idxOf_lt_kSize _ <| hxs _ <| Or.inr rfl ) ];
          · rw [ Finset.sum_congr rfl fun x hx => ?_ ];
            rotate_left;
            use fun x => ( List.foldl ( fun cs w => if idxOf w < cs.size then cs.setIfInBounds ( idxOf w ) ( cs[idxOf w]! + 1 ) else cs ) ( Array.replicate kSize 0 ) xs )[ x ]!;
            · grind;
            · ring;
          · have h_size : ∀ (xs : List ℤ), (∀ x ∈ xs, minVal ≤ x ∧ x ≤ maxVal) → (List.foldl (fun cs w => incAt cs (idxOf w)) (Array.replicate kSize 0) xs).size = kSize := by
              intro xs hxs; induction' xs using List.reverseRecOn with xs ih <;> norm_num at *;
              rw [ incAt_size, ‹ ( ∀ x ∈ xs, minVal ≤ x ∧ x ≤ maxVal ) → ( List.foldl ( fun cs w => incAt cs ( idxOf w ) ) ( Array.replicate kSize 0 ) xs ).size = kSize › fun x hx => hxs x <| Or.inl hx ];
            exact absurd ‹ ( List.foldl ( fun cs w => if idxOf w < cs.size then cs.setIfInBounds ( idxOf w ) ( cs[idxOf w]! + 1 ) else cs ) ( Array.replicate kSize 0 ) xs ).size ≤ idxOf ih › ( by erw [ h_size xs fun x hx => hxs x ( Or.inl hx ) ] ; exact not_le_of_gt ( idxOf_lt_kSize _ ( hxs _ ( Or.inr rfl ) ) ) );
      convert h_sum nums.toList _ ; aesop;
      intro x hx;
      obtain ⟨ i, hi ⟩ := List.mem_iff_get.mp hx;
      specialize h i ; aesop

/-
PROVIDED SOLUTION
Unfold postcondition. We need to prove 4 things about implementation nums = emit (buildCounts nums) 0 #[] (by implementation_eq).

Let counts = buildCounts nums. counts.size = kSize (by buildCounts_size).

1. SIZE: (emit counts 0 #[]).size = nums.size.
   By emit_size: size = 0 + ∑ j ∈ Ico 0 kSize, counts[j]! = ∑ j ∈ Ico 0 kSize, counts[j]!.
   Finset.Ico 0 kSize = Finset.range kSize.
   By buildCounts_total: this sum = nums.size. ✓

2. SORTED: isSortedNondecreasing (emit counts 0 #[]).
   By emit_sorted with out = #[], which is trivially sorted and has no elements so h_bound is vacuously true. ✓

3. IN_RANGE: allInRange (emit counts 0 #[]).
   By emit_inRange with out = #[] (trivially allInRange), i = 0 ≤ kSize, counts.size = kSize. ✓

4. PERMUTATION: ∀ v, (emit counts 0 #[]).count v = nums.count v.
   By emit_count: (emit counts 0 #[]).count v = (#[]).count v + ∑ j ∈ Ico 0 kSize, (if (-50000 + j) == v then counts[j]! else 0).
   = 0 + ∑ j ∈ Ico 0 kSize, (if (-50000 + j) == v then counts[j]! else 0).

   Case 1: v is in range [minVal, maxVal]. Let j₀ = idxOf v. Then (-50000 + j₀) = v.
   By buildCounts_spec: counts[j₀]! = nums.count v.
   For j ≠ j₀ with (-50000 + j) == v: this means -50000 + j = v, so j = v + 50000 = j₀. Contradiction.
   So the sum = counts[j₀]! = nums.count v. ✓

   Case 2: v is NOT in range. Then no j ∈ [0, kSize) satisfies -50000 + j = v (since -50000 + j ranges over [-50000, 50000] for j ∈ [0, 100000]).
   So the sum = 0. And nums.count v = 0 since all elements of nums are in range (by precondition) but v is not. ✓

For case 2, we need: if precondition nums and v ∉ [minVal, maxVal], then nums.count v = 0.
-/
theorem correctness_goal
    (nums : Array Int)
    (h_precond : precondition nums)
    : postcondition nums (implementation nums) := by
  refine' And.intro _ ( And.intro _ _ );
  · rw [ implementation_eq, emit_size ];
    rw [ buildCounts_size, Finset.sum_Ico_eq_sum_range ];
    simpa using buildCounts_total nums h_precond;
  · rw [ implementation_eq ];
    apply_rules [ emit_sorted ];
    · exact fun i j hij hj => by cases i <;> cases j <;> trivial;
    · decide +revert;
  · refine' ⟨ _, _ ⟩;
    · rw [ implementation_eq ];
      exact emit_inRange _ _ _ ( by unfold allInRange; aesop ) ( by norm_num ) ( buildCounts_size _ );
    · intro v
      by_cases hv : minVal ≤ v ∧ v ≤ maxVal;
      · -- Since v is in the range [minVal, maxVal], there exists a unique j in [0, kSize) such that (-50000 + j) = v. This j is exactly idxOf v.
        obtain ⟨j, hj⟩ : ∃ j ∈ Finset.range kSize, (-50000 + Int.ofNat j) = v := by
          unfold minVal maxVal kSize at *; norm_num at *; exact ⟨ Int.toNat ( v + 50000 ), by norm_num; omega, by norm_num; omega ⟩ ;
        -- By definition of `emit`, we know that the count of `v` in the emitted array is equal to the count of `v` in the original array.
        have h_count : (emit (buildCounts nums) 0 #[]).count v = (buildCounts nums)[j]! := by
          rw [ emit_count ];
          rw [ Finset.sum_eq_single j ] <;> aesop;
        convert h_count using 1;
        · rw [ implementation_eq ];
        · convert buildCounts_spec nums v hv h_precond |> Eq.symm using 1;
          unfold idxOf; aesop;
      · -- Since $v$ is not in the range $[-50000, 50000]$, it cannot be in the input array $nums$.
        have h_not_in_nums : ¬∃ i, i < nums.size ∧ nums[i]! = v := by
          exact fun ⟨ i, hi, hi' ⟩ => hv ⟨ by linarith [ h_precond i hi ], by linarith [ h_precond i hi ] ⟩;
        rw [ show Array.count v nums = 0 from _ ];
        · rw [ implementation_eq, emit_count ];
          rw [ Finset.sum_eq_zero ] ; aesop;
          intro x hx; split_ifs <;> simp_all +decide [ minVal, maxVal ] ;
          exact absurd ( hv ( by linarith ) ) ( by linarith [ show ( x : ℤ ) ≤ 100000 by exact_mod_cast Nat.le_of_lt_succ ( by linarith [ show ( buildCounts nums ).size = 100001 by exact buildCounts_size nums ] ) ] );
        · rw [ Array.count_eq_zero ];
          contrapose! h_not_in_nums;
          obtain ⟨ i, hi ⟩ := Array.mem_iff_getElem.mp h_not_in_nums; use i; aesop;

end Proof
