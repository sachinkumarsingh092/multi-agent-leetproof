import Velvet.Std
import Extensions.Tactics
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false
set_option pp.funBinderTypes true
set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

/- Problem Description
    1539. Kth Missing Positive Number: Given a strictly increasing array of positive integers `arr` and a positive integer `k`, return the k-th positive integer that does not appear in `arr`.
    **Important: complexity should be O(log n) time and O(1) space**
    Natural language breakdown:
    1. The input `arr` is an array of natural numbers, intended to represent positive integers.
    2. The array is strictly increasing: each element is less than the next element.
    3. A positive integer `m` is considered “missing” if `m ≥ 1` and `m` is not an element of `arr`.
    4. For any `n ≥ 1`, we can count how many missing positive integers are in the range `[1, n]`.
    5. The desired output `result` is the unique positive integer such that:
       a. `result` is missing from `arr`.
       b. Exactly `k-1` missing positive integers are ≤ `result - 1`.
       c. Exactly `k` missing positive integers are ≤ `result`.
    6. These properties characterize the k-th missing positive integer without prescribing an algorithm.
-/

section Specs
-- Boolean membership check for arrays of naturals.
-- We use Bool equality (==) to keep this decidable/computable.
def inArrayB (arr : Array Nat) (x : Nat) : Bool :=
  arr.any (fun y => y == x)

-- `arr` is strictly increasing.
def strictlyIncreasing (arr : Array Nat) : Prop :=
  ∀ (i : Nat), i + 1 < arr.size → arr[i]! < arr[i + 1]!

-- Every element of `arr` is positive.
def allPositive (arr : Array Nat) : Prop :=
  ∀ (i : Nat), i < arr.size → 0 < arr[i]!

-- Number of missing positive integers in the interval [1, n].
-- This is a computable definition using `Finset.Icc` and filtering by membership in `arr`.
def missingUpTo (arr : Array Nat) (n : Nat) : Nat :=
  ((Finset.Icc (1 : Nat) n).filter (fun m => !(inArrayB arr m))).card

-- Preconditions
-- `k` is positive and `arr` satisfies the problem's input constraints.
def precondition (arr : Array Nat) (k : Nat) : Prop :=
  k > 0 ∧ strictlyIncreasing arr ∧ allPositive arr

-- Postconditions
-- `result` is the k-th missing positive integer:
-- it is missing itself, and the missing-count just below it is k-1 while up to it is k.
def postcondition (arr : Array Nat) (k : Nat) (result : Nat) : Prop :=
  0 < result ∧
  inArrayB arr result = false ∧
  missingUpTo arr (Nat.pred result) = k - 1 ∧
  missingUpTo arr result = k
end Specs

section Impl
method KthMissingPositiveNumber (arr : Array Nat) (k : Nat)
  return (result : Nat)
  require precondition arr k
  ensures postcondition arr k result
  do
  -- Binary search on the answer value `x`.
  -- Define missing count up to x as: x - (# of arr elements ≤ x).
  -- With strictly increasing positive arr, this is monotone in x.

  let n := arr.size

  -- Compute an upper bound `hi` such that missingUpTo arr hi ≥ k.
  -- For an array of size n, among numbers 1..(n+k), at most n appear in arr,
  -- so at least k are missing.
  let hi := n + k
  let mut lo : Nat := 1
  let mut r : Nat := hi

  -- Standard lower_bound for the smallest x with missingCount(x) ≥ k.
  while lo < r
    -- Search interval is well-formed and stays within [1, hi].
    invariant "inv_outer_bounds" (1 ≤ lo ∧ lo ≤ r ∧ r ≤ hi)
    -- `hi`/`n` are definitions we can rewrite with.
    invariant "inv_outer_defs" (n = arr.size ∧ hi = n + k)
    -- Keep the input assumptions available inside the loop.
    invariant "inv_outer_input" (strictlyIncreasing arr ∧ allPositive arr ∧ k > 0)
    -- Bracket the k-th missing: below `lo` there are < k missing,
    -- while at `r` there are at least k missing.
    invariant "inv_outer_bracket_lo" (missingUpTo arr (Nat.pred lo) < k)
    invariant "inv_outer_bracket_r" (k ≤ missingUpTo arr r)
    decreasing r - lo
  do
    let mid := lo + (r - lo) / 2

    -- Count how many array elements are ≤ mid via binary search on indices.
    let mut l2 : Nat := 0
    let mut r2 : Nat := n
    while l2 < r2
      -- Index window is well-formed within [0,n].
      invariant "inv_inner_bounds" (l2 ≤ r2 ∧ r2 ≤ n)
      invariant "inv_inner_defs" (n = arr.size)
      -- All elements strictly left of `l2` are ≤ mid.
      invariant "inv_inner_left" (∀ i, i < l2 → arr[i]! ≤ mid)
      -- All elements at/after `r2` are > mid.
      invariant "inv_inner_right" (∀ i, r2 ≤ i ∧ i < n → mid < arr[i]!)
      decreasing r2 - l2
    do
      let m2 := l2 + (r2 - l2) / 2
      if arr[m2]! <= mid then
        l2 := m2 + 1
      else
        r2 := m2

    let countLe := l2
    let missingCount := mid - countLe

    if missingCount < k then
      lo := mid + 1
    else
      r := mid

  return lo
end Impl

section TestCases
-- Test case 1: Example 1
-- arr = [2,3,4,7,11], k = 5 => 9
def test1_arr : Array Nat := #[2, 3, 4, 7, 11]
def test1_k : Nat := 5
def test1_Expected : Nat := 9

-- Test case 2: Example 2
-- arr = [1,2,3,4], k = 2 => 6
def test2_arr : Array Nat := #[1, 2, 3, 4]
def test2_k : Nat := 2
def test2_Expected : Nat := 6

-- Test case 3: Empty array (vacuously strictly increasing); missing positives are [1,2,3,...]
def test3_arr : Array Nat := #[]
def test3_k : Nat := 1
def test3_Expected : Nat := 1

-- Test case 4: Single element not starting at 1
-- arr = [2]; missing positives are [1,3,4,...]
def test4_arr : Array Nat := #[2]
def test4_k : Nat := 1
def test4_Expected : Nat := 1

-- Test case 5: Single element starting at 1
-- arr = [1]; missing positives are [2,3,4,...]
def test5_arr : Array Nat := #[1]
def test5_k : Nat := 1
def test5_Expected : Nat := 2

-- Test case 6: Small gap inside array
-- arr = [1,3]; missing positives are [2,4,5,...]
def test6_arr : Array Nat := #[1, 3]
def test6_k : Nat := 1
def test6_Expected : Nat := 2

-- Test case 7: First few positives missing before the first element
-- arr = [5,6,7]; missing positives are [1,2,3,4,8,9,...]
def test7_arr : Array Nat := #[5, 6, 7]
def test7_k : Nat := 2
def test7_Expected : Nat := 2

-- Test case 8: Large jump later in the array
-- arr = [1,2,100]; missing positives are [3..99] then [101..]
-- 97th missing is 99
def test8_arr : Array Nat := #[1, 2, 100]
def test8_k : Nat := 97
def test8_Expected : Nat := 99

-- Test case 9: Same array as example 1 but smallest valid k
-- missing positives start with 1
def test9_arr : Array Nat := #[2, 3, 4, 7, 11]
def test9_k : Nat := 1
def test9_Expected : Nat := 1
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((KthMissingPositiveNumber test1_arr test1_k).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((KthMissingPositiveNumber test2_arr test2_k).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((KthMissingPositiveNumber test3_arr test3_k).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((KthMissingPositiveNumber test4_arr test4_k).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((KthMissingPositiveNumber test5_arr test5_k).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((KthMissingPositiveNumber test6_arr test6_k).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((KthMissingPositiveNumber test7_arr test7_k).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((KthMissingPositiveNumber test8_arr test8_k).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((KthMissingPositiveNumber test9_arr test9_k).run), DivM.res test9_Expected ]
end Assertions

section Pbt
velvet_plausible_test KthMissingPositiveNumber (config := { maxMs := some 20000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000

theorem goal_0
    (arr : Array ℕ)
    (lo : ℕ)
    (r : ℕ)
    (a_3 : ∀ (i : ℕ), i + OfNat.ofNat 1 < arr.size → arr[i]! < arr[i + OfNat.ofNat 1]!)
    (l2 : ℕ)
    (r2 : ℕ)
    (a_6 : l2 ≤ r2)
    (a_7 : r2 ≤ arr.size)
    (if_pos_1 : l2 < r2)
    (if_pos_2 : arr[l2 + (r2 - l2) / OfNat.ofNat 2]! ≤ lo + (r - lo) / OfNat.ofNat 2)
    : ∀ i < l2 + (r2 - l2) / OfNat.ofNat 2 + OfNat.ofNat 1, arr[i]! ≤ lo + (r - lo) / OfNat.ofNat 2 := by
  let mid : Nat := lo + (r - lo) / 2
  let m2 : Nat := l2 + (r2 - l2) / 2

  have if_pos_2' : arr[m2]! ≤ mid := by
    simpa [mid, m2] using if_pos_2

  have hm2_lt_r2 : m2 < r2 := by
    have hpos : 0 < r2 - l2 := Nat.sub_pos_of_lt if_pos_1
    have hdiv : (r2 - l2) / 2 < r2 - l2 :=
      Nat.div_lt_self hpos (by decide : 1 < (2 : Nat))
    have h := Nat.add_lt_add_left hdiv l2
    -- `l2 + (r2 - l2) = r2` since `l2 ≤ r2`.
    simpa [m2, Nat.add_sub_of_le a_6] using h

  have hm2_lt_size : m2 < arr.size := lt_of_lt_of_le hm2_lt_r2 a_7

  -- Adjacent strict increase implies monotonicity on indices.
  have mono : ∀ {i j : Nat}, i ≤ j → j < arr.size → arr[i]! ≤ arr[j]! := by
    intro i j hij hj
    induction j with
    | zero =>
        have hi0 : i = 0 := Nat.eq_zero_of_le_zero (by simpa using hij)
        subst hi0
        simp
    | succ j ih =>
        have hj' : j < arr.size := Nat.lt_of_succ_lt hj
        cases lt_or_eq_of_le hij with
        | inr hEq =>
            subst hEq
            simp
        | inl hLt =>
            have hij' : i ≤ j := Nat.le_of_lt_succ hLt
            have hle : arr[i]! ≤ arr[j]! := ih hij' hj'
            have hlt : arr[j]! < arr[j + 1]! := a_3 j (by simpa using hj)
            exact le_trans hle (Nat.le_of_lt hlt)

  intro i hi
  have hi' : i < Nat.succ m2 := by
    -- Goal is `i < m2 + 1` after rewriting.
    simpa [Nat.succ_eq_add_one, m2, Nat.add_assoc] using hi
  have hie : i ≤ m2 := Nat.le_of_lt_succ hi'
  have hle : arr[i]! ≤ arr[m2]! := mono hie hm2_lt_size
  exact le_trans hle if_pos_2'

theorem goal_1
    (arr : Array ℕ)
    (lo : ℕ)
    (r : ℕ)
    (a : OfNat.ofNat 1 ≤ lo)
    (a_3 : ∀ (i : ℕ), i + OfNat.ofNat 1 < arr.size → arr[i]! < arr[i + OfNat.ofNat 1]!)
    (l2 : ℕ)
    (r2 : ℕ)
    (if_neg : lo + (r - lo) / OfNat.ofNat 2 < arr[l2 + (r2 - l2) / OfNat.ofNat 2]!)
    : ∀ (i : ℕ), l2 + (r2 - l2) / OfNat.ofNat 2 ≤ i → i < arr.size → lo + (r - lo) / OfNat.ofNat 2 < arr[i]! := by
  -- Derive a general monotonicity lemma from the adjacent-step strict increase.
  have hmono : ∀ {p q : Nat}, p < q → q < arr.size → arr[p]! < arr[q]! := by
    intro p q hpq hq
    -- Strong induction on q.
    have hmono_all : ∀ q : Nat, (q < arr.size → ∀ p : Nat, p < q → arr[p]! < arr[q]!) := by
      intro q
      refine Nat.strong_induction_on q (fun q ih => ?_)
      intro hq p hpq
      have hp1le : p + 1 ≤ q := Nat.succ_le_of_lt hpq
      cases Nat.eq_or_lt_of_le hp1le with
      | inl hp1eq =>
          -- q = p+1
          subst hp1eq
          -- now `hq : p+1 < arr.size`
          simpa using (a_3 p (by simpa using hq))
      | inr hp1lt =>
          -- p+1 < q, so compare via q-1.
          have qpos : 0 < q := lt_trans (Nat.succ_pos p) hp1lt
          have h1leq : 1 ≤ q := Nat.succ_le_of_lt qpos
          have hqpred_lt_q : q - 1 < q := by
            exact Nat.sub_lt_self (by decide : 0 < (1 : Nat)) h1leq
          have hqpred_lt_size : q - 1 < arr.size := lt_trans hqpred_lt_q hq
          have hp1le_pred : p + 1 ≤ q - 1 := by
            -- `le_pred_of_lt` gives `p+1 ≤ pred q`.
            simpa [Nat.pred_eq_sub_one] using (Nat.le_pred_of_lt hp1lt)
          have hp_lt_pred : p < q - 1 :=
            lt_of_lt_of_le (Nat.lt_succ_self p) hp1le_pred
          have hstep1 : arr[p]! < arr[q - 1]! :=
            (ih (q - 1) hqpred_lt_q) hqpred_lt_size p hp_lt_pred
          have hqsubadd : q - 1 + 1 = q := Nat.sub_add_cancel h1leq
          have hqpred_succ_lt_size : q - 1 + 1 < arr.size := by
            simpa [hqsubadd] using hq
          have hstep2 : arr[q - 1]! < arr[(q - 1) + 1]! :=
            a_3 (q - 1) (by simpa using hqpred_succ_lt_size)
          have hstep2' : arr[q - 1]! < arr[q]! := by
            simpa [hqsubadd] using hstep2
          exact lt_trans hstep1 hstep2'
    exact hmono_all q hq p hpq

  intro i hge hi
  -- Split `m2 ≤ i` into `i = m2` or `m2 < i`.
  cases eq_or_lt_of_le hge with
  | inl hEq =>
      simpa [hEq] using if_neg
  | inr hLt =>
      have harr : arr[l2 + (r2 - l2) / 2]! < arr[i]! := hmono hLt hi
      exact lt_trans if_neg harr

theorem goal_2
    (arr : Array ℕ)
    (k : ℕ)
    (lo : ℕ)
    (r : ℕ)
    (a_3 : ∀ (i : ℕ), i + OfNat.ofNat 1 < arr.size → arr[i]! < arr[i + OfNat.ofNat 1]!)
    (a_4 : ∀ i < arr.size, OfNat.ofNat 0 < arr[i]!)
    (i : ℕ)
    (r2_1 : ℕ)
    (if_pos_1 : lo + (r - lo) / OfNat.ofNat 2 - i < k)
    (invariant_inv_inner_left : ∀ i_1 < i, arr[i_1]! ≤ lo + (r - lo) / OfNat.ofNat 2)
    (a_7 : r2_1 ≤ arr.size)
    (a_6 : i ≤ r2_1)
    (done_2 : r2_1 ≤ i)
    : {m ∈ Finset.Icc (OfNat.ofNat 1) (lo + (r - lo) / OfNat.ofNat 2) | ∀ (i : ℕ) (x : i < arr.size), ¬arr[i] = m}.card < k := by
  classical
  set mid : Nat := lo + (r - lo) / 2

  have hi_eq : i = r2_1 := le_antisymm a_6 done_2
  have hi_le_size : i ≤ arr.size := by
    simpa [hi_eq] using a_7

  have getBang_eq_getElem (j : Nat) (hj : j < arr.size) : arr[j]! = arr[j]'hj := by
    simp [Array.getElem!_eq_getD, Array.getD, hj]

  have lt_of_index_lt : ∀ {n m : Nat}, n < m → m < arr.size → arr[n]! < arr[m]! := by
    intro n m hnm hm
    induction m generalizing n with
    | zero =>
        exact (Nat.not_lt_zero _ hnm).elim
    | succ m0 ih =>
        have hm0 : m0 < arr.size := lt_trans (Nat.lt_succ_self m0) hm
        have hnm' : n < m0 ∨ n = m0 := Nat.lt_succ_iff_lt_or_eq.mp hnm
        cases hnm' with
        | inl hlt =>
            have h1 : arr[n]! < arr[m0]! := ih hlt hm0
            have h2 : arr[m0]! < arr[m0 + 1]! := a_3 m0 (by simpa using hm)
            exact lt_trans h1 h2
        | inr heq =>
            subst heq
            exact a_3 _ (by simpa using hm)

  let f : Fin i → Nat := fun x => arr[x.1]'(lt_of_lt_of_le x.2 hi_le_size)

  have hf_strict : StrictMono f := by
    intro x y hxy
    have hxsize : (x.1 : Nat) < arr.size := lt_of_lt_of_le x.2 hi_le_size
    have hysize : (y.1 : Nat) < arr.size := lt_of_lt_of_le y.2 hi_le_size
    have hlt : arr[x.1]! < arr[y.1]! := lt_of_index_lt (n := x.1) (m := y.1) hxy hysize
    simpa [f, getBang_eq_getElem, hxsize, hysize] using hlt

  have hf_inj : Function.Injective f := hf_strict.injective

  let S : Finset Nat := Finset.Icc 1 mid
  let P : Finset Nat := (Finset.univ : Finset (Fin i)).image f

  have hPsub : P ⊆ S := by
    intro m hm
    rcases Finset.mem_image.mp hm with ⟨x, hx, rfl⟩
    have hxsize : (x.1 : Nat) < arr.size := lt_of_lt_of_le x.2 hi_le_size
    have hxpos : 0 < arr[x.1]'hxsize := by
      have : 0 < arr[x.1]! := a_4 x.1 hxsize
      simpa [getBang_eq_getElem x.1 hxsize] using this
    have hxle : arr[x.1]'hxsize ≤ mid := by
      have : arr[x.1]! ≤ mid := by
        simpa [mid] using (invariant_inv_inner_left x.1 x.2)
      simpa [getBang_eq_getElem x.1 hxsize] using this
    have hxge : 1 ≤ arr[x.1]'hxsize := Nat.succ_le_of_lt hxpos
    refine (Finset.mem_Icc).2 ?_
    refine ⟨?_, ?_⟩
    · simpa [f] using hxge
    · simpa [f] using hxle

  have hMsub :
      {m ∈ S | ∀ (j : ℕ) (x : j < arr.size), ¬arr[j] = m} ⊆ S \ P := by
    intro m hm
    have hmS : m ∈ S := (Finset.mem_filter.mp hm).1
    have hmMiss : ∀ (j : ℕ) (x : j < arr.size), ¬arr[j] = m := (Finset.mem_filter.mp hm).2
    have hmnotP : m ∉ P := by
      intro hmP
      rcases Finset.mem_image.mp hmP with ⟨x, hx, hxEq⟩
      have hxsize : (x.1 : Nat) < arr.size := lt_of_lt_of_le x.2 hi_le_size
      have : arr[x.1]'hxsize = m := by
        simpa [P, f] using hxEq
      exact (hmMiss x.1 hxsize) (by simpa using this)
    simp [Finset.mem_sdiff, hmS, hmnotP]

  have hScard : S.card = mid := by
    simpa [S, Nat.card_Icc, mid]

  have hPcard : P.card = i := by
    simpa [P] using
      (Finset.card_image_of_injective (s := (Finset.univ : Finset (Fin i))) (f := f) hf_inj)

  have hMle :
      ({m ∈ S | ∀ (j : ℕ) (x : j < arr.size), ¬arr[j] = m}).card ≤ mid - i := by
    have h1 : ({m ∈ S | ∀ (j : ℕ) (x : j < arr.size), ¬arr[j] = m}).card ≤ (S \ P).card := by
      exact Finset.card_le_card hMsub

    have hPS : P ∩ S = P := by
      ext x
      constructor
      · intro hx
        exact (Finset.mem_inter.mp hx).1
      · intro hx
        exact Finset.mem_inter.mpr ⟨hx, hPsub hx⟩

    have h2 : (S \ P).card = S.card - P.card := by
      have h := (Finset.card_sdiff (s := P) (t := S))
      -- h : (S \ P).card = S.card - (P ∩ S).card
      simpa [hPS] using h

    have : ({m ∈ S | ∀ (j : ℕ) (x : j < arr.size), ¬arr[j] = m}).card ≤ S.card - P.card := by
      simpa [h2] using h1
    simpa [hScard, hPcard] using this

  have hmid_lt : mid - i < k := by
    simpa [mid] using if_pos_1

  have hgoal : ({m ∈ S | ∀ (j : ℕ) (x : j < arr.size), ¬arr[j] = m}).card < k :=
    lt_of_le_of_lt hMle hmid_lt

  simpa [S, mid] using hgoal

theorem goal_3
    (arr : Array ℕ)
    (k : ℕ)
    (lo : ℕ)
    (r : ℕ)
    (a : OfNat.ofNat 1 ≤ lo)
    (a_4 : ∀ i < arr.size, OfNat.ofNat 0 < arr[i]!)
    (i : ℕ)
    (r2_1 : ℕ)
    (invariant_inv_inner_left : ∀ i_1 < i, arr[i_1]! ≤ lo + (r - lo) / OfNat.ofNat 2)
    (a_7 : r2_1 ≤ arr.size)
    (invariant_inv_inner_right : ∀ (i : ℕ), r2_1 ≤ i → i < arr.size → lo + (r - lo) / OfNat.ofNat 2 < arr[i]!)
    (a_6 : i ≤ r2_1)
    (if_neg : k ≤ lo + (r - lo) / OfNat.ofNat 2 - i)
    (done_2 : r2_1 ≤ i)
    : k ≤ {m ∈ Finset.Icc (OfNat.ofNat 1) (lo + (r - lo) / OfNat.ofNat 2) | ∀ (i : ℕ) (x : i < arr.size), ¬arr[i] = m}.card := by
  classical
  have hir : i = r2_1 := le_antisymm a_6 done_2
  have hi : i ≤ arr.size := by
    simpa [hir] using a_7

  set mid : Nat := lo + (r - lo) / 2

  have hbang (j : Nat) (hj : j < arr.size) : arr[j]! = arr[j]'hj := by
    simp [Array.getElem!_eq_getD, Array.getD, Array.get?_eq_getElem?, hj]

  let f : Fin i → Nat := fun t => arr[t.1]!
  let S : Finset Nat := (Finset.univ : Finset (Fin i)).image f

  have hS_sub : S ⊆ Finset.Icc 1 mid := by
    intro m hm
    rcases Finset.mem_image.1 hm with ⟨t, htU, rfl⟩
    have ht' : t.1 < arr.size := lt_of_lt_of_le t.2 hi
    have hpos0 : 0 < arr[t.1]! := by
      simpa using a_4 t.1 ht'
    have hpos1 : 1 ≤ arr[t.1]! := Nat.succ_le_of_lt hpos0
    have hle : arr[t.1]! ≤ mid := by
      simpa [mid] using (invariant_inv_inner_left t.1 t.2)
    exact Finset.mem_Icc.2 ⟨hpos1, hle⟩

  have hS_card : S.card ≤ i := by
    have : S.card ≤ (Finset.univ : Finset (Fin i)).card := by
      simpa [S] using (Finset.card_image_le (s := (Finset.univ : Finset (Fin i))) (f := f))
    simpa using this

  have hIcc_card : (Finset.Icc (1 : Nat) mid).card = mid := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using (Nat.card_Icc (a := (1 : Nat)) (b := mid))

  have hforall_iff_notmem (m : Nat) (hm : m ∈ Finset.Icc (1 : Nat) mid) :
      (∀ (j : Nat) (x : j < arr.size), ¬arr[j] = m) ↔ m ∉ S := by
    constructor
    · intro hall hmS
      rcases Finset.mem_image.1 hmS with ⟨t, htU, rfl⟩
      have ht' : t.1 < arr.size := lt_of_lt_of_le t.2 hi
      have : ¬arr[t.1] = arr[t.1]! := hall t.1 ht'
      exact this (by simpa [hbang t.1 ht'])
    · intro hnotS j x
      intro hEq
      have hm_le : m ≤ mid := (Finset.mem_Icc.1 hm).2
      have hjlt : j < i := by
        by_contra hge
        have hij : i ≤ j := le_of_not_gt hge
        have hr2j : r2_1 ≤ j := by
          simpa [hir] using hij
        have hgtBang : mid < arr[j]! := by
          simpa [mid] using (invariant_inv_inner_right j hr2j x)
        have hEqBang : arr[j]! = m := by
          simpa [hbang j x] using hEq
        have : mid < m := by
          simpa [hEqBang] using hgtBang
        exact (Nat.not_lt_of_ge hm_le) this
      have hEqBang : arr[j]! = m := by
        simpa [hbang j x] using hEq
      have hmS : m ∈ S := by
        refine Finset.mem_image.2 ?_
        refine ⟨⟨j, hjlt⟩, by simp, ?_⟩
        simpa [f, hEqBang]
      exact hnotS hmS

  have hMissing_eq :
      {m ∈ Finset.Icc (1 : Nat) mid | ∀ (j : Nat) (x : j < arr.size), ¬arr[j] = m}
        = (Finset.Icc (1 : Nat) mid) \ S := by
    ext m
    constructor
    · intro hm
      have hm' : m ∈ Finset.Icc (1 : Nat) mid ∧ (∀ (j : Nat) (x : j < arr.size), ¬arr[j] = m) := by
        simpa using hm
      have hnot : m ∉ S := (hforall_iff_notmem m hm'.1).1 hm'.2
      have : m ∈ Finset.Icc (1 : Nat) mid ∧ m ∉ S := ⟨hm'.1, hnot⟩
      simpa [Finset.mem_sdiff] using this
    · intro hm
      have hm' : m ∈ Finset.Icc (1 : Nat) mid ∧ m ∉ S := by
        simpa [Finset.mem_sdiff] using hm
      have hall : ∀ (j : Nat) (x : j < arr.size), ¬arr[j] = m :=
        (hforall_iff_notmem m hm'.1).2 hm'.2
      have : m ∈ Finset.Icc (1 : Nat) mid ∧ (∀ (j : Nat) (x : j < arr.size), ¬arr[j] = m) := ⟨hm'.1, hall⟩
      simpa using this

  have hk : k ≤ mid - i := by
    simpa [mid] using if_neg

  have hmid_le_missing : mid - i ≤ ((Finset.Icc (1 : Nat) mid) \ S).card := by
    have : mid - i ≤ mid - S.card := Nat.sub_le_sub_left hS_card mid
    have hcard_sdiff : ((Finset.Icc (1 : Nat) mid) \ S).card = (Finset.Icc (1 : Nat) mid).card - S.card := by
      have h' : ((Finset.Icc (1 : Nat) mid) \ S).card = (Finset.Icc (1 : Nat) mid).card - (S ∩ Finset.Icc (1 : Nat) mid).card := by
        -- `card_sdiff` is stated as `card (t \ s) = card t - card (s ∩ t)`
        simpa using (Finset.card_sdiff (s := S) (t := Finset.Icc (1 : Nat) mid))
      have hinter : (S ∩ Finset.Icc (1 : Nat) mid).card = S.card := by
        simpa [Finset.inter_eq_left.2 hS_sub]
      simpa [h', hinter]
    simpa [hIcc_card, hcard_sdiff] using this

  simpa [mid, hMissing_eq] using (le_trans hk hmid_le_missing)

theorem goal_4
    (arr : Array ℕ)
    (k : ℕ)
    (require_1 : OfNat.ofNat 0 < k ∧ (∀ (i : ℕ), i + OfNat.ofNat 1 < arr.size → arr[i]! < arr[i + OfNat.ofNat 1]!) ∧ ∀ i < arr.size, OfNat.ofNat 0 < arr[i]!)
    : OfNat.ofNat 0 < k := by
    intros; expose_names; try simp_all; try grind

theorem goal_5
    (arr : Array ℕ)
    (k : ℕ)
    : k ≤ {m ∈ Finset.Icc (OfNat.ofNat 1) (arr.size + k) | ∀ (i : ℕ) (x : i < arr.size), ¬arr[i] = m}.card := by
  classical
  set n : ℕ := arr.size with hn

  let U : Finset ℕ := Finset.Icc 1 (n + k)
  let P : ℕ → Prop := fun m => ∀ (i : ℕ) (x : i < n), ¬ arr[i] = m

  have hcardU : U.card = n + k := by
    -- `Nat.card_Icc : #(Icc a b) = b + 1 - a`.
    have h : U.card = (n + k) + 1 - 1 := by
      simpa [U] using (Nat.card_Icc (a := (1 : ℕ)) (b := n + k))
    simpa [Nat.add_assoc] using h

  let present : Finset ℕ := U.filter (fun m => ¬ P m)

  let V : Finset ℕ := (Finset.univ : Finset (Fin n)).image (fun j : Fin n => arr[j.1])

  have hsubset : present ⊆ V := by
    intro m hm
    rcases Finset.mem_filter.mp hm with ⟨_, hmnot⟩
    have hex : ∃ i, ∃ x : i < n, arr[i] = m := by
      have hmnot' : ¬ (∀ (i : ℕ) (x : i < n), ¬ arr[i] = m) := by
        simpa [P] using hmnot
      push_neg at hmnot'
      simpa using hmnot'
    rcases hex with ⟨i, hi, hEq⟩
    refine Finset.mem_image.mpr ?_
    refine ⟨⟨i, hi⟩, by simp, ?_⟩
    simpa using hEq

  have hVcard : V.card ≤ n := by
    calc
      V.card ≤ (Finset.univ : Finset (Fin n)).card := by
        simpa [V] using
          (Finset.card_image_le (s := (Finset.univ : Finset (Fin n)))
            (f := fun j : Fin n => arr[j.1]))
      _ = n := by simp [Finset.card_fin]

  have hpresent : present.card ≤ n := by
    exact le_trans (Finset.card_le_card hsubset) hVcard

  have hpart : (U.filter P).card + present.card = U.card := by
    simpa [present] using
      (Finset.filter_card_add_filter_neg_card_eq_card (s := U) (p := P))

  have hsub_eq : U.card - present.card = (U.filter P).card := by
    calc
      U.card - present.card = ((U.filter P).card + present.card) - present.card := by
        simpa [hpart.symm]
      _ = (U.filter P).card := Nat.add_sub_cancel _ _

  have hsub : U.card - n ≤ (U.filter P).card := by
    have hsub' : U.card - n ≤ U.card - present.card :=
      Nat.sub_le_sub_left hpresent U.card
    simpa [hsub_eq] using hsub'

  have hUk : U.card - n = k := by
    calc
      U.card - n = (n + k) - n := by simpa [hcardU]
      _ = (k + n) - n := by simpa [Nat.add_comm]
      _ = k := Nat.add_sub_cancel k n

  have hk : k ≤ U.card - n := by
    simpa [hUk]

  have : k ≤ (U.filter P).card := le_trans hk hsub

  simpa [U, P, hn] using this

theorem goal_6
    (arr : Array ℕ)
    (k : ℕ)
    (i : ℕ)
    (r_1 : ℕ)
    (a : OfNat.ofNat 1 ≤ i)
    (a_1 : i ≤ r_1)
    (a_5 : OfNat.ofNat 0 < k)
    (invariant_inv_outer_bracket_lo : {m ∈ Finset.Icc (OfNat.ofNat 1) (i - OfNat.ofNat 1) | ∀ (i : ℕ) (x : i < arr.size), ¬arr[i] = m}.card < k)
    (invariant_inv_outer_bracket_r : k ≤ {m ∈ Finset.Icc (OfNat.ofNat 1) r_1 | ∀ (i : ℕ) (x : i < arr.size), ¬arr[i] = m}.card)
    (done_1 : r_1 ≤ i)
    : postcondition arr k i := by
  classical
  have hir : i = r_1 := le_antisymm a_1 done_1
  have hi_pos : 0 < i := lt_of_lt_of_le Nat.zero_lt_one a

  have inArrayB_eq_false_iff_forall (m : Nat) :
      inArrayB arr m = false ↔ ∀ (j : Nat) (hj : j < arr.size), ¬ arr[j] = m := by
    unfold inArrayB
    simpa [Nat.beq_eq_true_eq] using
      (@Array.any_eq_false Nat (fun y => y == m) arr)

  have missingUpTo_eq_card (n : Nat) :
      missingUpTo arr n =
        {m ∈ Finset.Icc (1 : Nat) n | ∀ (j : Nat) (hj : j < arr.size), ¬arr[j] = m}.card := by
    unfold missingUpTo
    have hpred :
        (Finset.Icc (1 : Nat) n).filter (fun m => !(inArrayB arr m)) =
          (Finset.Icc (1 : Nat) n).filter (fun m => inArrayB arr m = false) := by
      apply Finset.filter_congr
      intro m hm
      cases hb : inArrayB arr m <;> simp (config := {contextual := false}) [hb]
    have hpred2 :
        (Finset.Icc (1 : Nat) n).filter (fun m => inArrayB arr m = false) =
          {m ∈ Finset.Icc (1 : Nat) n | ∀ (j : Nat) (hj : j < arr.size), ¬arr[j] = m} := by
      ext m
      simp [inArrayB_eq_false_iff_forall]
    simpa [hpred, hpred2]

  have hLo : missingUpTo arr (Nat.pred i) < k := by
    have hm : missingUpTo arr (i - 1) =
        {m ∈ Finset.Icc (1 : Nat) (i - 1) | ∀ (j : Nat) (hj : j < arr.size), ¬arr[j] = m}.card :=
      missingUpTo_eq_card (i - 1)
    have : missingUpTo arr (i - 1) < k := by
      rw [hm]
      simpa using invariant_inv_outer_bracket_lo
    simpa (config := {contextual := false}) [Nat.pred_eq_sub_one] using this

  have hR : k ≤ missingUpTo arr i := by
    have hm : missingUpTo arr r_1 =
        {m ∈ Finset.Icc (1 : Nat) r_1 | ∀ (j : Nat) (hj : j < arr.size), ¬arr[j] = m}.card :=
      missingUpTo_eq_card r_1
    have : k ≤ missingUpTo arr r_1 := by
      rw [hm]
      simpa using invariant_inv_outer_bracket_r
    simpa (config := {contextual := false}) [hir] using this

  let Q : Nat → Prop := fun m => ∀ (j : Nat) (hj : j < arr.size), ¬arr[j] = m

  have missingUpTo_stepQ (t : Nat) (ht : 1 ≤ t) :
      missingUpTo arr t = missingUpTo arr (Nat.pred t) + (if Q t then 1 else 0) := by
    cases t with
    | zero =>
        cases (Nat.not_succ_le_zero 0 (by simpa using ht))
    | succ n =>
        have hSucc : missingUpTo arr (Nat.succ n) = {m ∈ Finset.Icc (1 : Nat) (Nat.succ n) | Q m}.card := by
          simpa [missingUpTo_eq_card, Q]
        have hPred : missingUpTo arr n = {m ∈ Finset.Icc (1 : Nat) n | Q m}.card := by
          simpa [missingUpTo_eq_card, Q]
        have hIcc : Finset.Icc (1 : Nat) (Nat.succ n) = insert (Nat.succ n) (Finset.Icc (1 : Nat) n) := by
          simpa [Nat.pred_succ] using
            (Finset.insert_Icc_pred_right_eq_Icc (a := (1 : Nat)) (b := Nat.succ n)
              (by exact Nat.succ_le_succ (Nat.zero_le n))).symm
        have hnotmem : Nat.succ n ∉ {m ∈ Finset.Icc (1 : Nat) n | Q m} := by
          intro hm
          have hmIcc : Nat.succ n ∈ Finset.Icc (1 : Nat) n := (Finset.mem_filter.mp hm).1
          have hle : Nat.succ n ≤ n := (Finset.mem_Icc.mp hmIcc).2
          exact (Nat.not_succ_le_self n) hle

        by_cases hq : Q (Nat.succ n)
        · have hfilter : {m ∈ Finset.Icc (1 : Nat) (Nat.succ n) | Q m} =
              insert (Nat.succ n) {m ∈ Finset.Icc (1 : Nat) n | Q m} := by
            ext m
            by_cases hm : m = Nat.succ n
            · subst hm; simp [hIcc, hq]
            · simp [hIcc, hm, hq]
          have hcard :
              ({m ∈ Finset.Icc (1 : Nat) (Nat.succ n) | Q m}.card) =
                ({m ∈ Finset.Icc (1 : Nat) n | Q m}.card) + 1 := by
            simpa [hfilter] using
              (Finset.card_insert_of_not_mem (s := {m ∈ Finset.Icc (1 : Nat) n | Q m}) (a := Nat.succ n) hnotmem)
          calc
            missingUpTo arr (Nat.succ n)
                = {m ∈ Finset.Icc (1 : Nat) (Nat.succ n) | Q m}.card := hSucc
            _ = {m ∈ Finset.Icc (1 : Nat) n | Q m}.card + 1 := hcard
            _ = missingUpTo arr n + 1 := by simpa [Q, hPred]
            _ = missingUpTo arr (Nat.pred (Nat.succ n)) + 1 := by simp
            _ = missingUpTo arr (Nat.pred (Nat.succ n)) + (if Q (Nat.succ n) then 1 else 0) := by simp [hq]
        · have hfilter : {m ∈ Finset.Icc (1 : Nat) (Nat.succ n) | Q m} =
              {m ∈ Finset.Icc (1 : Nat) n | Q m} := by
            ext m
            by_cases hm : m = Nat.succ n
            · subst hm; simp [hIcc, hq]
            · simp [hIcc, hm, hq]
          calc
            missingUpTo arr (Nat.succ n)
                = {m ∈ Finset.Icc (1 : Nat) (Nat.succ n) | Q m}.card := hSucc
            _ = {m ∈ Finset.Icc (1 : Nat) n | Q m}.card := by simpa [hfilter]
            _ = missingUpTo arr n := by simpa [Q, hPred]
            _ = missingUpTo arr (Nat.pred (Nat.succ n)) := by simp
            _ = missingUpTo arr (Nat.pred (Nat.succ n)) + (if Q (Nat.succ n) then 1 else 0) := by simp [hq]

  have hQi : Q i := by
    by_contra hq
    have hstep := missingUpTo_stepQ i a
    have hEq : missingUpTo arr i = missingUpTo arr (Nat.pred i) := by
      simpa (config := {contextual := false}) [Q, hq, Nat.add_zero] using hstep
    have : missingUpTo arr i < k := by
      -- rewrite goal using hEq
      rw [hEq]
      exact hLo
    exact (Nat.not_lt_of_ge hR) this

  have hIn : inArrayB arr i = false := (inArrayB_eq_false_iff_forall i).2 (by simpa [Q] using hQi)

  have hstep1 : missingUpTo arr i = missingUpTo arr (Nat.pred i) + 1 := by
    have hstep := missingUpTo_stepQ i a
    simpa [Q, hQi] using hstep

  have hMi_le : missingUpTo arr i ≤ k := by
    have hPred_le : missingUpTo arr (Nat.pred i) ≤ k - 1 := Nat.le_pred_of_lt hLo
    calc
      missingUpTo arr i = missingUpTo arr (Nat.pred i) + 1 := hstep1
      _ ≤ (k - 1) + 1 := by gcongr
      _ = k := by
        exact Nat.sub_add_cancel (Nat.succ_le_iff.mp a_5)

  have hMi : missingUpTo arr i = k := le_antisymm hMi_le hR

  have hMp : missingUpTo arr (Nat.pred i) = k - 1 := by
    have hk : (k - 1) + 1 = k := Nat.sub_one_add_one (Nat.ne_of_gt a_5)
    apply Nat.add_right_cancel
    calc
      missingUpTo arr (Nat.pred i) + 1 = missingUpTo arr i := by
        simpa [Nat.add_comm] using hstep1.symm
      _ = k := hMi
      _ = (k - 1) + 1 := by simpa [hk]

  exact ⟨hi_pos, hIn, hMp, hMi⟩


prove_correct KthMissingPositiveNumber by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at *); try (conv => congr <;> simp) ; try expose_names)
  exact (goal_0 arr lo r a_3 l2 r2 a_6 a_7 if_pos_1 if_pos_2)
  exact (goal_1 arr lo r a a_3 l2 r2 if_neg)
  exact (goal_2 arr k lo r a_3 a_4 i r2_1 if_pos_1 invariant_inv_inner_left a_7 a_6 done_2)
  exact (goal_3 arr k lo r a a_4 i r2_1 invariant_inv_inner_left a_7 invariant_inv_inner_right a_6 if_neg done_2)
  exact (goal_4 arr k require_1)
  exact (goal_5 arr k)
  exact (goal_6 arr k i r_1 a a_1 a_5 invariant_inv_outer_bracket_lo invariant_inv_outer_bracket_r done_1)
end Proof
