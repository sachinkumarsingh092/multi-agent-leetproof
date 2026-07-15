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
    XorQueriesOfASubarray: answer each query with the XOR of the subarray arr[left..right].
    **Important: complexity should be O(n + q) time and O(n) space**
    Natural language breakdown:
    1. We are given an array `arr` of natural numbers.
    2. We are given an array `queries`, where each query is a pair (left, right) of indices.
    3. Each query denotes the contiguous subarray consisting of elements at indices left, left+1, ..., right.
    4. The XOR value of a query is the bitwise XOR of all elements in that subarray.
    5. We return an array `answer` with the same length as `queries`.
    6. For each query index i, answer[i] equals the XOR of arr[left_i..right_i].
    7. Each query must be in bounds: left ≤ right and right < arr.size.
-/

section Specs
-- Helper: the subarray of `arr` from indices `l` to `r` inclusive.
-- Implemented via `extract l (r+1)`, which returns the elements with indices in [l, r+1).
def subarray (arr : Array Nat) (l : Nat) (r : Nat) : Array Nat :=
  arr.extract l (r + 1)

-- Helper: XOR of all elements in an array.
def xorAll (a : Array Nat) : Nat :=
  a.foldl (fun acc x => acc ^^^ x) 0

-- Helper: XOR of arr[l..r] inclusive.
def subarrayXor (arr : Array Nat) (l : Nat) (r : Nat) : Nat :=
  xorAll (subarray arr l r)

-- Preconditions: every query index pair is well-formed and in-bounds for `arr`.
def precondition (arr : Array Nat) (queries : Array (Nat × Nat)) : Prop :=
  ∀ (i : Nat), i < queries.size →
    let q := queries[i]!
    let l := q.1
    let r := q.2
    l ≤ r ∧ r < arr.size

-- Postconditions:
-- 1) output length equals number of queries
-- 2) each output element equals the XOR of the corresponding inclusive subarray

def postcondition (arr : Array Nat) (queries : Array (Nat × Nat)) (answer : Array Nat) : Prop :=
  answer.size = queries.size ∧
  ∀ (i : Nat), i < queries.size →
    let q := queries[i]!
    let l := q.1
    let r := q.2
    answer[i]! = subarrayXor arr l r
end Specs

section Impl
method XorQueriesOfASubarray (arr : Array Nat) (queries : Array (Nat × Nat))
  return (answer : Array Nat)
  require precondition arr queries
  ensures postcondition arr queries answer
  do
  -- Prefix XOR array: pref[i] = XOR of arr[0..i-1], with pref[0] = 0
  let mut pref : Array Nat := Array.replicate (arr.size + 1) 0
  let mut i : Nat := 0
  while i < arr.size
    -- pref is always the right length
    invariant "pref_size" pref.size = arr.size + 1
    -- loop index stays in-bounds
    invariant "pref_i_bounds" i ≤ arr.size
    -- correctness of computed prefix XORs up to i
    invariant "pref_correct_prefix" (∀ k : Nat, k ≤ i → pref[k]! = xorAll (arr.extract 0 k))
    decreasing arr.size - i
  do
    let prev := pref[i]!
    let next := prev ^^^ arr[i]!
    pref := pref.set! (i + 1) next
    i := i + 1

  let mut ans : Array Nat := Array.replicate queries.size 0
  let mut j : Nat := 0
  while j < queries.size
    -- ans is always the right length
    invariant "ans_size" ans.size = queries.size
    -- loop index stays in-bounds
    invariant "ans_j_bounds" j ≤ queries.size
    -- answers computed so far satisfy the spec
    invariant "ans_correct_prefix" (
      ∀ k : Nat, k < j →
        let q := queries[k]!
        let l := q.1
        let r := q.2
        ans[k]! = subarrayXor arr l r)
    decreasing queries.size - j
  do
    let q := queries[j]!
    let l := q.1
    let r := q.2
    -- XOR(arr[l..r]) = pref[r+1] XOR pref[l]
    let xr := pref[r + 1]!
    let xl := pref[l]!
    ans := ans.set! j (xr ^^^ xl)
    j := j + 1

  return ans
end Impl

section TestCases
-- Test case 1: Example 1
-- arr = [1,3,4,8], queries = [(0,1),(1,2),(0,3),(3,3)] => [2,7,14,8]
def test1_arr : Array Nat := #[1, 3, 4, 8]
def test1_queries : Array (Nat × Nat) := #[(0, 1), (1, 2), (0, 3), (3, 3)]
def test1_Expected : Array Nat := #[2, 7, 14, 8]

-- Test case 2: Example 2
-- arr = [4,8,2,10], queries = [(2,3),(1,3),(0,0),(0,3)] => [8,0,4,4]
def test2_arr : Array Nat := #[4, 8, 2, 10]
def test2_queries : Array (Nat × Nat) := #[(2, 3), (1, 3), (0, 0), (0, 3)]
def test2_Expected : Array Nat := #[8, 0, 4, 4]

-- Test case 3: Empty arr and no queries (degenerate valid case)
def test3_arr : Array Nat := #[]
def test3_queries : Array (Nat × Nat) := #[]
def test3_Expected : Array Nat := #[]

-- Test case 4: Singleton array with repeated identical queries
-- XOR of a single element range is the element itself

def test4_arr : Array Nat := #[13]
def test4_queries : Array (Nat × Nat) := #[(0, 0), (0, 0), (0, 0)]
def test4_Expected : Array Nat := #[13, 13, 13]

-- Test case 5: Two elements, cover each element and the full range

def test5_arr : Array Nat := #[5, 5]
def test5_queries : Array (Nat × Nat) := #[(0, 0), (1, 1), (0, 1)]
def test5_Expected : Array Nat := #[5, 5, 0]

-- Test case 6: Array with zeros and multiple ranges

def test6_arr : Array Nat := #[0, 1, 0, 1]
def test6_queries : Array (Nat × Nat) := #[(0, 3), (0, 0), (1, 2), (2, 3)]
def test6_Expected : Array Nat := #[0, 0, 1, 1]

-- Test case 7: Larger range queries stressing boundaries

def test7_arr : Array Nat := #[1, 2, 3, 4, 5]
def test7_queries : Array (Nat × Nat) := #[(0, 4), (0, 1), (3, 4), (2, 2)]
def test7_Expected : Array Nat := #[1, 3, 1, 3]

-- Test case 8: Many queries, including last index only and full range

def test8_arr : Array Nat := #[7, 6, 5, 4, 3, 2, 1]
def test8_queries : Array (Nat × Nat) := #[(6, 6), (0, 6), (1, 5), (2, 4)]
def test8_Expected : Array Nat := #[1, 0, 6, 2]
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((XorQueriesOfASubarray test1_arr test1_queries).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((XorQueriesOfASubarray test2_arr test2_queries).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((XorQueriesOfASubarray test3_arr test3_queries).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((XorQueriesOfASubarray test4_arr test4_queries).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((XorQueriesOfASubarray test5_arr test5_queries).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((XorQueriesOfASubarray test6_arr test6_queries).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((XorQueriesOfASubarray test7_arr test7_queries).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((XorQueriesOfASubarray test8_arr test8_queries).run), DivM.res test8_Expected ]
end Assertions

section Pbt
velvet_plausible_test XorQueriesOfASubarray (config := { maxMs := some 20000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000

theorem goal_0_0
    (arr : Array ℕ)
    (i : ℕ)
    (invariant_pref_i_bounds : i ≤ arr.size)
    (if_pos : i < arr.size)
    (hk_arr : i + 1 ≤ arr.size)
    : Array.foldl (fun acc x => acc ^^^ x) 0 (arr.extract 0 (i + 1)) 0 (i + 1) =
  Array.foldl (fun acc x => acc ^^^ x) 0 (arr.extract 0 i) 0 i ^^^ arr[i]! := by

  let f : Nat → Nat → Nat := fun acc x => acc ^^^ x

  have hsize_i : (arr.extract 0 i).size = i := by
    simpa using (Array.size_extract_of_le (i := 0) (j := i) invariant_pref_i_bounds)

  have hget : arr[i] = arr[i]! := by
    simp [Array.get!, if_pos]

  have hextract : arr.extract 0 (i + 1) = (arr.extract 0 i).push arr[i] := by
    simpa using (@Array.extract_succ_right Nat arr 0 i (Nat.succ_pos i) if_pos)

  have w : i + 1 = (arr.extract 0 i).size + (#[arr[i]] : Array Nat).size := by
    simpa [hsize_i]

  -- rewrite `extract 0 (i+1)` to a push
  have hrew :
      Array.foldl f 0 (arr.extract 0 (i + 1)) 0 (i + 1) =
        Array.foldl f 0 ((arr.extract 0 i).push arr[i]) 0 (i + 1) := by
    simpa [f] using congrArg (fun a => Array.foldl f 0 a 0 (i + 1)) hextract

  -- rewrite that push as an append of a singleton
  have hrew' :
      Array.foldl f 0 ((arr.extract 0 i).push arr[i]) 0 (i + 1) =
        Array.foldl f 0 ((arr.extract 0 i) ++ #[arr[i]]) 0 (i + 1) := by
    simpa using
      congrArg (fun a => Array.foldl f 0 a 0 (i + 1))
        (@Array.push_eq_append_singleton Nat (arr.extract 0 i) arr[i])

  have happend :
      Array.foldl f 0 ((arr.extract 0 i) ++ #[arr[i]]) 0 (i + 1) =
        (#[arr[i]]).foldl f ((arr.extract 0 i).foldl f 0) := by
    -- fold over append
    exact
      (Array.foldl_append' (f := f) (b := (0 : Nat))
        (xs := arr.extract 0 i) (ys := #[arr[i]]) (stop := i + 1) w)

  calc
    Array.foldl f 0 (arr.extract 0 (i + 1)) 0 (i + 1)
        = Array.foldl f 0 ((arr.extract 0 i).push arr[i]) 0 (i + 1) := hrew
    _ = Array.foldl f 0 ((arr.extract 0 i) ++ #[arr[i]]) 0 (i + 1) := hrew'
    _ = (#[arr[i]]).foldl f ((arr.extract 0 i).foldl f 0) := happend
    _ = ((arr.extract 0 i).foldl f 0) ^^^ arr[i] := by
          simp [f]
    _ = Array.foldl f 0 (arr.extract 0 i) 0 i ^^^ arr[i]! := by
          simpa [f, hsize_i, hget]

theorem goal_0
    (arr : Array ℕ)
    (queries : Array (ℕ × ℕ))
    (require_1 : ∀ i < queries.size, queries[i]!.1 ≤ queries[i]!.2 ∧ queries[i]!.2 < arr.size)
    (i : ℕ)
    (pref : Array ℕ)
    (invariant_pref_size : pref.size = arr.size + OfNat.ofNat 1)
    (invariant_pref_i_bounds : i ≤ arr.size)
    (if_pos : i < arr.size)
    (invariant_pref_correct_prefix : ∀ k ≤ i, pref[k]! = Array.foldl (fun (acc x : ℕ) => acc ^^^ x) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) k) (OfNat.ofNat 0) (min k arr.size))
    : ∀ k ≤ i + OfNat.ofNat 1,
        (pref.setIfInBounds (i + OfNat.ofNat 1) (pref[i]! ^^^ arr[i]!))[k]! =
          Array.foldl (fun (acc x : ℕ) => acc ^^^ x) (OfNat.ofNat 0)
            (arr.extract (OfNat.ofNat 0) k) (OfNat.ofNat 0) (min k arr.size) := by
  intro k hk0
  have hk : k ≤ i + 1 := by simpa using hk0
  have hi1 : i + 1 ≤ arr.size := Nat.succ_le_of_lt if_pos
  have hk_arr : k ≤ arr.size := le_trans hk hi1
  have hmin : min k arr.size = k := Nat.min_eq_left hk_arr

  by_cases hki : k ≤ i
  · have hget_ne :
        (pref.setIfInBounds (i + 1) (pref[i]! ^^^ arr[i]!))[k]! = pref[k]! := by
        expose_names; intros; expose_names; try simp_all; try grind
    have hk_inv := invariant_pref_correct_prefix k hki
    simpa [hget_ne, hmin] using hk_inv

  · have hik : i < k := Nat.lt_of_not_ge hki
    have hk_ge : i + 1 ≤ k := Nat.succ_le_of_lt hik
    have hkEq : k = i + 1 := Nat.le_antisymm hk hk_ge
    subst hkEq

    have hget_self :
        (pref.setIfInBounds (i + 1) (pref[i]! ^^^ arr[i]!))[i + 1]! = (pref[i]! ^^^ arr[i]!) := by
        expose_names; intros; expose_names; try simp_all; try grind

    have hmini : min i arr.size = i := Nat.min_eq_left (Nat.le_of_lt if_pos)
    have hprefi : pref[i]! = Array.foldl (fun acc x : ℕ => acc ^^^ x) 0 (arr.extract 0 i) 0 i := by
      simpa [hmini] using (invariant_pref_correct_prefix i (le_rfl))

    have hmin1 : min (i + 1) arr.size = i + 1 := Nat.min_eq_left hi1

    have hfold_succ :
        Array.foldl (fun acc x : ℕ => acc ^^^ x) 0 (arr.extract 0 (i + 1)) 0 (i + 1) =
          (Array.foldl (fun acc x : ℕ => acc ^^^ x) 0 (arr.extract 0 i) 0 i) ^^^ arr[i]! := by
        expose_names; exact (goal_0_0 arr i invariant_pref_i_bounds if_pos hk_arr)

    calc
      (pref.setIfInBounds (i + 1) (pref[i]! ^^^ arr[i]!))[i + 1]! = pref[i]! ^^^ arr[i]! := hget_self
      _ = (Array.foldl (fun acc x : ℕ => acc ^^^ x) 0 (arr.extract 0 i) 0 i) ^^^ arr[i]! := by
        simpa [hprefi]
      _ = Array.foldl (fun acc x : ℕ => acc ^^^ x) 0 (arr.extract 0 (i + 1)) 0 (min (i + 1) arr.size) := by
        simpa [hmin1] using (Eq.symm hfold_succ)

theorem goal_1
    (arr : Array ℕ)
    (queries : Array (ℕ × ℕ))
    (require_1 : ∀ i < queries.size, queries[i]!.1 ≤ queries[i]!.2 ∧ queries[i]!.2 < arr.size)
    (i_1 : ℕ)
    (pref_1 : Array ℕ)
    (ans : Array ℕ)
    (j : ℕ)
    (invariant_ans_size : ans.size = queries.size)
    (if_pos : j < queries.size)
    (invariant_pref_i_bounds : i_1 ≤ arr.size)
    (invariant_ans_correct_prefix : ∀ k < j, ans[k]! = Array.foldl (fun (acc x : ℕ) => acc ^^^ x) (OfNat.ofNat 0) (arr.extract queries[k]!.1 (queries[k]!.2 + OfNat.ofNat 1)) (OfNat.ofNat 0) (min (queries[k]!.2 + OfNat.ofNat 1) arr.size - queries[k]!.1))
    (done_1 : arr.size ≤ i_1)
    (invariant_pref_correct_prefix : ∀ k ≤ i_1, pref_1[k]! = Array.foldl (fun (acc x : ℕ) => acc ^^^ x) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) k) (OfNat.ofNat 0) (min k arr.size))
    : ∀ k < j + OfNat.ofNat 1, (ans.setIfInBounds j (pref_1[queries[j]!.2 + OfNat.ofNat 1]! ^^^ pref_1[queries[j]!.1]!))[k]! = Array.foldl (fun (acc x : ℕ) => acc ^^^ x) (OfNat.ofNat 0) (arr.extract queries[k]!.1 (queries[k]!.2 + OfNat.ofNat 1)) (OfNat.ofNat 0) (min (queries[k]!.2 + OfNat.ofNat 1) arr.size - queries[k]!.1) := by
  intro k hk
  let f : ℕ → ℕ → ℕ := fun acc x => acc ^^^ x
  set val : ℕ := (pref_1[queries[j]!.2 + 1]! ^^^ pref_1[queries[j]!.1]!)

  have hj_ans : j < ans.size := by
    simpa [invariant_ans_size] using if_pos

  have hk_le : k ≤ j := by
    have : k < j + 1 := by simpa using hk
    exact Nat.lt_succ_iff.mp this

  cases lt_or_eq_of_le hk_le with
  | inl hk_lt =>
      have hne : j ≠ k := by exact Ne.symm (Nat.ne_of_lt hk_lt)
      have hopt : (ans.setIfInBounds j val)[k]? = ans[k]? := by
        simpa [val] using
          (Array.getElem?_setIfInBounds_ne (xs := ans) (i := j) (j := k) hne (a := val))
      have hget : (ans.setIfInBounds j val)[k]! = ans[k]! := by
        simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, hopt]
      simpa [hget] using invariant_ans_correct_prefix k hk_lt

  | inr hk_eq =>
      subst k
      have hqj : queries[j]!.1 ≤ queries[j]!.2 ∧ queries[j]!.2 < arr.size := require_1 j if_pos
      set l : ℕ := queries[j]!.1
      set r : ℕ := queries[j]!.2

      have hl_le_arr : l ≤ arr.size := le_trans hqj.1 (le_of_lt hqj.2)
      have hr1_le_arr : r + 1 ≤ arr.size := Nat.succ_le_of_lt hqj.2
      have hl_le_r1 : l ≤ r + 1 := le_trans hqj.1 (Nat.le_succ r)

      have hi1 : i_1 = arr.size := Nat.le_antisymm invariant_pref_i_bounds done_1

      have pref_r1 : pref_1[r + 1]! = Array.foldl f 0 (arr.extract 0 (r + 1)) 0 (r + 1) := by
        have hr1_le_i1 : r + 1 ≤ i_1 := by simpa [hi1] using hr1_le_arr
        simpa [f, Nat.min_eq_left hr1_le_arr] using (invariant_pref_correct_prefix (r + 1) hr1_le_i1)

      have pref_l : pref_1[l]! = Array.foldl f 0 (arr.extract 0 l) 0 l := by
        have hl_le_i1 : l ≤ i_1 := by simpa [hi1] using hl_le_arr
        simpa [f, Nat.min_eq_left hl_le_arr] using (invariant_pref_correct_prefix l hl_le_i1)

      have hopj : (ans.setIfInBounds j val)[j]? = some val := by
        simp [Array.getElem?_setIfInBounds, hj_ans, val]

      have hgetj : (ans.setIfInBounds j val)[j]! = val := by
        simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, hopj]

      have foldl_xor_init (a : ℕ) (xs : List ℕ) : xs.foldl f a = a ^^^ xs.foldl f 0 := by
        induction xs generalizing a with
        | nil =>
            simp [f]
        | cons x tl ih =>
            have hx : List.foldl f x tl = x ^^^ List.foldl f 0 tl := by
              simpa using (ih (a := x))
            calc
              List.foldl f a (x :: tl) = List.foldl f (a ^^^ x) tl := by simp [List.foldl, f]
              _ = (a ^^^ x) ^^^ List.foldl f 0 tl := by simpa using ih (a := a ^^^ x)
              _ = a ^^^ (x ^^^ List.foldl f 0 tl) := by simp [Nat.xor_assoc]
              _ = a ^^^ List.foldl f x tl := by simpa [hx, Nat.xor_assoc]
              _ = a ^^^ List.foldl f 0 (x :: tl) := by
                    simp [List.foldl, f, Nat.zero_xor, Nat.xor_assoc]

      set xs : Array ℕ := arr.extract 0 l
      set ys : Array ℕ := arr.extract l (r + 1)

      have hxs_size : xs.size = l := by
        simp [xs, Array.size_extract, Nat.min_eq_left hl_le_arr]
      have hys_size : ys.size = (r + 1) - l := by
        simp [ys, Array.size_extract, Nat.min_eq_left hr1_le_arr]

      have hconcat : xs ++ ys = arr.extract 0 (r + 1) := by
        have h := (@Array.extract_append_extract (α := ℕ) arr 0 l (r + 1))
        simpa [xs, ys, Nat.min_eq_left (Nat.zero_le l), Nat.max_eq_right hl_le_r1] using h

      have wsize : r + 1 = xs.size + ys.size := by
        simp [hxs_size, hys_size, Nat.add_sub_of_le hl_le_r1]

      have hfold_prefix : Array.foldl f 0 (arr.extract 0 (r + 1)) 0 (r + 1) = ys.foldl f (xs.foldl f 0) := by
        have h := (Array.foldl_append' (f := f) (b := (0 : ℕ)) (xs := xs) (ys := ys) (stop := r + 1) wsize)
        simpa [hconcat] using h

      have hy_init : ys.foldl f (xs.foldl f 0) = (xs.foldl f 0) ^^^ ys.foldl f 0 := by
        have h := foldl_xor_init (a := xs.foldl f 0) (xs := ys.toList)
        simpa [Array.foldl_toList] using h

      have hpref_l : pref_1[l]! = xs.foldl f 0 := by
        simpa [xs, hxs_size, pref_l]

      have hpref_r1 : pref_1[r + 1]! = ys.foldl f (xs.foldl f 0) := by
        simpa [hfold_prefix] using pref_r1

      have hmin_r1 : min (r + 1) arr.size = r + 1 := Nat.min_eq_left hr1_le_arr

      have hys_fold : Array.foldl f 0 ys = Array.foldl f 0 ys 0 ((r + 1) - l) := by
        simpa [hys_size] using (rfl : Array.foldl f 0 ys = Array.foldl f 0 ys 0 ys.size)

      have xor_cancel_left (a b : ℕ) : a ^^^ (a ^^^ b) = b := by
        calc
          a ^^^ (a ^^^ b) = a ^^^ a ^^^ b := by
            -- from associativity, in the reverse direction
            simpa using (Eq.symm (Nat.xor_assoc a a b))
          _ = 0 ^^^ b := by simp [Nat.xor_self]
          _ = b := by simp [Nat.zero_xor]

      have xor_cancel (a b : ℕ) : (a ^^^ b) ^^^ a = b := by
        calc
          (a ^^^ b) ^^^ a = a ^^^ (a ^^^ b) := by simp [Nat.xor_assoc, Nat.xor_comm]
          _ = b := xor_cancel_left a b

      calc
        (ans.setIfInBounds j val)[j]! = val := hgetj
        _ = pref_1[r + 1]! ^^^ pref_1[l]! := by simp [val, l, r]
        _ = (ys.foldl f (xs.foldl f 0)) ^^^ (xs.foldl f 0) := by simp [hpref_r1, hpref_l]
        _ = ((xs.foldl f 0) ^^^ ys.foldl f 0) ^^^ (xs.foldl f 0) := by simp [hy_init, Nat.xor_assoc]
        _ = ys.foldl f 0 := by
              simpa [Nat.xor_comm, Nat.xor_assoc] using (xor_cancel (xs.foldl f 0) (ys.foldl f 0))
        _ = Array.foldl f 0 (arr.extract l (r + 1)) 0 ((r + 1) - l) := by
              simpa [ys, hys_fold, hys_size]
        _ = Array.foldl (fun (acc x : ℕ) => acc ^^^ x) 0
              (arr.extract (queries[j]!).1 ((queries[j]!).2 + 1)) 0
              (min ((queries[j]!).2 + 1) arr.size - (queries[j]!).1) := by
              simp [f, l, r, hmin_r1, ys]


prove_correct XorQueriesOfASubarray by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at *); try (conv => congr <;> simp) ; try expose_names)
  exact (goal_0 arr queries require_1 i pref invariant_pref_size invariant_pref_i_bounds if_pos invariant_pref_correct_prefix)
  exact (goal_1 arr queries require_1 i_1 pref_1 ans j invariant_ans_size if_pos invariant_pref_i_bounds invariant_ans_correct_prefix done_1 invariant_pref_correct_prefix)
end Proof
