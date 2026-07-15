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
def implementation (arr : Array Nat) (queries : Array (Nat × Nat)) : Array Nat :=
  -- Build prefix XORs: px[i] = arr[0] ^^^ ... ^^^ arr[i-1]
  -- px has size arr.size + 1, with px[0] = 0
  let px : Array Nat :=
    arr.foldl
      (fun acc x =>
        let last := acc.get! (acc.size - 1)
        acc.push (last ^^^ x))
      #[0]
  -- Answer queries using px[r+1] ^^^ px[l]
  queries.map (fun q =>
    let l := q.1
    let r := q.2
    (px.get! (r + 1)) ^^^ (px.get! l))
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
#assert_same_evaluation #[(implementation test1_arr test1_queries), test1_Expected]

-- Test case 2
#assert_same_evaluation #[(implementation test2_arr test2_queries), test2_Expected]

-- Test case 3
#assert_same_evaluation #[(implementation test3_arr test3_queries), test3_Expected]

-- Test case 4
#assert_same_evaluation #[(implementation test4_arr test4_queries), test4_Expected]

-- Test case 5
#assert_same_evaluation #[(implementation test5_arr test5_queries), test5_Expected]

-- Test case 6
#assert_same_evaluation #[(implementation test6_arr test6_queries), test6_Expected]

-- Test case 7
#assert_same_evaluation #[(implementation test7_arr test7_queries), test7_Expected]

-- Test case 8
#assert_same_evaluation #[(implementation test8_arr test8_queries), test8_Expected]
end Assertions

section Pbt
method implementationPbt (arr : Array Nat) (queries : Array (Nat × Nat))
  return (result : Array Nat)
  require precondition arr queries
  ensures postcondition arr queries result
  do
  return (implementation arr queries)

velvet_plausible_test implementationPbt (config := { maxMs := some 20000 })
end Pbt

section Proof
theorem correctness_goal_0_0
    (arr : Array ℕ)
    (queries : Array (ℕ × ℕ))
    (h_precond : precondition arr queries)
    (i : ℕ)
    (hi : i < queries.size)
    (hq : queries[i]!.1 ≤ queries[i]!.2 ∧ queries[i]!.2 < arr.size)
    (hl : queries[i]!.1 ≤ queries[i]!.2)
    (hr : queries[i]!.2 < arr.size)
    (k : ℕ)
    (hk : k ≤ arr.size)
    : (List.foldl
        (fun acc x =>
          let last := acc.get! (acc.size - 1);
          acc.push (last ^^^ x))
        #[0] arr.toList).get!
    k =
  xorAll (List.take k arr.toList).toArray := by
  classical
  clear h_precond i hi hq hl hr queries

  let step : Array Nat → Nat → Array Nat := fun acc x =>
    let last := acc.get! (acc.size - 1)
    acc.push (last ^^^ x)

  -- take (t+1) decomposes as take t ++ [element t]
  have take_succ_eq_take_append_get (L : List Nat) (t : Nat) (ht : t < L.length) :
      List.take (t + 1) L = List.take t L ++ [L.get ⟨t, ht⟩] := by
    induction L generalizing t with
    | nil =>
        cases ht
    | cons a L ih =>
        cases t with
        | zero =>
            simp [List.take, List.get]
        | succ t =>
            have ht' : t < L.length := by
              simpa [Nat.succ_lt_succ_iff] using ht
            have ih' := ih t ht'
            have hcons : a :: List.take (t + 1) L = a :: (List.take t L ++ [L.get ⟨t, ht'⟩]) := by
              simpa using congrArg (fun xs => a :: xs) ih'
            simpa [List.take, List.get, ht'] using hcons

  -- xorAll of take (t+1) is xorAll of take t xor the next element
  have xorAll_take_succ (L : List Nat) (t : Nat) (ht : t < L.length) :
      xorAll (List.take (t + 1) L).toArray =
        xorAll (List.take t L).toArray ^^^ (L.get ⟨t, ht⟩) := by
    unfold xorAll
    simp [List.foldl_toArray]
    rw [take_succ_eq_take_append_get L t ht]
    rw [List.foldl_append]
    simp

  have get!_push_lt (xs : Array Nat) (x : Nat) (j : Nat) (hj : j < xs.size) :
      (xs.push x).get! j = xs.get! j := by
    simp [Array.get!_eq_getD_getElem?, Array.getElem?_push, hj.ne]

  have get!_push_eq (xs : Array Nat) (x : Nat) :
      (xs.push x).get! xs.size = x := by
    simp [Array.get!_eq_getD_getElem?, Array.getElem?_push_eq]

  let motive : Nat → Array Nat → Prop := fun t b =>
    b.size = t + 1 ∧ ∀ j, j ≤ t → b.get! j = xorAll (List.take j arr.toList).toArray

  have hm : motive arr.size (arr.foldl step #[0]) := by
    refine Array.foldl_induction (motive := motive) (init := #[0]) ?h0 ?hf
    · constructor
      · simp [motive]
      · intro j hj
        have : j = 0 := Nat.le_zero.mp hj
        subst this
        simp [motive, xorAll, Array.get!_eq_getD_getElem?]
    · intro i b hb
      cases i with
      | mk t htArr =>
        rcases hb with ⟨hbsize, hbprop⟩
        let x : Nat := arr[t]'htArr
        constructor
        · simp [motive, step, hbsize, x]
        · intro j hj
          have hbsize' : b.size = t + 1 := hbsize
          by_cases hjs : j = t + 1
          · subst hjs
            let htList : t < arr.toList.length := by
              simpa [Array.length_toList] using htArr
            have hpred : b.size - 1 = t := by
              simp [hbsize']
            have ht1 : t + 1 = b.size := by simpa [hbsize'] using hbsize'.symm
            have hx : arr.toList.get ⟨t, htList⟩ = x := by
              have hx' : (arr.toList[t]'htList) = x := by
                simpa [x, htList] using (Array.getElem_toList (xs := arr) (i := t) (h := htArr))
              simpa using hx'
            have hx_xor :
                xorAll (List.take t arr.toList).toArray ^^^ x =
                  xorAll (List.take t arr.toList).toArray ^^^ (arr.toList.get ⟨t, htList⟩) := by
              simpa using congrArg (fun y => xorAll (List.take t arr.toList).toArray ^^^ y) hx.symm
            calc
              (step b x).get! (t + 1)
                  = (b.push (b.get! (b.size - 1) ^^^ x)).get! (t + 1) := by
                      simp [step]
              _ = (b.push (b.get! (b.size - 1) ^^^ x)).get! b.size := by
                      simp [ht1]
              _ = b.get! (b.size - 1) ^^^ x := by
                      simpa using (get!_push_eq (xs := b) (x := b.get! (b.size - 1) ^^^ x))
              _ = b.get! t ^^^ x := by
                      simp [hpred]
              _ = xorAll (List.take t arr.toList).toArray ^^^ x := by
                      simp [hbprop t (le_rfl)]
              _ = xorAll (List.take t arr.toList).toArray ^^^ (arr.toList.get ⟨t, htList⟩) := by
                      exact hx_xor
              _ = xorAll (List.take (t + 1) arr.toList).toArray := by
                      symm
                      simpa using (xorAll_take_succ (L := arr.toList) (t := t) (ht := htList))
          · have hjt : j ≤ t := by
              exact Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hj hjs)
            have hjlt : j < b.size := by
              have : j < t + 1 := Nat.lt_succ_of_le hjt
              simpa [hbsize'] using this
            have := hbprop j hjt
            simpa [motive, step, x, get!_push_lt _ _ _ hjlt] using this

  rcases hm with ⟨_, hprop_final⟩

  have hfold : arr.toList.foldl step #[0] = arr.foldl step #[0] := by
    simpa using (Array.foldl_toList (xs := arr) (f := step) (init := #[0]))

  simpa [step, hfold] using (hprop_final k hk)

theorem correctness_goal_0
    (arr : Array ℕ)
    (queries : Array (ℕ × ℕ))
    (h_precond : precondition arr queries)
    (i : ℕ)
    (hi : i < queries.size)
    (hq : queries[i]!.1 ≤ queries[i]!.2 ∧ queries[i]!.2 < arr.size)
    (hl : queries[i]!.1 ≤ queries[i]!.2)
    (hr : queries[i]!.2 < arr.size)
    : ∀ k ≤ arr.size,
  (Array.foldl
          (fun acc x =>
            let last := acc.get! (acc.size - 1);
            acc.push (last ^^^ x))
          #[0] arr).get!
      k =
    xorAll (arr.extract 0 k) := by
  intro k hk
  -- reduce to a list lemma about foldl building prefix XORs
  have h_list :
      ((arr.toList.foldl
            (fun acc x =>
              let last := acc.get! (acc.size - 1)
              acc.push (last ^^^ x))
            #[0]).get! k)
        = (xorAll ((arr.toList.take k).toArray)) := by
    expose_names; exact (correctness_goal_0_0 arr queries h_precond i hi hq hl hr k hk)
  -- rewrite array foldl to list foldl
  have h_fold :
      (Array.foldl
            (fun acc x =>
              let last := acc.get! (acc.size - 1)
              acc.push (last ^^^ x))
            #[0] arr)
        = (arr.toList.foldl
            (fun acc x =>
              let last := acc.get! (acc.size - 1)
              acc.push (last ^^^ x))
            #[0]) := by
    -- Array.foldl_toList: xs.toList.foldl f init = xs.foldl f init
    simpa using (Array.foldl_toList (f := (fun acc x =>
              let last := acc.get! (acc.size - 1)
              acc.push (last ^^^ x))) (init := #[0]) (xs := arr)).symm
  -- rewrite extract 0 k as (take k).toArray
  have h_extract : arr.extract 0 k = (arr.toList.take k).toArray := by
    expose_names; intros; expose_names; try ( simp at * ); try grind
  -- finish
  rw [h_fold]
  -- now goal matches h_list after rewriting the RHS
  simpa [h_extract] using h_list

theorem correctness_goal_1
    (arr : Array ℕ)
    (i : ℕ)
    : ∀ (l r : ℕ),
  l ≤ r → r < arr.size → xorAll (arr.extract 0 (r + 1)) ^^^ xorAll (arr.extract 0 l) = xorAll (arr.extract l (r + 1)) := by
  intro l r hlr hrr

  -- XOR is associative
  haveI : Std.Associative (fun a b : Nat => a ^^^ b) := ⟨Nat.xor_assoc⟩

  have foldl_xor_init (xs : Array Nat) (a : Nat) :
      xs.foldl (· ^^^ ·) a = a ^^^ xs.foldl (· ^^^ ·) 0 := by
    -- xs.foldl op (a ^^^ 0) = a ^^^ xs.foldl op 0
    simpa [Nat.xor_zero] using
      (Array.foldl_assoc (xs := xs) (op := (· ^^^ ·)) (a₁ := a) (a₂ := (0 : Nat)))

  have xorAll_append (xs ys : Array Nat) :
      xorAll (xs ++ ys) = xorAll xs ^^^ xorAll ys := by
    unfold xorAll
    -- (xs ++ ys).foldl op 0 = ys.foldl op (xs.foldl op 0)
    simp [Array.foldl_append]
    -- ys.foldl op (xs.foldl op 0) = xs.foldl op 0 ^^^ ys.foldl op 0
    simpa using (foldl_xor_init (xs := ys) (a := xs.foldl (· ^^^ ·) 0))

  have hle : l ≤ r + 1 := le_trans hlr (Nat.le_succ r)

  have hsplit : arr.extract 0 (r + 1) = arr.extract 0 l ++ arr.extract l (r + 1) := by
    simpa [Nat.min_eq_left (Nat.zero_le l), Nat.max_eq_right hle] using
      (Array.extract_append_extract (i := 0) (j := l) (k := (r + 1))).symm

  have hx :
      xorAll (arr.extract 0 (r + 1)) =
        xorAll (arr.extract 0 l) ^^^ xorAll (arr.extract l (r + 1)) := by
    simpa [hsplit] using
      (xorAll_append (arr.extract 0 l) (arr.extract l (r + 1)))

  -- cancel the prefix XOR
  rw [hx]
  -- (A ^^^ B) ^^^ A = B
  rw [Nat.xor_assoc]
  rw [Nat.xor_comm (xorAll (arr.extract l (r + 1))) (xorAll (arr.extract 0 l))]
  rw [← Nat.xor_assoc]
  simp [Nat.xor_self, Nat.zero_xor]

theorem correctness_goal
    (arr : Array Nat)
    (queries : Array (Nat × Nat))
    (h_precond : precondition arr queries)
    : postcondition arr queries (implementation arr queries) := by
  classical
  unfold postcondition
  constructor
  · simp [implementation, Array.size_map]
  · intro i hi
    have hq : (queries[i]!).1 ≤ (queries[i]!).2 ∧ (queries[i]!).2 < arr.size := by
      simpa [precondition] using h_precond i hi
    have hl : (queries[i]!).1 ≤ (queries[i]!).2 := hq.1
    have hr : (queries[i]!).2 < arr.size := hq.2

    have hpx_spec : ∀ k, k ≤ arr.size →
        (arr.foldl
          (fun acc x =>
            let last := acc.get! (acc.size - 1)
            acc.push (last ^^^ x))
          #[0]).get! k = xorAll (arr.extract 0 k) := by
      expose_names; exact (correctness_goal_0 arr queries h_precond i hi hq hl hr)

    have hsub_cancel : ∀ (l r : Nat), l ≤ r → r < arr.size →
        (xorAll (arr.extract 0 (r+1)) ^^^ xorAll (arr.extract 0 l)) = xorAll (arr.extract l (r+1)) := by
      expose_names; exact (correctness_goal_1 arr i)

    have hr' : (queries[i]!).2 + 1 ≤ arr.size := Nat.succ_le_of_lt hr
    have hl' : (queries[i]!).1 ≤ arr.size := le_trans hl (Nat.le_of_lt hr)

    -- compute implementation at index i
    -- implementation uses the same prefix-xor array as in hpx_spec
    calc
      (implementation arr queries)[i]!
          =
            (arr.foldl
              (fun acc x =>
                let last := acc.get! (acc.size - 1)
                acc.push (last ^^^ x))
              #[0]).get! ((queries[i]!).2 + 1) ^^^
              (arr.foldl
                (fun acc x =>
                  let last := acc.get! (acc.size - 1)
                  acc.push (last ^^^ x))
                #[0]).get! (queries[i]!).1 := by
              simp [implementation, hi]
      _   = xorAll (arr.extract 0 ((queries[i]!).2 + 1)) ^^^ xorAll (arr.extract 0 (queries[i]!).1) := by
              simp [hpx_spec, hr', hl']
      _   = xorAll (arr.extract (queries[i]!).1 ((queries[i]!).2 + 1)) :=
              hsub_cancel (queries[i]!).1 (queries[i]!).2 hl hr
      _   = subarrayXor arr (queries[i]!).1 (queries[i]!).2 := by
              simp [subarrayXor, subarray]
end Proof
