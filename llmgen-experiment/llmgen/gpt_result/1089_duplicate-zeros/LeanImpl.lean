import Lean
import Mathlib.Tactic
import Velvet.Std

set_option maxHeartbeats 10000000

section Specs
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false

/- Problem Description
    1089. Duplicate Zeros: duplicate each occurrence of 0 in a fixed-length integer array, shifting right and truncating.
    Natural language breakdown:
    1. Input is an array of integers with a fixed length n.
    2. We define a conceptual output stream obtained by scanning the input left-to-right.
    3. Each nonzero input element contributes exactly one output element equal to itself.
    4. Each zero input element contributes exactly two consecutive output elements, both equal to 0.
    5. The actual returned array is the first n elements of this conceptual output stream (truncate to length n).
    6. Because the original problem updates in-place and returns nothing, we model the modified array as a returned array.
    7. Therefore the result must have the same size as the input.
    8. Every output index j (0 ≤ j < n) is produced by a unique input index i, determined by how many output elements are produced by prefixes of the input.
    Your algorithm should run in **O(n)** time and **O(1)** extra space.
-/

-- Helper: producedLen arr k = number of conceptual output elements produced by the first k input elements.
-- Each nonzero produces 1; each zero produces 2.
-- We use foldl over a prefix (arr.take k) to avoid recursion.
-- Note: we use Int = 0 propositionally; this is fine (not Float).
def producedLen (arr : Array Int) (k : Nat) : Nat :=
  (arr.take k).foldl (fun (acc : Nat) (x : Int) => if x = 0 then acc + 2 else acc + 1) 0

-- Precondition: none.
def precondition (arr : Array Int) : Prop :=
  True

-- Postcondition: result is the length-preserving truncation of duplicating zeros.
-- We characterize the mapping index-wise using the prefix produced lengths.
-- For each output index j, there is a unique input index i < n such that
-- producedLen arr i ≤ j < producedLen arr (i+1). The output value equals arr[i], but if arr[i]=0 then it is 0.
def postcondition (arr : Array Int) (result : Array Int) : Prop :=
  result.size = arr.size ∧
  (∀ (j : Nat), j < arr.size →
    ∃! (i : Nat),
      i < arr.size ∧
      producedLen arr i ≤ j ∧
      j < producedLen arr (i + 1) ∧
      result[j]! = (if arr[i]! = 0 then (0 : Int) else arr[i]!))
end Specs

section Impl
def implementation (arr : Array Int) : Array Int :=
  let n := arr.size
  -- count zeros once (O(n))
  let zeros :=
    arr.foldl (fun acc x => if x = (0 : Int) then acc + 1 else acc) 0
  -- Walk from right to left, writing into `res` (initially `arr`).
  -- `j` is the conceptual index in the duplicated stream.
  let rec go (i : Nat) (j : Nat) (res : Array Int) : Array Int :=
    match i with
    | 0 =>
        res
    | i' + 1 =>
        let x := arr[i']!
        -- write x at (j-1) if it falls within bounds
        let res1 :=
          match j with
          | 0 => res
          | j1 + 1 =>
              if j1 < n then
                res.set! j1 x
              else
                res
        if x = (0 : Int) then
          -- write the duplicated zero at (j-2) if within bounds
          let res2 :=
            match j with
            | 0 => res1
            | 1 => res1
            | (j2 + 2) =>
                if j2 < n then
                  res1.set! j2 (0 : Int)
                else
                  res1
          go i' (j - 2) res2
        else
          go i' (j - 1) res1
  go n (n + zeros) arr
end Impl

section TestCases
-- Test case 1: Example 1
-- Input: [1,0,2,3,0,4,5,0]
-- Output: [1,0,0,2,3,0,0,4]
def test1_arr : Array Int := #[1, 0, 2, 3, 0, 4, 5, 0]
def test1_Expected : Array Int := #[1, 0, 0, 2, 3, 0, 0, 4]

-- Test case 2: Example 2 (no zeros)
def test2_arr : Array Int := #[1, 2, 3]
def test2_Expected : Array Int := #[1, 2, 3]

-- Test case 3: empty array
def test3_arr : Array Int := #[]
def test3_Expected : Array Int := #[]

-- Test case 4: single element zero
def test4_arr : Array Int := #[0]
def test4_Expected : Array Int := #[0]

-- Test case 5: single element nonzero
def test5_arr : Array Int := #[7]
def test5_Expected : Array Int := #[7]

-- Test case 6: all zeros (truncation preserves all zeros)
def test6_arr : Array Int := #[0, 0, 0]
def test6_Expected : Array Int := #[0, 0, 0]

-- Test case 7: zeros causing truncation of later elements
-- [1,0,0,2] -> conceptual: 1,0,0,0,0,2 -> take 4 => [1,0,0,0]
def test7_arr : Array Int := #[1, 0, 0, 2]
def test7_Expected : Array Int := #[1, 0, 0, 0]

-- Test case 8: negative values with zeros
-- [0,-1,0,2] -> conceptual: 0,0,-1,0,0,2 -> take 4 => [0,0,-1,0]
def test8_arr : Array Int := #[0, -1, 0, 2]
def test8_Expected : Array Int := #[0, 0, -1, 0]

-- Test case 9: trailing zero does not create a visible extra element after truncation
-- [1,2,0] -> conceptual: 1,2,0,0 -> take 3 => [1,2,0]
def test9_arr : Array Int := #[1, 2, 0]
def test9_Expected : Array Int := #[1, 2, 0]

-- Recommend to validate: boundary sizes (0/1), multiple zeros, truncation at end
end TestCases

section Assertions
-- Test case 1
#assert_same_evaluation #[(implementation test1_arr), test1_Expected]

-- Test case 2
#assert_same_evaluation #[(implementation test2_arr), test2_Expected]

-- Test case 3
#assert_same_evaluation #[(implementation test3_arr), test3_Expected]

-- Test case 4
#assert_same_evaluation #[(implementation test4_arr), test4_Expected]

-- Test case 5
#assert_same_evaluation #[(implementation test5_arr), test5_Expected]

-- Test case 6
#assert_same_evaluation #[(implementation test6_arr), test6_Expected]

-- Test case 7
#assert_same_evaluation #[(implementation test7_arr), test7_Expected]

-- Test case 8
#assert_same_evaluation #[(implementation test8_arr), test8_Expected]

-- Test case 9
#assert_same_evaluation #[(implementation test9_arr), test9_Expected]
end Assertions

section Proof
theorem correctness_goal_0
    (arr : Array ℤ)
    : (implementation arr).size = arr.size := by
  classical
  simp [implementation]
  have hgo : ∀ (i j : Nat) (res : Array ℤ),
      (implementation.go arr arr.size i j res).size = res.size := by
    intro i
    induction i with
    | zero =>
        intro j res
        simp [implementation.go]
    | succ i ih =>
        intro j res
        by_cases hx : arr[i]! = (0 : ℤ)
        · -- x = 0
          cases j with
          | zero =>
              simp [implementation.go, hx, ih, Array.set!_eq_setIfInBounds]
          | succ j1 =>
              cases j1 with
              | zero =>
                  -- j = 1, the write index is 0
                  by_cases h0 : (0 < arr.size)
                  · simp [implementation.go, hx, ih, h0, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
                  · simp [implementation.go, hx, ih, h0, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
              | succ j2 =>
                  -- j = j2 + 2, write indices are j2 and j2+1
                  by_cases h2 : j2 < arr.size
                  · by_cases h3 : j2 + 1 < arr.size
                    · simp [implementation.go, hx, ih, h2, h3, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
                    · simp [implementation.go, hx, ih, h2, h3, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
                  · by_cases h3 : j2 + 1 < arr.size
                    · simp [implementation.go, hx, ih, h2, h3, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
                    · simp [implementation.go, hx, ih, h2, h3, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
        · -- x ≠ 0
          cases j with
          | zero =>
              simp [implementation.go, hx, ih, Array.set!_eq_setIfInBounds]
          | succ j1 =>
              by_cases h1 : j1 < arr.size
              · simp [implementation.go, hx, ih, h1, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
              · simp [implementation.go, hx, ih, h1, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
  simpa using
    (hgo arr.size (arr.size + Array.foldl (fun acc x => if x = 0 then acc + 1 else acc) 0 arr) arr)

theorem correctness_goal_1_0
    (arr : Array ℤ)
    (h_precond : precondition arr)
    (j : ℕ)
    (hj : j < arr.size)
    : ∃! i, i < arr.size ∧ producedLen arr i ≤ j ∧ j < producedLen arr (i + 1) := by
  classical
  have _ : True := h_precond

  let n : Nat := arr.size
  let l : List Int := arr.toList
  have hl_len : l.length = n := by
    simp [l, n, Array.length_toList]

  let step : Nat → Int → Nat := fun (acc : Nat) (x : Int) => if x = 0 then acc + 2 else acc + 1

  -- Rewrite `producedLen` as a fold over the list prefix.
  have hprod_list : ∀ k : Nat, producedLen arr k = (l.take k).foldl step 0 := by
    intro k
    unfold producedLen
    have ht : arr.take k = (l.take k).toArray := by
      simpa [l, Array.toArray_toList] using (List.take_toArray (l := arr.toList) (i := k))
    calc
      (arr.take k).foldl step 0
          = ((l.take k).toArray).foldl step 0 := by simpa [ht]
      _ = (((l.take k).toArray).toList).foldl step 0 := by
          symm
          simpa using (Array.foldl_toList (f := step) (init := 0) (xs := (l.take k).toArray))
      _ = (l.take k).foldl step 0 := by simp

  -- Strict increase before `n`
  have hlt_succ : ∀ i : Nat, i < n → producedLen arr i < producedLen arr (i + 1) := by
    intro i hi
    have hiL : i < l.length := by simpa [hl_len] using hi
    -- `l[i]?` is `some arr[i]` when `i < n`
    have hopt : l[i]? = some arr[i] := by
      have h1 : l[i]? = arr[i]? := by
        simpa [l] using (Array.getElem?_toList (xs := arr) (i := i))
      have h2 : arr[i]? = some arr[i] := Array.getElem?_eq_getElem (xs := arr) (i := i) hi
      simpa [h1] using h2

    have hcalc : producedLen arr (i + 1) = (l[i]?.toList).foldl step (producedLen arr i) := by
      simp [hprod_list, List.take_succ, List.foldl_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

    have hcalc' : producedLen arr (i + 1) = step (producedLen arr i) arr[i] := by
      simpa [hopt, hcalc]

    rw [hcalc']
    by_cases hz : (arr[i] : Int) = 0
    · simp [step, hz, Nat.lt_add_of_pos_right, Nat.succ_pos]
    · simp [step, hz, Nat.lt_add_of_pos_right, Nat.succ_pos]

  -- Non-strict monotonicity (after `n` the prefix stabilizes)
  have hle_succ : ∀ i : Nat, producedLen arr i ≤ producedLen arr (i + 1) := by
    intro i
    by_cases hi : i < n
    · exact Nat.le_of_lt (hlt_succ i hi)
    · have hnle : n ≤ i := Nat.le_of_not_gt hi
      have ht1 : arr.take i = arr := by
        simpa [Array.take_eq_extract] using
          (Array.extract_eq_self_of_le  (j := i) hnle)
      have ht2 : arr.take (i + 1) = arr := by
        have hnle' : n ≤ i + 1 := le_trans hnle (Nat.le_succ i)
        simpa [Array.take_eq_extract] using
          (Array.extract_eq_self_of_le  (j := i + 1) hnle')
      simp [producedLen, ht1, ht2]

  have hmono : Monotone (producedLen arr) :=
    monotone_nat_of_le_succ (f := producedLen arr) hle_succ

  -- Lower bound: before `n`, producedLen is at least the index
  have hge_id : ∀ k : Nat, k ≤ n → k ≤ producedLen arr k := by
    intro k hk
    induction k with
    | zero =>
        simp [producedLen]
    | succ k ih =>
        have hk0 : k ≤ n := Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self k)) hk
        have hklt : k < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk
        have ih' : k ≤ producedLen arr k := ih hk0
        have hstep : producedLen arr k + 1 ≤ producedLen arr (k + 1) :=
          Nat.succ_le_of_lt (hlt_succ k hklt)
        have : k + 1 ≤ producedLen arr k + 1 := Nat.add_le_add_right ih' 1
        exact le_trans this hstep

  have hj_lt_prod_n : j < producedLen arr n := by
    have hn_le : n ≤ producedLen arr n := hge_id n (by rfl)
    exact Nat.lt_of_lt_of_le (by simpa [n] using hj) hn_le

  -- Find the minimal prefix whose produced length exceeds `j`.
  let P : Nat → Prop := fun k => k ≤ n ∧ j < producedLen arr k
  have hex : ∃ k, P k := ⟨n, le_rfl, hj_lt_prod_n⟩
  let k : Nat := Nat.find hex
  have hk_spec : P k := Nat.find_spec hex
  have hk_le_n : k ≤ n := hk_spec.1
  have hj_lt_prod_k : j < producedLen arr k := hk_spec.2

  have hk_ne0 : k ≠ 0 := by
    intro hk0
    have : j < producedLen arr 0 := by
      simpa [k, hk0] using hj_lt_prod_k
    simpa [producedLen] using this

  have hk_pos : 0 < k := Nat.pos_of_ne_zero hk_ne0
  have hk1 : 1 ≤ k := (Nat.succ_le_iff).2 hk_pos

  let i : Nat := k - 1
  have hi_succ : i + 1 = k := by
    simpa [i] using (Nat.sub_add_cancel hk1)

  have hi_lt_n : i < n := by
    have : i + 1 ≤ n := by simpa [hi_succ] using hk_le_n
    exact Nat.lt_of_succ_le this

  have hi_le_j : producedLen arr i ≤ j := by
    have hi_lt_k : i < k := by
      have : i + 1 ≤ k := by simpa [hi_succ]
      exact Nat.lt_of_succ_le this
    have hnot : ¬ j < producedLen arr i := by
      intro hlt
      have hPi : P i := ⟨Nat.le_of_lt hi_lt_n, hlt⟩
      have hk_le_i : k ≤ i := by
        simpa [k] using (Nat.find_min' hex hPi)
      exact (Nat.not_lt_of_ge hk_le_i) hi_lt_k
    exact le_of_not_gt (by
      simpa [gt_iff_lt] using hnot)

  have hj_lt_succ : j < producedLen arr (i + 1) := by
    simpa [hi_succ] using hj_lt_prod_k

  refine ⟨i, ?_, ?_⟩
  · exact ⟨hi_lt_n, hi_le_j, hj_lt_succ⟩
  · intro y hy
    have hy_le_j : producedLen arr y ≤ j := hy.2.1
    have hy_jlt : j < producedLen arr (y + 1) := hy.2.2
    rcases lt_trichotomy y i with hyi | rfl | hiy
    · exfalso
      have hle : producedLen arr (y + 1) ≤ producedLen arr i := hmono (Nat.succ_le_of_lt hyi)
      have : j < producedLen arr i := lt_of_lt_of_le hy_jlt hle
      exact (Nat.not_lt_of_ge hi_le_j) this
    · rfl
    · exfalso
      have hle : producedLen arr (i + 1) ≤ producedLen arr y := hmono (Nat.succ_le_of_lt hiy)
      have : j < producedLen arr y := lt_of_lt_of_le hj_lt_succ hle
      exact (Nat.not_lt_of_ge hy_le_j) this

lemma producedLen_succ' (arr : Array Int) (k : Nat) (hk : k < arr.size) :
    producedLen arr (k + 1) = producedLen arr k + (if arr[k]'hk = 0 then 2 else 1) := by
  classical
  -- Expand producedLen
  unfold producedLen
  -- rewrite `take (k+1)` as `take k` plus the `k`th element
  have ht : arr.take (k + 1) = (arr.take k).push (arr[k]'hk) := by
    have hE : arr.extract 0 (k + 1) = (arr.extract 0 k).push (arr[k]'hk) := by
      simpa using
        (Array.extract_succ_right (i := 0) (j := k)
          (w := Nat.zero_lt_succ k) (h := hk))
    simpa [Array.take_eq_extract] using hE
  -- compute the fold over the push
  -- (the fold function is the one from producedLen)
  rw [ht, Array.foldl_push]
  -- finish by splitting on whether the last element is zero
  by_cases hzero : (arr[k]'hk : Int) = 0 <;> simp [hzero, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]



theorem correctness_goal_1_1
    (arr : Array ℤ)
    (h_precond : precondition arr)
    (j : ℕ)
    (hj : j < arr.size)
    (i : ℕ)
    (hi : i < arr.size ∧ producedLen arr i ≤ j ∧ j < producedLen arr (i + 1))
    (hui : ∀ (y : ℕ), y < arr.size ∧ producedLen arr y ≤ j ∧ j < producedLen arr (y + 1) → y = i)
    : (implementation arr)[j]! = if arr[i]! = 0 then 0 else arr[i]! := by
    sorry

theorem correctness_goal_1
    (arr : Array ℤ)
    (h_precond : precondition arr)
    (j : ℕ)
    (hj : j < arr.size)
    : ∃! i,
  i < arr.size ∧
    producedLen arr i ≤ j ∧ j < producedLen arr (i + 1) ∧ (implementation arr)[j]! = if arr[i]! = 0 then 0 else arr[i]! := by
  classical
  have hex_unique : ∃! i,
      i < arr.size ∧ producedLen arr i ≤ j ∧ j < producedLen arr (i + 1) := by
    expose_names; exact (correctness_goal_1_0 arr h_precond j hj)
  rcases hex_unique with ⟨i, hi, hui⟩
  have hval : (implementation arr)[j]! = if arr[i]! = 0 then 0 else arr[i]! := by
    expose_names; exact (correctness_goal_1_1 arr h_precond j hj i hi hui)
  refine ⟨i, ?_, ?_⟩
  · exact ⟨hi.1, hi.2.1, hi.2.2, hval⟩
  · intro i' hi'
    have hi'bounds : i' < arr.size ∧ producedLen arr i' ≤ j ∧ j < producedLen arr (i' + 1) :=
      ⟨hi'.1, hi'.2.1, hi'.2.2.1⟩
    have : i' = i := hui i' hi'bounds
    simpa [this]

theorem correctness_goal
    (arr : Array Int)
    (h_precond : precondition arr)
    : postcondition arr (implementation arr) := by
  classical
  unfold postcondition
  constructor
  · have h_size : (implementation arr).size = arr.size := by
      expose_names; exact (correctness_goal_0 arr)
    exact h_size
  · intro j hj
    have h_main :
        ∃! (i : Nat),
          i < arr.size ∧
          producedLen arr i ≤ j ∧
          j < producedLen arr (i + 1) ∧
          (implementation arr)[j]! = (if arr[i]! = 0 then (0 : Int) else arr[i]!) := by
      expose_names; exact (correctness_goal_1 arr h_precond j hj)
    simpa using h_main
end Proof
