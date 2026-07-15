import Lean
import Mathlib.Tactic
import Velvet.Std

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
  -- Kadane's algorithm (maximum subarray), single pass.
  -- We must avoid counting the first element twice: initialize from nums[0]!
  -- and then fold over the remaining elements.
  let init : Int := nums[0]!
  let step (state : Int × Int) (x : Int) : Int × Int :=
    let cur := state.1
    let best := state.2
    let cur' :=
      -- either extend previous best-ending-here subarray, or start fresh at x
      if cur + x < x then x else cur + x
    let best' := if best < cur' then cur' else best
    (cur', best')
  let tail : Array Int := nums.extract 1 nums.size
  (tail.foldl step (init, init)).2
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

section Assertions
-- Test case 1
#assert_same_evaluation #[(implementation test1_nums), test1_Expected]

-- Test case 2
#assert_same_evaluation #[(implementation test2_nums), test2_Expected]

-- Test case 3
#assert_same_evaluation #[(implementation test3_nums), test3_Expected]

-- Test case 4
#assert_same_evaluation #[(implementation test4_nums), test4_Expected]

-- Test case 5
#assert_same_evaluation #[(implementation test5_nums), test5_Expected]

-- Test case 6
#assert_same_evaluation #[(implementation test6_nums), test6_Expected]

-- Test case 7
#assert_same_evaluation #[(implementation test7_nums), test7_Expected]

-- Test case 8
#assert_same_evaluation #[(implementation test8_nums), test8_Expected]

-- Test case 9
#assert_same_evaluation #[(implementation test9_nums), test9_Expected]
end Assertions

section Proof
theorem correctness_goal_0
    (nums : Array ℤ)
    (h_precond : precondition nums)
    : ∀ (start stop : ℕ), rangeSum nums start stop = List.foldl (fun acc x => acc + x) 0 (nums.toList.extract start stop) := by
  intro start stop
  -- `h_precond` is not needed for this lemma.
  unfold rangeSum arraySum
  -- Bridge `Array.foldl` to `List.foldl` via `toList` and commute `extract` with `toList`.
  calc
    (nums.extract start stop).foldl (fun acc x => acc + x) 0
        = (nums.extract start stop).toList.foldl (fun acc x => acc + x) 0 := by
            simpa using
              (Array.foldl_toList (xs := nums.extract start stop)
                (f := fun acc x => acc + x) (init := (0 : ℤ))).symm
    _ = (nums.toList.extract start stop).foldl (fun acc x => acc + x) 0 := by
          simp [Array.toList_extract]
    _ = List.foldl (fun acc x => acc + x) 0 (nums.toList.extract start stop) := by
          rfl

theorem correctness_goal_1
    (nums : Array ℤ)
    : implementation nums =
  let l := nums.toList;
  let init := nums[0]?.getD 0;
  let step := fun state x =>
    let cur := state.1;
    let best := state.2;
    let cur' := if cur + x < x then x else cur + x;
    let best' := if best < cur' then cur' else best;
    (cur', best');
  let tailL := l.extract 1;
  (List.foldl step (init, init) tailL).2 := by
  -- `nums[0]!` agrees with `nums[0]?.getD 0` since `Int`'s default inhabitant is `0`.
  have hinit : (nums[0]!) = nums[0]?.getD 0 := by
    simpa using (Array.get!_eq_getD_getElem? (xs := nums) (i := 0))

  -- unfold the implementation and inline the RHS `let`s
  simp [implementation, hinit]

  -- name the (simplified) step function that `simp` produced
  set step : (ℤ × ℤ) → ℤ → (ℤ × ℤ) :=
    fun state x =>
      (if state.1 < 0 then x else state.1 + x,
        if state.2 < (if state.1 < 0 then x else state.1 + x) then (if state.1 < 0 then x else state.1 + x)
        else state.2)

  -- it suffices to show the folded pairs coincide
  apply congrArg Prod.snd

  have hsize : (nums.extract 1).size = nums.size - 1 := by
    simp [Array.size_extract]

  have htail_toList : (nums.extract 1).toList = nums.toList.extract 1 nums.size := by
    -- `nums.extract 1` means `nums.extract 1 nums.size`
    simpa using (Array.toList_extract (xs := nums) (start := 1) (stop := nums.size))

  -- convert the array fold to the corresponding list fold
  calc
    Array.foldl step (nums[0]?.getD 0, nums[0]?.getD 0) (nums.extract 1) 0 (nums.size - 1)
        = Array.foldl step (nums[0]?.getD 0, nums[0]?.getD 0) (nums.extract 1) 0 (nums.extract 1).size := by
            simpa [hsize]
    _ = (nums.extract 1).foldl step (nums[0]?.getD 0, nums[0]?.getD 0) := by
            rfl
    _ = (nums.extract 1).toList.foldl step (nums[0]?.getD 0, nums[0]?.getD 0) := by
            simpa using
              (Array.foldl_toList step (init := (nums[0]?.getD 0, nums[0]?.getD 0)) (xs := (nums.extract 1))).symm
    _ = (nums.toList.extract 1 nums.size).foldl step (nums[0]?.getD 0, nums[0]?.getD 0) := by
            simpa [htail_toList]
    _ = List.foldl step (nums[0]?.getD 0, nums[0]?.getD 0) (List.take (nums.size - 1) nums.toList.tail) := by
            -- `List.extract` unfolds to `take (stop-start)` of the tail
            simp [List.extract, Array.length_toList]

theorem correctness_goal_2 : ∀ (l : List ℤ),
  l.length > 0 →
    let init := l.get! 0;
    let step := fun state x =>
      let cur := state.1;
      let best := state.2;
      let cur' := if cur + x < x then x else cur + x;
      let best' := if best < cur' then cur' else best;
      (cur', best');
    let tailL := l.extract 1;
    let result := (List.foldl step (init, init) tailL).2;
    (∃ start stop,
        start < stop ∧ stop ≤ l.length ∧ List.foldl (fun acc x => acc + x) 0 (l.extract start stop) = result) ∧
      ∀ (start stop : ℕ),
        start < stop ∧ stop ≤ l.length → List.foldl (fun acc x => acc + x) 0 (l.extract start stop) ≤ result := by
  intro l hl
  classical
  cases l with
  | nil =>
      simp at hl
  | cons a t =>
      let sumSeg (l : List ℤ) (start stop : Nat) : ℤ :=
        List.foldl (fun acc x => acc + x) 0 (l.extract start stop)

      let step : (ℤ × ℤ) → ℤ → (ℤ × ℤ) := fun state x =>
        let cur := state.1
        let best := state.2
        let cur' := if cur + x < x then x else cur + x
        let best' := if best < cur' then cur' else best
        (cur', best')

      let BestSpec (l : List ℤ) (best : ℤ) : Prop :=
        (∃ start stop,
            start < stop ∧ stop ≤ l.length ∧ sumSeg l start stop = best) ∧
          ∀ start stop, start < stop ∧ stop ≤ l.length → sumSeg l start stop ≤ best

      let CurSpec (l : List ℤ) (cur : ℤ) : Prop :=
        (∃ start, start < l.length ∧ sumSeg l start l.length = cur) ∧
          ∀ start, start < l.length → sumSeg l start l.length ≤ cur

      let Inv (l : List ℤ) (st : ℤ × ℤ) : Prop :=
        CurSpec l st.1 ∧ BestSpec l st.2 ∧ st.1 ≤ st.2

      have sumSeg_append_of_stop_le (pref : List ℤ) (x : ℤ) (start stop : Nat)
          (hstartstop : start < stop) (hstop : stop ≤ pref.length) :
          sumSeg (pref ++ [x]) start stop = sumSeg pref start stop := by
        have hstartle : start ≤ pref.length := le_trans (Nat.le_of_lt hstartstop) hstop
        unfold sumSeg
        simp [List.extract_eq_drop_take]
        have : start - pref.length = 0 := Nat.sub_eq_zero_of_le hstartle
        simp [List.drop_append, this]
        -- reduce the extra `take` on `[x]` to `take 0`.
        have hsub : stop - start - (pref.length - start) = 0 := by
          have : stop - start ≤ pref.length - start := Nat.sub_le_sub_right hstop start
          exact Nat.sub_eq_zero_of_le this
        simp [List.take_append, List.length_drop, hstartle, hsub]

      have sumSeg_append_last_of_lt (pref : List ℤ) (x : ℤ) (start : Nat)
          (hstart : start < pref.length) :
          sumSeg (pref ++ [x]) start (pref.length + 1) = sumSeg pref start pref.length + x := by
        have hstartle : start ≤ pref.length := Nat.le_of_lt hstart
        unfold sumSeg
        -- rewrite both extracts as drop/take
        simp [List.extract_eq_drop_take]
        have : start - pref.length = 0 := Nat.sub_eq_zero_of_le hstartle
        simp [List.drop_append, this]
        -- simplify the take to all elements
        have hlen : (pref.drop start ++ [x]).length = pref.length + 1 - start := by
          simp [List.length_drop, hstartle]
          omega
        -- use take_length
        have htake : (pref.drop start ++ [x]).take (pref.length + 1 - start) = (pref.drop start ++ [x]) := by
          -- rewrite the count to the list length
          simpa [hlen] using (List.take_length (l := pref.drop start ++ [x]))
        -- now compute the foldl sum
        -- also simplify sumSeg pref start pref.length to folding over drop start
        have htake2 : (pref.drop start).take (pref.length - start) = pref.drop start := by
          have hlen2 : (pref.drop start).length = pref.length - start := by
            simp [List.length_drop, hstartle]
          simpa [hlen2] using (List.take_length (l := pref.drop start))
        -- finish
        simp [htake, htake2, List.foldl_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

      have sumSeg_append_last_eq (pref : List ℤ) (x : ℤ) :
          sumSeg (pref ++ [x]) pref.length (pref.length + 1) = x := by
        unfold sumSeg
        simp [List.extract_eq_drop_take, List.drop_append, List.foldl_append]

      have inv_step : ∀ (pref : List ℤ) (st : ℤ × ℤ),
          pref.length > 0 → Inv pref st → ∀ x, Inv (pref ++ [x]) (step st x) := by
        intro pref st hp hInv x
        rcases hInv with ⟨hCur, hBest, hcurle⟩
        rcases hCur with ⟨⟨sCur, hsCurLt, hsCurEq⟩, hsCurUb⟩
        rcases hBest with ⟨⟨sBest, eBest, hsBestLt, heBestLe, hsBestEq⟩, hsBestUb⟩
        set cur : ℤ := st.1
        set best : ℤ := st.2
        set cur' : ℤ := if cur + x < x then x else cur + x
        set best' : ℤ := if best < cur' then cur' else best
        have hstep : step st x = (cur', best') := by
          simp [step, cur, best, cur', best']

        have hCur' : CurSpec (pref ++ [x]) cur' := by
          constructor
          · by_cases hcx : cur + x < x
            · refine ⟨pref.length, by simp, ?_⟩
              have : cur' = x := by simp [cur', hcx]
              simp [this, sumSeg_append_last_eq]
            · have : cur' = cur + x := by simp [cur', hcx]
              refine ⟨sCur, ?_, ?_⟩
              · have : sCur < pref.length := hsCurLt
                have : sCur < (pref ++ [x]).length := by
                  simpa using Nat.lt_trans hsCurLt (Nat.lt_succ_self _)
                simpa using this
              · have hsEqCur : sumSeg pref sCur pref.length = cur := by
                  simpa [cur] using hsCurEq
                have hs : sumSeg (pref ++ [x]) sCur (pref.length + 1) = sumSeg pref sCur pref.length + x :=
                  sumSeg_append_last_of_lt pref x sCur hsCurLt
                simp [this, hsEqCur, hs]
          · intro start hstartLt
            have hle : start ≤ pref.length := by
              have : start < pref.length + 1 := by simpa using hstartLt
              exact Nat.lt_succ_iff.mp this
            cases lt_or_eq_of_le hle with
            | inl hlt =>
                have hs : sumSeg (pref ++ [x]) start (pref.length + 1) = sumSeg pref start pref.length + x :=
                  sumSeg_append_last_of_lt pref x start hlt
                by_cases hcx : cur + x < x
                · have hcur' : cur' = x := by simp [cur', hcx]
                  have hub : sumSeg pref start pref.length ≤ cur := by
                    have : sumSeg pref start pref.length ≤ st.1 := hsCurUb start hlt
                    simpa [cur] using this
                  have hub' : sumSeg pref start pref.length + x ≤ cur + x := add_le_add_right hub x
                  have hx : cur + x ≤ x := le_of_lt hcx
                  have : sumSeg pref start pref.length + x ≤ x := le_trans hub' hx
                  simpa [hs, hcur'] using this
                · have hcur' : cur' = cur + x := by simp [cur', hcx]
                  have hub : sumSeg pref start pref.length ≤ cur := by
                    have : sumSeg pref start pref.length ≤ st.1 := hsCurUb start hlt
                    simpa [cur] using this
                  have : sumSeg pref start pref.length + x ≤ cur + x := add_le_add_right hub x
                  simpa [hs, hcur'] using this
            | inr heq =>
                subst heq
                have hs : sumSeg (pref ++ [x]) pref.length (pref.length + 1) = x :=
                  sumSeg_append_last_eq pref x
                by_cases hcx : cur + x < x
                · have hcur' : cur' = x := by simp [cur', hcx]
                  simpa [hs, hcur']
                · have hcur' : cur' = cur + x := by simp [cur', hcx]
                  have hxle : x ≤ cur + x := le_of_not_gt hcx
                  simpa [hs, hcur'] using hxle

        have hBest' : BestSpec (pref ++ [x]) best' := by
          constructor
          · by_cases hbc : best < cur'
            · have hbest' : best' = cur' := by simp [best', hbc]
              rcases hCur'.1 with ⟨s, hslt, hseq⟩
              refine ⟨s, (pref ++ [x]).length, hslt, le_rfl, ?_⟩
              simpa [hbest'] using hseq
            · have hbest' : best' = best := by simp [best', hbc]
              refine ⟨sBest, eBest, hsBestLt, le_trans heBestLe (by simp), ?_⟩
              have hsEq : sumSeg (pref ++ [x]) sBest eBest = sumSeg pref sBest eBest :=
                sumSeg_append_of_stop_le pref x sBest eBest hsBestLt heBestLe
              have hsBestEq' : sumSeg pref sBest eBest = best := by simpa [best] using hsBestEq
              simpa [hbest', hsEq, hsBestEq']
          · intro start stop hseg
            rcases hseg with ⟨hss, hstop⟩
            have hlen : (pref ++ [x]).length = pref.length + 1 := by simp
            have hstop' : stop ≤ pref.length ∨ stop = pref.length + 1 := by
              have : stop ≤ pref.length + 1 := by simpa [hlen] using hstop
              exact Nat.le_or_eq_of_le_succ this
            cases hstop' with
            | inl hstopLe =>
                have hsEq : sumSeg (pref ++ [x]) start stop = sumSeg pref start stop :=
                  sumSeg_append_of_stop_le pref x start stop hss hstopLe
                have hub : sumSeg pref start stop ≤ best := hsBestUb start stop ⟨hss, hstopLe⟩
                by_cases hbc : best < cur'
                · have hbest' : best' = cur' := by simp [best', hbc]
                  have : best ≤ cur' := le_of_lt hbc
                  exact le_trans (by simpa [hsEq] using hub) (by simpa [hbest'] using this)
                · have hbest' : best' = best := by simp [best', hbc]
                  simpa [hsEq, hbest'] using hub
            | inr hstopEq =>
                subst hstopEq
                have hubCur_len : sumSeg (pref ++ [x]) start (pref ++ [x]).length ≤ cur' :=
                  hCur'.2 start (by
                    -- start < stop = length
                    have : start < (pref ++ [x]).length := lt_of_lt_of_le hss hstop
                    exact this)
                have hubCur : sumSeg (pref ++ [x]) start (pref.length + 1) ≤ cur' := by
                  simpa [hlen] using hubCur_len
                by_cases hbc : best < cur'
                · have hbest' : best' = cur' := by simp [best', hbc]
                  simpa [hbest'] using hubCur
                · have hbest' : best' = best := by simp [best', hbc]
                  have : cur' ≤ best := le_of_not_gt hbc
                  exact le_trans hubCur (by simpa [hbest'] using this)

        have hcurle' : cur' ≤ best' := by
          by_cases hbc : best < cur'
          · simp [best', hbc]
          · have : cur' ≤ best := le_of_not_gt hbc
            simp [best', hbc, this]

        simpa [Inv, hstep] using And.intro hCur' (And.intro hBest' hcurle')

      have inv_scan : ∀ (rest : List ℤ) (pref : List ℤ) (st : ℤ × ℤ),
          pref.length > 0 → Inv pref st → Inv (pref ++ rest) (List.foldl step st rest) := by
        intro rest
        induction rest with
        | nil =>
            intro pref st hp hInv
            simpa using hInv
        | cons x xs ih =>
            intro pref st hp hInv
            have hInv' : Inv (pref ++ [x]) (step st x) := inv_step pref st hp hInv x
            have hp' : (pref ++ [x]).length > 0 := by simpa using Nat.lt_trans hp (by simp)
            simpa [List.foldl, List.append_assoc] using ih (pref := pref ++ [x]) (st := step st x) hp' hInv'

      have inv_singleton : Inv [a] (a, a) := by
        have hCur : CurSpec [a] a := by
          constructor
          · refine ⟨0, by simp, ?_⟩
            simp [sumSeg, List.extract_eq_drop_take]
          · intro start hlt
            have : start = 0 := by
              have : start < 1 := by simpa using hlt
              exact Nat.lt_one_iff.mp this
            subst this
            simp [sumSeg, List.extract_eq_drop_take]
        have hBest : BestSpec [a] a := by
          constructor
          · refine ⟨0, 1, by simp, by simp, ?_⟩
            simp [sumSeg, List.extract_eq_drop_take]
          · intro start stop hseg
            rcases hseg with ⟨hss, hstop⟩
            have hstop_le1 : stop ≤ 1 := by simpa using hstop
            have h1le_stop : 1 ≤ stop := by
              have h0lt_stop : 0 < stop := lt_of_le_of_lt (Nat.zero_le start) hss
              simpa using (Nat.succ_le_of_lt h0lt_stop)
            have hstop1 : stop = 1 := le_antisymm hstop_le1 h1le_stop
            have hstart0 : start = 0 := by
              have : start < 1 := by simpa [hstop1] using Nat.lt_of_lt_of_le hss hstop
              exact Nat.lt_one_iff.mp this
            subst hstart0; subst hstop1
            simp [sumSeg, List.extract_eq_drop_take]
        simp [Inv, hCur, hBest]

      have hInvAll : Inv ([a] ++ t) (List.foldl step (a, a) t) :=
        inv_scan (rest := t) (pref := [a]) (st := (a, a)) (by simp) inv_singleton

      have hBestAll : BestSpec (a :: t) (List.foldl step (a, a) t).2 := by
        simpa [Inv] using hInvAll.2.1

      simpa [BestSpec, sumSeg, step, List.extract_eq_drop_take] using hBestAll

theorem correctness_goal
    (nums : Array Int)
    (h_precond : precondition nums)
    : postcondition nums (implementation nums) := by
  classical

  have h_rangeSum_toList :
      (∀ start stop,
        rangeSum nums start stop =
          (nums.toList.extract start stop).foldl (fun acc x => acc + x) 0) := by
    expose_names; exact (correctness_goal_0 nums h_precond)

  -- Use init written via get? to match simp-normal form.
  have h_impl_toList :
      implementation nums =
        (let l := nums.toList
         let init : Int := nums[0]?.getD 0
         let step (state : Int × Int) (x : Int) : Int × Int :=
           let cur := state.1
           let best := state.2
           let cur' := if cur + x < x then x else cur + x
           let best' := if best < cur' then cur' else best
           (cur', best')
         let tailL : List Int := l.extract 1 l.length
         (tailL.foldl step (init, init)).2) := by
    expose_names; exact (correctness_goal_1 nums)

  have h_kadane_list_correct :
      (∀ (l : List Int), l.length > 0 →
        let init : Int := l.get! 0
        let step (state : Int × Int) (x : Int) : Int × Int :=
          let cur := state.1
          let best := state.2
          let cur' := if cur + x < x then x else cur + x
          let best' := if best < cur' then cur' else best
          (cur', best')
        let tailL : List Int := l.extract 1 l.length
        let result : Int := (tailL.foldl step (init, init)).2
        (∃ start stop,
            start < stop ∧ stop ≤ l.length ∧
              (l.extract start stop).foldl (fun acc x => acc + x) 0 = result) ∧
          (∀ start stop,
            start < stop ∧ stop ≤ l.length →
              (l.extract start stop).foldl (fun acc x => acc + x) 0 ≤ result)) := by
    expose_names; exact (correctness_goal_2)

  have h_len : nums.toList.length > 0 := by
    expose_names; intros; expose_names; assumption

  have hk := h_kadane_list_correct nums.toList h_len

  unfold postcondition
  constructor
  · rcases hk.1 with ⟨start, stop, hlt, hle, hsum⟩
    refine ⟨start, stop, hlt, ?_, ?_⟩
    · expose_names; intros; expose_names; try simp_all; try grind
    · rw [h_rangeSum_toList start stop]
      rw [h_impl_toList]
      simpa using hsum
  · intro start stop h
    have h' : start < stop ∧ stop ≤ nums.toList.length := by
      expose_names; intros; expose_names; try simp_all; try grind
    have := hk.2 start stop h'
    simpa [h_rangeSum_toList start stop, h_impl_toList] using this
end Proof
