import Lean
import Mathlib.Tactic
import Velvet.Std
import Extensions.VelvetPBT

set_option maxHeartbeats 10000000

section Specs
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false

/- Problem Description
    RemoveDuplicatesFromSortedArrayII: given a sorted (non-decreasing) integer array, keep each value at most twice.
    **Important: complexity should be O(n) time and O(1) space**
    Natural language breakdown:
    1. The input is an array of integers sorted in non-decreasing order.
    2. The output consists of a number k and an array out representing the modified array state.
    3. Only the first k elements of out are relevant; elements beyond index k are unconstrained.
    4. The first k elements must be in non-decreasing order.
    5. For every integer value x, the number of occurrences of x in the first k elements is the minimum of:
       a. 2, and
       b. the number of occurrences of x in the entire input array.
    6. Therefore, each distinct value appears at most twice in the kept prefix.
    7. Because the input is sorted and the output prefix is required to be sorted with these exact capped counts,
       the kept prefix is uniquely determined and preserves the relative order implied by sortedness.
-/

-- Helper: count occurrences of x in the first k positions of arr.
-- Uses Array.take to avoid any out-of-bounds access.
-- Note: This is a declarative observation function used in the specification.
def countInPrefix (arr : Array Int) (k : Nat) (x : Int) : Nat :=
  (arr.take k).count x

-- Helper: non-decreasing sortedness of the first k elements.
def sortedPrefix (arr : Array Int) (k : Nat) : Prop :=
  ∀ (i : Nat), i + 1 < k → arr[i]! ≤ arr[i + 1]!

-- Precondition: the whole input array is sorted in non-decreasing order.
def precondition (nums : Array Int) : Prop :=
  sortedPrefix nums nums.size

-- Postcondition: result is (k, out), where out is the post-state array.
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

  -- Pass 1: write the allowed elements (each value at most twice) into the front.
  let rec go (i : Nat) (write : Nat) (last : Option Int) (cnt : Nat) (out : Array Int) :
      Nat × Array Int :=
    if h : i < n then
      let x : Int := nums.get i h
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

  -- Pass 2: fill the unused suffix with zeros (tests expect zero padding).
  let rec fillZero (j : Nat) (out : Array Int) : Array Int :=
    if h : j < n then
      fillZero (j + 1) (out.set! j (0 : Int))
    else
      out
  termination_by nums.size - j

  (k, fillZero k out1)
end Impl

section TestCases
-- Test case 1: Example 1
-- Input: [1,1,1,2,2,3]
-- Output: k = 5, prefix [1,1,2,2,3]
def test1_nums : Array Int := #[1, 1, 1, 2, 2, 3]
def test1_Expected : Nat × Array Int := (5, #[1, 1, 2, 2, 3, 0])

-- Test case 2: Example 2
-- Input: [0,0,1,1,1,1,2,3,3]
-- Output: k = 7, prefix [0,0,1,1,2,3,3]
def test2_nums : Array Int := #[0, 0, 1, 1, 1, 1, 2, 3, 3]
def test2_Expected : Nat × Array Int := (7, #[0, 0, 1, 1, 2, 3, 3, 0, 0])

-- Test case 3: Empty array (boundary)
def test3_nums : Array Int := #[]
def test3_Expected : Nat × Array Int := (0, #[])

-- Test case 4: Singleton array (boundary)
def test4_nums : Array Int := #[7]
def test4_Expected : Nat × Array Int := (1, #[7])

-- Test case 5: All elements identical, more than twice
-- Input: [2,2,2,2] -> keep only two 2s
-- Trailing elements are arbitrary; keep size unchanged.
def test5_nums : Array Int := #[2, 2, 2, 2]
def test5_Expected : Nat × Array Int := (2, #[2, 2, 0, 0])

-- Test case 6: Already satisfies "at most twice" everywhere
-- Input is unchanged, k = size

def test6_nums : Array Int := #[1, 1, 2, 2, 3, 3]
def test6_Expected : Nat × Array Int := (6, #[1, 1, 2, 2, 3, 3])

-- Test case 7: Includes negative values and multiple runs exceeding 2
-- Input: [-1,-1,-1,0,0,0,1] -> prefix [-1,-1,0,0,1]
def test7_nums : Array Int := #[-1, -1, -1, 0, 0, 0, 1]
def test7_Expected : Nat × Array Int := (5, #[-1, -1, 0, 0, 1, 0, 0])

-- Test case 8: No duplicates at all (k = size)
def test8_nums : Array Int := #[0, 1, 2]
def test8_Expected : Nat × Array Int := (3, #[0, 1, 2])

-- Test case 9: Multiple groups with some exceeding 2
-- Input: [0,0,0,1,1,2,2,2,2,3] -> prefix [0,0,1,1,2,2,3]
def test9_nums : Array Int := #[0, 0, 0, 1, 1, 2, 2, 2, 2, 3]
def test9_Expected : Nat × Array Int := (7, #[0, 0, 1, 1, 2, 2, 3, 0, 0, 0])
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

section Pbt
method implementationPbt (nums : Array Int)
  return (result : Nat × Array Int)
  require precondition nums
  ensures postcondition nums result
  do
  return (implementation nums)

velvet_plausible_test implementationPbt (config := { maxMs := some 20000 })
end Pbt

section Proof
theorem correctness_goal_0_0
    (nums : Array ℤ)
    (k : ℕ)
    (out1 : Array ℤ)
    (hgo_res : implementation.go nums 0 0 none 0 nums = (k, out1))
    : out1.size = nums.size := by
  classical
  let n : Nat := nums.size

  have go_size_aux :
      ∀ rem i write (last : Option Int) cnt (out : Array Int),
        n - i = rem →
        out.size = n →
        (implementation.go nums i write last cnt out).2.size = n := by
    intro rem
    induction rem with
    | zero =>
        intro i write last cnt out hrem hout
        have hle : n ≤ i := by
          have : n - i = 0 := by simpa using hrem
          exact (Nat.sub_eq_zero_iff_le).1 this
        have hnot : ¬ i < n := not_lt_of_ge hle
        have hnot' : ¬ i < nums.size := by simpa [n] using hnot
        -- unfold one step and simplify the base case
        rw [implementation.go.eq_def]
        simp [hnot', hout, n]
    | succ rem ih =>
        intro i write last cnt out hrem hout
        have hi : i < n := by
          have : 0 < n - i := by simpa [hrem] using Nat.succ_pos rem
          exact (Nat.sub_pos_iff_lt).1 this
        have hi' : i < nums.size := by simpa [n] using hi
        have hrem' : n - (i + 1) = rem := by
          calc
            n - (i + 1) = n - i.succ := by rfl
            _ = n - i - 1 := by simpa [Nat.sub_succ']
            _ = (rem.succ) - 1 := by simpa [hrem]
            _ = rem := by simp
        -- unfold one step and simplify the recursive case
        rw [implementation.go.eq_def]
        -- reduce the outer `if` using `hi'`
        simp [hi']
        cases last with
        | none =>
            -- recursive call that writes
            have hout' : (out.setIfInBounds write (nums.get i hi')).size = n := by
              simpa [Array.size_setIfInBounds, hout]
            simpa [hrem'] using
              ih (i := i + 1) (write := write + 1) (last := some (nums.get i hi')) (cnt := 1)
                (out := out.setIfInBounds write (nums.get i hi')) hrem' hout'
        | some l =>
            by_cases hxeq : nums.get i hi' = l
            · by_cases hcnt : cnt < 2
              · have hout' : (out.setIfInBounds write (nums.get i hi')).size = n := by
                  simpa [Array.size_setIfInBounds, hout]
                simpa [hxeq, hcnt, hrem'] using
                  ih (i := i + 1) (write := write + 1) (last := some l) (cnt := cnt + 1)
                    (out := out.setIfInBounds write (nums.get i hi')) hrem' hout'
              · -- no write
                simpa [hxeq, hcnt, hrem'] using
                  ih (i := i + 1) (write := write) (last := some l) (cnt := cnt)
                    (out := out) hrem' hout
            · -- new value, write
              have hout' : (out.setIfInBounds write (nums.get i hi')).size = n := by
                simpa [Array.size_setIfInBounds, hout]
              simpa [hxeq, hrem'] using
                ih (i := i + 1) (write := write + 1) (last := some (nums.get i hi')) (cnt := 1)
                  (out := out.setIfInBounds write (nums.get i hi')) hrem' hout'

  have hsize : (implementation.go nums 0 0 none 0 nums).2.size = nums.size := by
    have := go_size_aux n 0 0 (none : Option Int) 0 nums (by simp [n]) (by simp [n])
    simpa [n] using this

  have hsnd : (implementation.go nums 0 0 none 0 nums).2 = out1 := by
    simpa using congrArg Prod.snd hgo_res

  simpa [hsnd] using hsize

theorem correctness_goal_0_1
    (nums : Array ℤ)
    (k : ℕ)
    (out1 : Array ℤ)
    (hgo_res : implementation.go nums 0 0 none 0 nums = (k, out1))
    : k ≤ nums.size := by
  classical

  have hwf :
      ∀ m : Nat,
        ∀ i write last cnt out,
          nums.size - i = m →
            (implementation.go nums i write last cnt out).1 ≤ write + m := by
    intro m
    refine (Nat.lt_wfRel.wf.induction
      (C := fun m =>
        ∀ i write last cnt out,
          nums.size - i = m →
            (implementation.go nums i write last cnt out).1 ≤ write + m)
      (a := m) ?_)
    intro m ih i write last cnt out him

    by_cases hi : i < nums.size
    · have hmpos : 0 < m := by
        simpa [him] using (Nat.sub_pos_of_lt hi)
      have hmne : m ≠ 0 := Nat.ne_of_gt hmpos
      have hlt : Nat.pred m < m := Nat.pred_lt hmne
      have him_succ : nums.size - (i + 1) = Nat.pred m := by
        calc
          nums.size - (i + 1) = Nat.pred (nums.size - i) := by
            simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using (Nat.sub_succ nums.size i)
          _ = Nat.pred m := by simp [him]

      cases last with
      | none =>
          have hrec :
              (implementation.go nums (i + 1) (write + 1) (some (nums.get i hi)) 1
                (out.set! write (nums.get i hi))).1 ≤ (write + 1) + Nat.pred m := by
            exact ih (Nat.pred m) hlt (i + 1) (write + 1) (some (nums.get i hi)) 1
              (out.set! write (nums.get i hi)) him_succ

          have hpred : Nat.pred m + 1 = m := by
            simpa [Nat.succ_eq_add_one, Nat.add_comm] using (Nat.succ_pred hmne)

          have hadd : (write + 1) + Nat.pred m = write + m := by
            calc
              (write + 1) + Nat.pred m = write + (1 + Nat.pred m) := by
                simp [Nat.add_assoc]
              _ = write + (Nat.pred m + 1) := by
                simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
              _ = write + m := by
                simpa using congrArg (fun t => write + t) hpred

          unfold implementation.go
          have :
              (implementation.go nums (i + 1) (write + 1) (some (nums.get i hi)) 1
                    (out.set! write (nums.get i hi))).1 ≤ write + m :=
            le_trans hrec (le_of_eq hadd)
          simpa [hi] using this

      | some l =>
          by_cases hxl : nums.get i hi = l
          · by_cases hcnt : cnt < 2
            · have hrec :
                  (implementation.go nums (i + 1) (write + 1) (some l) (cnt + 1)
                    (out.set! write (nums.get i hi))).1 ≤ (write + 1) + Nat.pred m := by
                exact ih (Nat.pred m) hlt (i + 1) (write + 1) (some l) (cnt + 1)
                  (out.set! write (nums.get i hi)) him_succ

              have hpred : Nat.pred m + 1 = m := by
                simpa [Nat.succ_eq_add_one, Nat.add_comm] using (Nat.succ_pred hmne)
              have hadd : (write + 1) + Nat.pred m = write + m := by
                calc
                  (write + 1) + Nat.pred m = write + (1 + Nat.pred m) := by
                    simp [Nat.add_assoc]
                  _ = write + (Nat.pred m + 1) := by
                    simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
                  _ = write + m := by
                    simpa using congrArg (fun t => write + t) hpred

              unfold implementation.go
              have :
                  (implementation.go nums (i + 1) (write + 1) (some l) (cnt + 1)
                      (out.set! write (nums.get i hi))).1 ≤ write + m :=
                le_trans hrec (le_of_eq hadd)
              simpa [hi, hxl, hcnt] using this

            · have hrec :
                  (implementation.go nums (i + 1) write (some l) cnt out).1 ≤ write + Nat.pred m := by
                exact ih (Nat.pred m) hlt (i + 1) write (some l) cnt out him_succ

              have hpred_le : Nat.pred m ≤ m := Nat.le_of_lt (Nat.pred_lt hmne)

              unfold implementation.go
              have : (implementation.go nums (i + 1) write (some l) cnt out).1 ≤ write + m :=
                le_trans hrec (Nat.add_le_add_left hpred_le write)
              simpa [hi, hxl, hcnt] using this

          · have hrec :
                (implementation.go nums (i + 1) (write + 1) (some (nums.get i hi)) 1
                  (out.set! write (nums.get i hi))).1 ≤ (write + 1) + Nat.pred m := by
              exact ih (Nat.pred m) hlt (i + 1) (write + 1) (some (nums.get i hi)) 1
                (out.set! write (nums.get i hi)) him_succ

            have hpred : Nat.pred m + 1 = m := by
              simpa [Nat.succ_eq_add_one, Nat.add_comm] using (Nat.succ_pred hmne)
            have hadd : (write + 1) + Nat.pred m = write + m := by
              calc
                (write + 1) + Nat.pred m = write + (1 + Nat.pred m) := by
                  simp [Nat.add_assoc]
                _ = write + (Nat.pred m + 1) := by
                  simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
                _ = write + m := by
                  simpa using congrArg (fun t => write + t) hpred

            unfold implementation.go
            have :
                (implementation.go nums (i + 1) (write + 1) (some (nums.get i hi)) 1
                      (out.set! write (nums.get i hi))).1 ≤ write + m :=
              le_trans hrec (le_of_eq hadd)
            simpa [hi, hxl] using this

    · -- exit case
      unfold implementation.go
      simpa [hi] using (Nat.le_add_right write m)

  have hfst : (implementation.go nums 0 0 none 0 nums).1 ≤ nums.size := by
    have := hwf nums.size 0 0 none 0 nums (by simp)
    simpa using this

  have hk : (implementation.go nums 0 0 none 0 nums).1 = k := congrArg Prod.fst hgo_res
  simpa [hk] using hfst

theorem correctness_goal_0_2
    (nums : Array ℤ)
    (h_precond : precondition nums)
    (k : ℕ)
    (out1 : Array ℤ)
    (hgo_res : implementation.go nums 0 0 none 0 nums = (k, out1))
    (h_size : out1.size = nums.size)
    (h_k_le : k ≤ nums.size)
    : ∀ (i : ℕ), i + 1 < k → out1[i]! ≤ out1[i + 1]! := by
    sorry

theorem correctness_goal_0_3
    (nums : Array ℤ)
    (h_precond : precondition nums)
    (k : ℕ)
    (out1 : Array ℤ)
    (hgo_res : implementation.go nums 0 0 none 0 nums = (k, out1))
    (h_size : out1.size = nums.size)
    (h_k_le : k ≤ nums.size)
    (h_sorted : ∀ (i : ℕ), i + 1 < k → out1[i]! ≤ out1[i + 1]!)
    : ∀ (x : ℤ), Array.count x (out1.extract 0 k) = Nat.min 2 (Array.count x nums) := by
    sorry

theorem correctness_goal_0
    (nums : Array ℤ)
    (h_precond : precondition nums)
    (k : ℕ)
    (out1 : Array ℤ)
    (hgo_res : implementation.go nums 0 0 none 0 nums = (k, out1))
    : out1.size = nums.size ∧
  k ≤ nums.size ∧
    (∀ (i : ℕ), i + 1 < k → out1[i]! ≤ out1[i + 1]!) ∧
      ∀ (x : ℤ), Array.count x (out1.extract 0 k) = Nat.min 2 (Array.count x nums) := by
  have h_size : out1.size = nums.size := by
    expose_names; exact (correctness_goal_0_0 nums k out1 hgo_res)
  have h_k_le : k ≤ nums.size := by
    expose_names; exact (correctness_goal_0_1 nums k out1 hgo_res)
  have h_sorted : (∀ (i : ℕ), i + 1 < k → out1[i]! ≤ out1[i + 1]!) := by
    expose_names; exact (correctness_goal_0_2 nums h_precond k out1 hgo_res h_size h_k_le)
  have h_count : ∀ (x : ℤ), Array.count x (out1.extract 0 k) = Nat.min 2 (Array.count x nums) := by
    expose_names; exact (correctness_goal_0_3 nums h_precond k out1 hgo_res h_size h_k_le h_sorted)
  exact ⟨h_size, h_k_le, h_sorted, h_count⟩

theorem correctness_goal_1
    (nums : Array ℤ)
    (k : ℕ)
    (out1 : Array ℤ)
    : (implementation.fillZero nums k out1).size = out1.size := by
  classical

  have h_fill_size : ∀ j (out : Array ℤ), (implementation.fillZero nums j out).size = out.size := by
    intro j out
    -- Induct on the termination measure `nums.size - j`.
    have aux : ∀ m j (out : Array ℤ), nums.size - j = m →
        (implementation.fillZero nums j out).size = out.size := by
      intro m
      induction m with
      | zero =>
          intro j out hj
          have hle : nums.size ≤ j := by
            exact (Nat.sub_eq_zero_iff_le).1 (by simpa [hj])
          have hnotlt : ¬ j < nums.size := Nat.not_lt_of_ge hle
          have hfill : implementation.fillZero nums j out = out := by
            conv_lhs => unfold implementation.fillZero
            rw [dif_neg hnotlt]
          simpa [hfill]
      | succ m ih =>
          intro j out hj
          by_cases hlt : j < nums.size
          ·
            have hj' : nums.size - (j + 1) = m := by
              calc
                nums.size - (j + 1) = Nat.pred (nums.size - j) := by
                  simpa [Nat.succ_eq_add_one] using (Nat.sub_succ nums.size j)
                _ = Nat.pred (m + 1) := by
                  simpa [hj]
                _ = m := by simp
            have ih' : (implementation.fillZero nums (j + 1) (out.set! j (0 : ℤ))).size =
                (out.set! j (0 : ℤ)).size := by
              simpa using ih (j := j + 1) (out := out.set! j (0 : ℤ)) hj'
            have hfill : implementation.fillZero nums j out =
                implementation.fillZero nums (j + 1) (out.set! j (0 : ℤ)) := by
              conv_lhs => unfold implementation.fillZero
              rw [dif_pos hlt]
            calc
              (implementation.fillZero nums j out).size
                  = (implementation.fillZero nums (j + 1) (out.set! j (0 : ℤ))).size := by
                      simpa [hfill]
              _ = (out.set! j (0 : ℤ)).size := ih'
              _ = out.size := by
                  simpa [Array.set!_eq_setIfInBounds] using
                    (Array.size_setIfInBounds (xs := out) (i := j) (a := (0 : ℤ)))
          ·
            have hfill : implementation.fillZero nums j out = out := by
              conv_lhs => unfold implementation.fillZero
              rw [dif_neg hlt]
            simpa [hfill]
    exact aux (nums.size - j) j out rfl

  simpa using h_fill_size k out1

theorem correctness_goal_2
    (nums : Array ℤ)
    (k : ℕ)
    (out1 : Array ℤ)
    : (implementation.fillZero nums k out1).extract 0 k = out1.extract 0 k := by
    classical

    -- Writing at an index `j ≥ k` does not change the prefix-extract `0..k`.
    have extract_set!_of_le :
        ∀ (out : Array ℤ) (j : Nat) (a : ℤ), k ≤ j →
          (out.set! j a).extract 0 k = out.extract 0 k := by
      intro out j a hkj
      apply Array.ext
      · simp [Array.size_extract, Array.set!_eq_setIfInBounds]
      · intro i hi1 hi2
        have hcondL : i < min k (out.set! j a).size := by
          simpa [Array.size_extract] using hi1
        have hcondR : i < min k out.size := by
          simpa [Array.size_extract] using hi2

        have hi_lt_k : i < k := lt_of_lt_of_le hcondR (Nat.min_le_left _ _)
        have hij : i < j := lt_of_lt_of_le hi_lt_k hkj
        have hne : j ≠ i := Nat.ne_of_gt hij

        have hopt : (out.set! j a)[i]? = out[i]? := by
          simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, hne]

        have hoptEx : ((out.set! j a).extract 0 k)[i]? = (out.extract 0 k)[i]? := by
          rw [Array.getElem?_extract, Array.getElem?_extract]
          simpa [hcondL, hcondR] using hopt

        have hsL :
            some (((out.set! j a).extract 0 k)[i]'hi1) = ((out.set! j a).extract 0 k)[i]? := by
          simpa using
            (Array.getElem?_eq_getElem (xs := (out.set! j a).extract 0 k) (i := i) hi1).symm
        have hsR :
            (out.extract 0 k)[i]? = some ((out.extract 0 k)[i]'hi2) := by
          simpa using
            (Array.getElem?_eq_getElem (xs := out.extract 0 k) (i := i) hi2)

        have : some (((out.set! j a).extract 0 k)[i]'hi1) = some ((out.extract 0 k)[i]'hi2) := by
          calc
            some (((out.set! j a).extract 0 k)[i]'hi1)
                = ((out.set! j a).extract 0 k)[i]? := hsL
            _ = (out.extract 0 k)[i]? := hoptEx
            _ = some ((out.extract 0 k)[i]'hi2) := by simpa [hsR]

        exact Option.some.inj this

    -- `fillZero` (starting at an index `j ≥ k`) preserves this prefix-extract.
    have fillZero_extract_of_le :
        ∀ (j : Nat) (out : Array ℤ), k ≤ j →
          (implementation.fillZero nums j out).extract 0 k = out.extract 0 k := by
      intro j out hkj

      have aux :
          ∀ m j out, k ≤ j → nums.size - j = m →
            (implementation.fillZero nums j out).extract 0 k = out.extract 0 k := by
        intro m
        induction m with
        | zero =>
            intro j out hkj hjm
            have hnj : nums.size ≤ j := Nat.sub_eq_zero_iff_le.mp hjm
            have hnot : ¬ j < nums.size := Nat.not_lt_of_ge hnj
            simp [implementation.fillZero, hnot]
        | succ m ih =>
            intro j out hkj hjm
            have hjlt : j < nums.size := by
              have : 0 < nums.size - j := by
                simpa [hjm] using Nat.succ_pos m
              exact Nat.sub_pos_iff_lt.mp this

            have hjm' : nums.size - (j + 1) = m := by
              simpa [Nat.sub_succ, hjm]

            have hkj' : k ≤ j + 1 := Nat.le_trans hkj (Nat.le_succ j)

            have hrec :
                (implementation.fillZero nums (j + 1) (out.set! j (0 : ℤ))).extract 0 k =
                  (out.set! j (0 : ℤ)).extract 0 k :=
              ih (j := j + 1) (out := out.set! j (0 : ℤ)) hkj' hjm'

            calc
              (implementation.fillZero nums j out).extract 0 k
                  = (implementation.fillZero nums (j + 1) (out.set! j (0 : ℤ))).extract 0 k := by
                      -- unfold only the LHS occurrence of `fillZero`
                      conv_lhs => unfold implementation.fillZero
                      simp [hjlt]
              _ = (out.set! j (0 : ℤ)).extract 0 k := hrec
              _ = out.extract 0 k := by
                      simpa using (extract_set!_of_le out j (0 : ℤ) hkj)

      exact aux (nums.size - j) j out hkj rfl

    simpa using (fillZero_extract_of_le k out1 (le_rfl))

theorem correctness_goal_3
    (nums : Array ℤ)
    (k : ℕ)
    (out1 : Array ℤ)
    (h_go : out1.size = nums.size ∧
  k ≤ nums.size ∧
    (∀ (i : ℕ), i + 1 < k → out1[i]! ≤ out1[i + 1]!) ∧
      ∀ (x : ℤ), Array.count x (out1.extract 0 k) = Nat.min 2 (Array.count x nums))
    (h_fill_size : (implementation.fillZero nums k out1).size = out1.size)
    (h_fill_extract : (implementation.fillZero nums k out1).extract 0 k = out1.extract 0 k)
    : (∀ (i : ℕ), i + 1 < k → out1[i]! ≤ out1[i + 1]!) →
  ∀ (i : ℕ), i + 1 < k → (implementation.fillZero nums k out1)[i]! ≤ (implementation.fillZero nums k out1)[i + 1]! := by
  intro h_sorted_out1 i hi
  rcases h_go with ⟨h_out1_size, hk_le_nums, _h_sorted, _h_count⟩
  have hkout1 : k ≤ out1.size := by
    simpa [h_out1_size] using hk_le_nums
  have hkfz : k ≤ (implementation.fillZero nums k out1).size := by
    simpa [h_fill_size] using hkout1

  have hi_lt : i < k := by
    exact Nat.lt_trans (Nat.lt_succ_self i) hi

  have hget_i : (implementation.fillZero nums k out1)[i]? = out1[i]? := by
    have h := congrArg (fun a => a[i]?) h_fill_extract
    -- Use `simp only` to avoid rewriting `xs[i]?` into `some xs[i]`.
    simpa only [Array.getElem?_extract, Nat.sub_zero, Nat.zero_add, Nat.min_eq_left hkfz,
      Nat.min_eq_left hkout1, hi_lt] using h

  have hget_i1 : (implementation.fillZero nums k out1)[i + 1]? = out1[i + 1]? := by
    have h := congrArg (fun a => a[i + 1]?) h_fill_extract
    simpa only [Array.getElem?_extract, Nat.sub_zero, Nat.zero_add, Nat.min_eq_left hkfz,
      Nat.min_eq_left hkout1, hi] using h

  have hbang_i : (implementation.fillZero nums k out1)[i]! = out1[i]! := by
    simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, hget_i]

  have hbang_i1 : (implementation.fillZero nums k out1)[i + 1]! = out1[i + 1]! := by
    simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, hget_i1]

  have hout := h_sorted_out1 i hi
  simpa [hbang_i, hbang_i1] using hout

theorem correctness_goal
    (nums : Array Int)
    (h_precond : precondition nums)
    : postcondition nums (implementation nums) := by
  classical
  -- unfold just enough to expose go and fillZero
  simp [postcondition, implementation, precondition, sortedPrefix, countInPrefix]
  -- Now we must prove the conjunction about the result of go and fillZero.
  -- Split the result of go.
  cases hgo_res : implementation.go nums 0 0 none 0 nums with
  | mk k out1 =>
    -- Core correctness of the first pass.
    have h_go : out1.size = nums.size ∧
        k ≤ nums.size ∧
        (∀ (i : Nat), i + 1 < k → out1[i]! ≤ out1[i + 1]!) ∧
        (∀ (x : Int), Array.count x (out1.extract 0 k) = Nat.min 2 (Array.count x nums)) := by
      expose_names; exact (correctness_goal_0 nums h_precond k out1 hgo_res)

    -- Size is preserved by fillZero.
    have h_fill_size : (implementation.fillZero nums k out1).size = out1.size := by
      expose_names; exact (correctness_goal_1 nums k out1)

    -- Prefix up to k is unchanged by fillZero.
    have h_fill_extract : (implementation.fillZero nums k out1).extract 0 k = out1.extract 0 k := by
      expose_names; exact (correctness_goal_2 nums k out1)

    -- Sortedness of the prefix is unchanged by fillZero.
    have h_fill_sorted : (∀ (i : Nat), i + 1 < k → out1[i]! ≤ out1[i + 1]!) →
        (∀ (i : Nat), i + 1 < k → (implementation.fillZero nums k out1)[i]! ≤ (implementation.fillZero nums k out1)[i + 1]!) := by
      expose_names; exact (correctness_goal_3 nums k out1 h_go h_fill_size h_fill_extract)

    -- Assemble the goal.
    rcases h_go with ⟨h_size1, h_k_le, h_sorted1, h_count1⟩
    refine And.intro ?_ (And.intro ?_ (And.intro ?_ ?_))
    · -- size
      simpa [h_fill_size, h_size1]
    · -- k ≤ size
      simpa [h_k_le]
    · -- sortedPrefix
      exact h_fill_sorted h_sorted1
    · -- count
      intro x
      simpa [h_fill_extract] using h_count1 x
end Proof
