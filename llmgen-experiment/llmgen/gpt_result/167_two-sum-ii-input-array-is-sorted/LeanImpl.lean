import Lean
import Mathlib.Tactic
import Velvet.Std

set_option maxHeartbeats 10000000

section Specs
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false

/- Problem Description
    TwoSumIISorted: Given a 1-indexed sorted array of integers, return the (1-indexed) positions of
    the unique pair of distinct elements whose sum equals a target.
    Natural language breakdown:
    1. Input is an array `numbers : Array Int` sorted in non-decreasing order.
    2. We are given an integer `target : Int`.
    3. There exist indices i and j with 0 ≤ i < j < numbers.size such that numbers[i] + numbers[j] = target.
    4. The problem guarantees this pair is unique (exactly one solution).
    5. Output is an array of length 2 containing the 1-based indices: [i+1, j+1].
    6. The two indices must be strictly increasing and within 1..numbers.size.
    7. We must not use the same element twice (captured by i < j).
    Your algorithm should run in **O(n)** time and **O(1)** extra space.
-/

-- Helper: non-decreasing order on an Int array.
-- We use the standard relational characterization of sortedness by indices.
def isSortedNondecreasing (numbers : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < numbers.size → numbers[i]! ≤ numbers[j]!

-- Helper: a valid 0-based pair (i,j) witnessing the target sum.
def isWitnessPair (numbers : Array Int) (target : Int) (i : Nat) (j : Nat) : Prop :=
  i < j ∧ j < numbers.size ∧ numbers[i]! + numbers[j]! = target

-- Helper: uniqueness of the witness pair, expressed over 0-based indices.
def hasUniqueWitnessPair (numbers : Array Int) (target : Int) : Prop :=
  (∃ (i : Nat) (j : Nat), isWitnessPair numbers target i j) ∧
  (∀ (i₁ : Nat) (j₁ : Nat) (i₂ : Nat) (j₂ : Nat),
    isWitnessPair numbers target i₁ j₁ → isWitnessPair numbers target i₂ j₂ → i₁ = i₂ ∧ j₁ = j₂)

-- Helper: output shape/validity and correspondence to a witness pair.
def outputMatchesUniquePair (numbers : Array Int) (target : Int) (result : Array Nat) : Prop :=
  result.size = 2 ∧
  (1 ≤ result[0]!) ∧ (result[0]! < result[1]!) ∧ (result[1]! ≤ numbers.size) ∧
  (numbers[(result[0]! - 1)]! + numbers[(result[1]! - 1)]! = target) ∧
  (∀ (i : Nat) (j : Nat), isWitnessPair numbers target i j →
    result[0]! = i + 1 ∧ result[1]! = j + 1)

-- Preconditions
-- We keep them simple and decidable-ish (arith + array bounds), and capture the problem guarantees.
def precondition (numbers : Array Int) (target : Int) : Prop :=
  numbers.size ≥ 2 ∧
  isSortedNondecreasing numbers ∧
  hasUniqueWitnessPair numbers target

-- Postconditions
-- Ensure the result is exactly the 1-based indices of the unique witness pair.
def postcondition (numbers : Array Int) (target : Int) (result : Array Nat) : Prop :=
  outputMatchesUniquePair numbers target result
end Specs

section Impl
def implementation (numbers : Array Int) (target : Int) : Array Nat :=
  let rec go (l r : Nat) : Array Nat :=
    if h : l < r then
      let s : Int := numbers[l]! + numbers[r]!
      if s = target then
        #[l + 1, r + 1]
      else if s < target then
        go (l + 1) r
      else
        go l (r - 1)
    else
      -- Unreachable under the precondition (unique witness pair exists).
      #[1, 1]
  if hsz : numbers.size = 0 then
    #[1, 1]
  else
    go 0 (numbers.size - 1)
end Impl

section TestCases
-- Test case 1: Example 1
-- numbers = [2,7,11,15], target = 9 => [1,2]
def test1_numbers : Array Int := #[2, 7, 11, 15]
def test1_target : Int := 9
def test1_Expected : Array Nat := #[1, 2]

-- Test case 2: Example 2
-- numbers = [2,3,4], target = 6 => [1,3]
def test2_numbers : Array Int := #[2, 3, 4]
def test2_target : Int := 6
def test2_Expected : Array Nat := #[1, 3]

-- Test case 3: Example 3 (includes negative)
-- numbers = [-1,0], target = -1 => [1,2]
def test3_numbers : Array Int := #[-1, 0]
def test3_target : Int := -1
def test3_Expected : Array Nat := #[1, 2]

-- Test case 4: Contains duplicates, unique solution uses equal values
-- numbers = [1,1,3,4], target = 2 => [1,2]
def test4_numbers : Array Int := #[1, 1, 3, 4]
def test4_target : Int := 2
def test4_Expected : Array Nat := #[1, 2]

-- Test case 5: Duplicates but solution uses farthest pair
-- numbers = [0,0,3,4], target = 4 => [1,4]
def test5_numbers : Array Int := #[0, 0, 3, 4]
def test5_target : Int := 4
def test5_Expected : Array Nat := #[1, 4]

-- Test case 6: All negative, minimal size 2
-- numbers = [-5,-2], target = -7 => [1,2]
def test6_numbers : Array Int := #[-5, -2]
def test6_target : Int := -7
def test6_Expected : Array Nat := #[1, 2]

-- Test case 7: Larger array, solution in the middle
-- numbers = [-10,-3,0,5,9,12], target = 6 => [-3 + 9]
-- indices 2 and 5 (1-based)
def test7_numbers : Array Int := #[-10, -3, 0, 5, 9, 12]
def test7_target : Int := 6
def test7_Expected : Array Nat := #[2, 5]

-- Test case 8: Boundary-ish: uses first and last elements
-- numbers = [1,2,3,4,10], target = 11 => [1,5]
def test8_numbers : Array Int := #[1, 2, 3, 4, 10]
def test8_target : Int := 11
def test8_Expected : Array Nat := #[1, 5]

-- Test case 9: Includes many equal elements, unique solution still exists
-- numbers = [2,2,2,2,9], target = 11 => [1,5]
def test9_numbers : Array Int := #[2, 2, 2, 2, 9]
def test9_target : Int := 11
def test9_Expected : Array Nat := #[1, 5]
end TestCases

section Assertions
-- Test case 1
#assert_same_evaluation #[(implementation test1_numbers test1_target), test1_Expected]

-- Test case 2
#assert_same_evaluation #[(implementation test2_numbers test2_target), test2_Expected]

-- Test case 3
#assert_same_evaluation #[(implementation test3_numbers test3_target), test3_Expected]

-- Test case 4
#assert_same_evaluation #[(implementation test4_numbers test4_target), test4_Expected]

-- Test case 5
#assert_same_evaluation #[(implementation test5_numbers test5_target), test5_Expected]

-- Test case 6
#assert_same_evaluation #[(implementation test6_numbers test6_target), test6_Expected]

-- Test case 7
#assert_same_evaluation #[(implementation test7_numbers test7_target), test7_Expected]

-- Test case 8
#assert_same_evaluation #[(implementation test8_numbers test8_target), test8_Expected]

-- Test case 9
#assert_same_evaluation #[(implementation test9_numbers test9_target), test9_Expected]
end Assertions

section Proof
theorem correctness_goal
    (numbers : Array Int)
    (target : Int)
    (h_precond : precondition numbers target)
    : postcondition numbers target (implementation numbers target) := by
  classical
  -- Unpack precondition
  rcases h_precond with ⟨hsz2, hsorted, hexuniq⟩
  rcases hexuniq with ⟨hex, huniq⟩
  rcases hex with ⟨iw, jw, hwit⟩
  rcases hwit with ⟨hij, hjlt, hsum⟩

  have hi_lt : iw < numbers.size := Nat.lt_trans hij hjlt

  have hszpos : 0 < numbers.size :=
    lt_of_lt_of_le (by decide : (0 : Nat) < 2) hsz2
  have hszne0 : numbers.size ≠ 0 := Nat.ne_of_gt hszpos

  -- Strong correctness lemma for `implementation.go`.
  -- Measure: distance from the unique witness bounds.
  have goCorrectAux :
      ∀ m : Nat,
        (∀ l r : Nat,
          (iw - l) + (r - jw) = m →
          r < numbers.size → l ≤ iw → jw ≤ r →
            implementation.go numbers target l r = #[iw + 1, jw + 1]) := by
    intro m
    refine Nat.strongRecOn m ?_
    intro m ih l r hmeas hrsize hl hj

    have hlr : l < r :=
      Nat.lt_of_le_of_lt hl (Nat.lt_of_lt_of_le hij hj)

    -- Unfold one step of the recursion (the `else` branch is impossible because `l < r`).
    unfold implementation.go
    simp [hlr]

    -- Case split on the sum comparison
    by_cases hst : numbers[l]! + numbers[r]! = target
    · -- Found a witness; uniqueness forces (l,r) = (iw,jw)
      have hpair : isWitnessPair numbers target l r := ⟨hlr, hrsize, hst⟩
      rcases huniq l r iw jw hpair ⟨hij, hjlt, hsum⟩ with ⟨hlEq, hrEq⟩
      cases hlEq; cases hrEq
      simp [hsum]
    · by_cases hslt : numbers[l]! + numbers[r]! < target
      · -- s < target: must have l < iw
        have hl_ne : l ≠ iw := by
          intro hliw
          have hliw' : l = iw := hliw
          -- show target ≤ numbers[iw]! + numbers[r]! using jw ≤ r
          have h_jw_le_r : numbers[jw]! ≤ numbers[r]! := by
            rcases lt_or_eq_of_le hj with hjr | hjr
            · exact hsorted jw r hjr hrsize
            · simpa [hjr]
          have h1 : numbers[iw]! ≤ numbers[iw]! := le_rfl
          have hsum_le : numbers[iw]! + numbers[jw]! ≤ numbers[iw]! + numbers[r]! :=
            Int.add_le_add h1 h_jw_le_r
          have hle : target ≤ numbers[iw]! + numbers[r]! := by
            simpa [hsum] using hsum_le
          have : target ≤ numbers[l]! + numbers[r]! := by
            simpa [hliw'] using hle
          exact (not_lt_of_ge this) hslt

        have hl_lt_iw : l < iw := Nat.lt_of_le_of_ne hl hl_ne
        have hl' : l + 1 ≤ iw := Nat.succ_le_of_lt hl_lt_iw

        -- measure decreases
        have hmeas_lt : (iw - (l + 1)) + (r - jw) < m := by
          rcases Nat.exists_eq_add_of_le hl' with ⟨k, hk⟩
          have hsub1 : iw - (l + 1) = k := by
            simpa [hk, Nat.add_assoc] using (Nat.add_sub_cancel_left (l + 1) k)
          have hk' : iw = l + (k + 1) := by
            simpa [hk, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
          have hsub2 : iw - l = k + 1 := by
            simpa [hk', Nat.add_assoc] using (Nat.add_sub_cancel_left l (k + 1))
          have hmstep : (iw - (l + 1)) + (r - jw) + 1 = (iw - l) + (r - jw) := by
            simp [hsub1, hsub2, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
          have : (iw - (l + 1)) + (r - jw) < (iw - (l + 1)) + (r - jw) + 1 :=
            Nat.lt_succ_self _
          simpa [hmstep, hmeas] using this

        have hrec :
            implementation.go numbers target (l + 1) r = #[iw + 1, jw + 1] :=
          ih ((iw - (l + 1)) + (r - jw)) hmeas_lt (l + 1) r rfl hrsize hl' hj

        simp [hst, hslt, hrec]
      · -- s > target: must have jw < r
        have hsle : target ≤ numbers[l]! + numbers[r]! := le_of_not_gt hslt
        have hsgt : target < numbers[l]! + numbers[r]! :=
          lt_of_le_of_ne hsle (Ne.symm hst)

        have hr_ne : r ≠ jw := by
          intro hrjw
          have hrjw' : r = jw := hrjw
          -- show numbers[l]! + numbers[jw]! ≤ target using l ≤ iw
          have h_l_le_iw : numbers[l]! ≤ numbers[iw]! := by
            rcases lt_or_eq_of_le hl with hliw | hliw
            · exact hsorted l iw hliw hi_lt
            · simpa [hliw]
          have h2 : numbers[jw]! ≤ numbers[jw]! := le_rfl
          have hsum_le : numbers[l]! + numbers[jw]! ≤ numbers[iw]! + numbers[jw]! :=
            Int.add_le_add h_l_le_iw h2
          have hle : numbers[l]! + numbers[jw]! ≤ target := by
            simpa [hsum] using hsum_le
          have : numbers[l]! + numbers[r]! ≤ target := by
            simpa [hrjw'] using hle
          exact (not_lt_of_ge this) hsgt

        have hj_lt_r : jw < r := Nat.lt_of_le_of_ne hj (Ne.symm hr_ne)
        have hj' : jw ≤ r - 1 := by
          simpa using (LT.lt.le_pred hj_lt_r)
        have hrsize' : r - 1 < numbers.size :=
          Nat.lt_of_le_of_lt (Nat.sub_le r 1) hrsize

        have hmeas_lt : (iw - l) + ((r - 1) - jw) < m := by
          have hle : jw + 1 ≤ r := Nat.succ_le_of_lt hj_lt_r
          rcases Nat.exists_eq_add_of_le hle with ⟨k, hk⟩
          have hk' : r = jw + (k + 1) := by
            simpa [hk, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
          have hsub1 : r - jw = k + 1 := by
            simpa [hk', Nat.add_assoc] using (Nat.add_sub_cancel_left jw (k + 1))
          have hsub2 : (r - 1) - jw = k := by
            simp [hk, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
          have hmstep : (iw - l) + ((r - 1) - jw) + 1 = (iw - l) + (r - jw) := by
            simp [hsub1, hsub2, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
          have : (iw - l) + ((r - 1) - jw) < (iw - l) + ((r - 1) - jw) + 1 :=
            Nat.lt_succ_self _
          simpa [hmstep, hmeas] using this

        have hrec :
            implementation.go numbers target l (r - 1) = #[iw + 1, jw + 1] :=
          ih ((iw - l) + ((r - 1) - jw)) hmeas_lt l (r - 1) rfl hrsize' hl hj'

        simp [hst, hslt, hrec]

  have goCorrect :
      ∀ l r : Nat,
        r < numbers.size → l ≤ iw → jw ≤ r →
          implementation.go numbers target l r = #[iw + 1, jw + 1] := by
    intro l r hrsize hl hj
    simpa using (goCorrectAux ((iw - l) + (r - jw)) l r rfl hrsize hl hj)

  -- reduce `implementation` to the initial `go` call
  have himpl : implementation numbers target = implementation.go numbers target 0 (numbers.size - 1) := by
    simp [implementation, hszne0]

  have hr0 : numbers.size - 1 < numbers.size := by
    have := Nat.pred_lt_self (a := numbers.size) hszpos
    simpa [Nat.pred_eq_sub_one] using this

  have hj_le_r0 : jw ≤ numbers.size - 1 := by
    have : jw ≤ Nat.pred numbers.size := (LT.lt.le_pred hjlt)
    simpa [Nat.pred_eq_sub_one] using this

  have hres : implementation numbers target = #[iw + 1, jw + 1] := by
    have hgo0 :
        implementation.go numbers target 0 (numbers.size - 1) = #[iw + 1, jw + 1] :=
      goCorrect 0 (numbers.size - 1) hr0 (Nat.zero_le _) hj_le_r0
    simpa [himpl] using hgo0

  -- Prove the postcondition
  have : outputMatchesUniquePair numbers target #[iw + 1, jw + 1] := by
    unfold outputMatchesUniquePair
    refine ⟨by simp, ?_⟩
    refine ⟨?_, ?_⟩
    · simpa using (Nat.succ_le_succ (Nat.zero_le iw))
    refine ⟨?_, ?_⟩
    · simpa using Nat.succ_lt_succ hij
    refine ⟨?_, ?_⟩
    · exact Nat.succ_le_of_lt hjlt
    refine ⟨?_, ?_⟩
    · simp [hsum]
    · intro i j hijw
      rcases huniq i j iw jw hijw ⟨hij, hjlt, hsum⟩ with ⟨hiEq, hjEq⟩
      subst hiEq; subst hjEq
      simp

  unfold postcondition
  simpa [hres] using this
end Proof
