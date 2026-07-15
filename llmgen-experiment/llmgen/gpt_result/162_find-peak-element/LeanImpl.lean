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
    162. Find Peak Element: return an index of any peak element in a 0-indexed integer array.
    **Important: complexity should be O(log n) time and O(1) space**
    Natural language breakdown:
    1. Input is a 0-indexed array `nums` of integers.
    2. An index `i` is a peak if `nums[i]` is strictly greater than its neighbors.
    3. Out-of-range neighbors are treated as negative infinity, so an endpoint only needs to be strictly greater than its single in-range neighbor.
    4. The function returns the index of any peak; if multiple peaks exist, any one is acceptable.
    5. To ensure a strict peak exists, adjacent elements are assumed to be different.
    6. The returned index must be a valid index into the array.
-/

-- `IsPeakIndex nums i` means `i` is in range and strictly greater than each existing in-range neighbor.
-- The sentinel neighbors (-∞) are modeled by making the comparison obligations only when the neighbor exists.
def IsPeakIndex (nums : Array Int) (i : Nat) : Prop :=
  i < nums.size ∧
  (0 < i → nums[i]! > nums[i - 1]!) ∧
  (i + 1 < nums.size → nums[i]! > nums[i + 1]!)

-- Preconditions:
-- 1) array is nonempty so an index can be returned
-- 2) adjacent elements are distinct (standard problem constraint), ensuring existence of a strict peak
-- Note: we keep this decidable/first-order with bounded indexing.
def precondition (nums : Array Int) : Prop :=
  nums.size > 0 ∧
  (∀ i : Nat, i + 1 < nums.size → nums[i]! ≠ nums[i + 1]!)

def postcondition (nums : Array Int) (result : Nat) : Prop :=
  IsPeakIndex nums result
end Specs

section Impl
def implementation (nums : Array Int) : Nat :=
  let n := nums.size
  if h0 : n = 0 then
    0
  else
    -- Binary search on the slope: if nums[mid] < nums[mid+1], a peak exists to the right; else to the left (incl. mid).
    let rec go (lo hi : Nat) : Nat :=
      if h : lo < hi then
        let mid := lo + (hi - lo) / 2
        -- Here mid < hi, so mid+1 ≤ hi and thus mid+1 < n (since hi < n is maintained).
        let a := nums[mid]!
        let b := nums[mid + 1]!
        if a < b then
          go (mid + 1) hi
        else
          go lo mid
      else
        lo
    -- Invariant: search within [0, n-1]
    go 0 (n - 1)
termination_by
  nums.size
end Impl

section TestCases
-- Test case 1: Example 1
-- nums = [1,2,3,1] has a peak at index 2 (value 3)
def test1_nums : Array Int := #[1, 2, 3, 1]
def test1_Expected : Nat := 2

-- Test case 2: Example 2 (one valid peak is at index 5 with value 6)
def test2_nums : Array Int := #[1, 2, 1, 3, 5, 6, 4]
def test2_Expected : Nat := 5

-- Test case 3: Single element (always a peak)
def test3_nums : Array Int := #[7]
def test3_Expected : Nat := 0

-- Test case 4: Strictly increasing (peak at last index)
def test4_nums : Array Int := #[1, 2, 3, 4]
def test4_Expected : Nat := 3

-- Test case 5: Strictly decreasing (peak at index 0)
def test5_nums : Array Int := #[4, 3, 2, 1]
def test5_Expected : Nat := 0

-- Test case 6: Two elements increasing (peak at index 1)
def test6_nums : Array Int := #[1, 2]
def test6_Expected : Nat := 1

-- Test case 7: Two elements decreasing (peak at index 0)
def test7_nums : Array Int := #[2, 1]
def test7_Expected : Nat := 0

-- Test case 8: Peak in the middle
-- [1,3,2] has a peak at index 1

def test8_nums : Array Int := #[1, 3, 2]
def test8_Expected : Nat := 1

-- Test case 9: Includes negative values; peak at index 3 (value 0)
-- [-3,-2,-4,0,-1] has peak 0 at index 3

def test9_nums : Array Int := #[-3, -2, -4, 0, -1]
def test9_Expected : Nat := 3
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
  return (result : Nat)
  require precondition nums
  ensures postcondition nums result
  do
  return (implementation nums)

velvet_plausible_test implementationPbt (config := { maxMs := some 20000 })
end Pbt

section Proof
theorem correctness_goal_0_0
    (nums : Array ℤ)
    (hadj : ∀ (i : ℕ), i + 1 < nums.size → nums[i]! ≠ nums[i + 1]!)
    : ∀ (lo hi : ℕ),
  lo ≤ hi →
    hi < nums.size →
      lo = 0 ∨ nums[lo]! > nums[lo - 1]! →
        hi + 1 = nums.size ∨ nums[hi]! > nums[hi + 1]! → IsPeakIndex nums (implementation.go nums lo hi) := by
  classical
  -- prove by strong induction on the interval length `hi - lo`
  have main : ∀ m : Nat,
      ∀ lo hi : Nat,
        lo ≤ hi →
        hi < nums.size →
        (lo = 0 ∨ nums[lo]! > nums[lo - 1]!) →
        (hi + 1 = nums.size ∨ nums[hi]! > nums[hi + 1]!) →
        hi - lo = m →
        IsPeakIndex nums (implementation.go nums lo hi) := by
    intro m
    refine Nat.strong_induction_on m ?_
    intro m ih lo hi hlole hhi hloB hhiB hlen
    by_cases hlt : lo < hi
    · -- recursive step
      set mid : Nat := lo + (hi - lo) / 2 with hmid
      have hsub_pos : 0 < hi - lo := Nat.sub_pos_of_lt hlt
      have hdiv_lt : (hi - lo) / 2 < (hi - lo) :=
        Nat.div_lt_self hsub_pos (by decide : 1 < (2 : Nat))
      have hmid_lt_hi : mid < hi := by
        have : lo + (hi - lo) / 2 < lo + (hi - lo) := Nat.add_lt_add_left hdiv_lt lo
        -- rewrite `lo + (hi - lo)` to `hi`
        simpa [hmid, Nat.add_sub_of_le hlole] using this
      have hmid_lt_size : mid < nums.size := lt_trans hmid_lt_hi hhi
      have hmid1_le_hi : mid + 1 ≤ hi := Nat.succ_le_of_lt hmid_lt_hi
      have hmid1_lt_size : mid + 1 < nums.size := lt_of_le_of_lt hmid1_le_hi hhi

      by_cases hcmp : nums[mid]! < nums[mid + 1]!
      · -- go right
        have hlo'B : (mid + 1 = 0 ∨ nums[mid + 1]! > nums[(mid + 1) - 1]!) := by
          right
          simp
          change nums[mid]! < nums[mid + 1]!
          simpa using hcmp
        have hk : hi - (mid + 1) < m := by
          have hlo_le_mid : lo ≤ mid := by
            -- `lo ≤ lo + x`
            have : lo ≤ lo + (hi - lo) / 2 := Nat.le_add_right lo ((hi - lo) / 2)
            simpa [hmid] using this
          have hlo_lt_mid1 : lo < mid + 1 := Nat.lt_succ_of_le hlo_le_mid
          have hk' : hi - (mid + 1) < hi - lo :=
            Nat.sub_lt_sub_left (k := lo) (m := hi) (n := mid + 1) hlt hlo_lt_mid1
          simpa [hlen] using hk'
        have hrec : IsPeakIndex nums (implementation.go nums (mid + 1) hi) :=
          ih (hi - (mid + 1)) hk (mid + 1) hi hmid1_le_hi hhi hlo'B hhiB rfl

        -- simplify the goal to the recursive call (without unfolding that recursive call)
        have hcmp' : nums[lo + (hi - lo) / 2]! < nums[lo + (hi - lo) / 2 + 1]! := by
          -- rewrite `mid` back to the expression
          simpa [hmid, Nat.add_assoc] using hcmp
        -- unfold one layer of `go` and select the branch
        simp (singlePass := true) [implementation.go]
        simp [hlt]
        simp [hcmp']
        -- rewrite the syntactic mid-expression back to our `mid`
        simp [hmid.symm, Nat.add_assoc]
        exact hrec
      · -- go left
        have hne : nums[mid]! ≠ nums[mid + 1]! := hadj mid hmid1_lt_size
        have hgt : nums[mid]! > nums[mid + 1]! := by
          have hdisj : nums[mid]! < nums[mid + 1]! ∨ nums[mid]! > nums[mid + 1]! := lt_or_gt_of_ne hne
          cases hdisj with
          | inl hlt' => exact (False.elim (hcmp hlt'))
          | inr hgt' => exact hgt'
        have hhi'B : (mid + 1 = nums.size ∨ nums[mid]! > nums[mid + 1]!) := Or.inr hgt
        have hk : mid - lo < m := by
          have hlo_le_mid : lo ≤ mid := by
            have : lo ≤ lo + (hi - lo) / 2 := Nat.le_add_right lo ((hi - lo) / 2)
            simpa [hmid] using this
          have hk' : mid - lo < hi - lo :=
            Nat.sub_lt_sub_right (c := lo) (a := mid) (b := hi) hlo_le_mid hmid_lt_hi
          simpa [hlen] using hk'
        have hrec : IsPeakIndex nums (implementation.go nums lo mid) :=
          ih (mid - lo) hk lo mid (by
            have : lo ≤ lo + (hi - lo) / 2 := Nat.le_add_right lo ((hi - lo) / 2)
            simpa [hmid] using this) hmid_lt_size hloB hhi'B rfl

        have hcmp' : ¬ nums[lo + (hi - lo) / 2]! < nums[lo + (hi - lo) / 2 + 1]! := by
          simpa [hmid, Nat.add_assoc] using hcmp
        simp (singlePass := true) [implementation.go]
        simp [hlt]
        simp [hcmp']
        simp [hmid.symm, Nat.add_assoc]
        exact hrec
    · -- base case: `lo ≥ hi`, together with `lo ≤ hi` gives `lo = hi`, and `go` returns `lo`
      have hhi_le_lo : hi ≤ lo := Nat.le_of_not_gt (by simpa using hlt)
      have hEq : lo = hi := Nat.le_antisymm hlole hhi_le_lo
      have hret : implementation.go nums lo hi = lo := by
        simp [implementation.go, hlt]
      simpa [hret] using (show IsPeakIndex nums lo from by
        refine And.intro (by simpa [hEq] using hhi) ?_
        refine And.intro ?_ ?_
        · intro hlo_pos
          have hlo_ne : lo ≠ 0 := Nat.ne_of_gt hlo_pos
          cases hloB with
          | inl h0 => exact (False.elim (hlo_ne h0))
          | inr hgt => exact hgt
        · intro hlo1_lt
          cases hhiB with
          | inl hlast =>
              exact False.elim ((Nat.ne_of_lt hlo1_lt) (by simpa [hEq] using hlast))
          | inr hgt =>
              simpa [hEq] using hgt)
  intro lo hi hlole hhi hloB hhiB
  exact main (hi - lo) lo hi hlole hhi hloB hhiB rfl

theorem correctness_goal_0
    (nums : Array ℤ)
    (h_precond : precondition nums)
    : IsPeakIndex nums (implementation.go nums 0 (nums.size - 1)) := by
  classical
  rcases h_precond with ⟨hsize_pos, hadj⟩

  have hlast_lt : nums.size - 1 < nums.size := by
    expose_names; intros; expose_names; try simp_all; try grind

  have go_correct :
      ∀ lo hi : Nat,
        lo ≤ hi → hi < nums.size →
        (lo = 0 ∨ nums[lo]! > nums[lo - 1]!) →
        (hi + 1 = nums.size ∨ nums[hi]! > nums[hi + 1]!) →
        IsPeakIndex nums (implementation.go nums lo hi) := by
    expose_names; exact (correctness_goal_0_0 nums hadj)

  -- right boundary is sentinel at index n
  have hright0 : (nums.size - 1) + 1 = nums.size := by
    expose_names; intros; expose_names; try simp_all; try grind

  simpa using
    go_correct 0 (nums.size - 1) (Nat.zero_le _) hlast_lt (Or.inl rfl) (Or.inl hright0)

theorem correctness_goal
    (nums : Array Int)
    (h_precond : precondition nums)
    : postcondition nums (implementation nums) := by
  classical
  unfold postcondition
  have hnpos : nums.size > 0 := h_precond.1
  have hn0 : nums.size ≠ 0 := Nat.ne_of_gt hnpos
  -- reduce to the nonempty branch of the implementation
  have h_go : IsPeakIndex nums (implementation.go nums 0 (nums.size - 1)) := by
    expose_names; exact (correctness_goal_0 nums h_precond)
  -- finish by rewriting `implementation`
  simpa [implementation, hn0] using h_go
end Proof
