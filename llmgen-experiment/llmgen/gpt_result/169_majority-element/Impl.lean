import Velvet.Std
import Extensions.Tactics
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false
set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

/- Problem Description
    169. Majority Element: Return the array element that appears strictly more than ⌊n/2⌋ times.
    **Important: complexity should be O(n) time and O(1) space**
    Natural language breakdown:
    1. Input is an array `nums` of length `n`.
    2. For a value `x`, its frequency is the number of indices whose element equals `x`.
    3. A value `x` is a majority element if its frequency is strictly greater than ⌊n/2⌋.
    4. The problem guarantees that at least one majority element exists.
    5. The output must be a value that is a majority element of `nums`.
    6. Such a majority element is unique: if any value has frequency > ⌊n/2⌋, it must equal the output.
-/

section Specs
-- Helper: the majority threshold (⌊n/2⌋).
-- Using Nat division, since Array.size and Array.count are Nat.
def majorityThreshold (n : Nat) : Nat :=
  n / 2

-- Helper predicate: `x` is a majority element of `nums`.
def isMajority (nums : Array Int) (x : Int) : Prop :=
  nums.count x > majorityThreshold nums.size

-- Preconditions
-- The problem states a majority element always exists.
def precondition (nums : Array Int) : Prop :=
  ∃ x : Int, isMajority nums x

-- Postconditions
-- The returned value is the unique majority element.
def postcondition (nums : Array Int) (result : Int) : Prop :=
  isMajority nums result ∧
  (∀ y : Int, isMajority nums y → y = result)
end Specs

section Impl
method MajorityElement (nums : Array Int)
  return (result : Int)
  require precondition nums
  ensures postcondition nums result
  do
  let mut i : Nat := 0
  let mut candidate : Int := 0
  let mut count : Int := 0

  -- Boyer–Moore majority vote (O(n) time, O(1) extra space).
  while i < nums.size
    invariant "inv_i_bounds" (i ≤ nums.size)
    invariant "inv_bm_accounting"
      (∃ (cN p : Nat),
        count = Int.ofNat cN ∧
        i = 2 * p + cN ∧
        (∀ v : Int, (nums.extract 0 i).count v ≤ p + (if v = candidate then cN else 0)))
    decreasing nums.size - i
  do
    let x := nums[i]!
    if count = 0 then
      candidate := x
      count := 1
    else
      if x = candidate then
        count := count + 1
      else
        count := count - 1
    i := i + 1

  -- The precondition guarantees a true majority exists, so the candidate is the majority.
  return candidate
end Impl

section TestCases
-- Test case 1: Example 1
-- Input: [3,2,3] -> majority is 3
-- counts: 3 appears 2 times, n=3, ⌊n/2⌋=1

def test1_nums : Array Int := #[3, 2, 3]

def test1_Expected : Int := 3

-- Test case 2: Example 2
-- Input: [2,2,1,1,1,2,2] -> majority is 2

def test2_nums : Array Int := #[2, 2, 1, 1, 1, 2, 2]

def test2_Expected : Int := 2

-- Test case 3: Single element (smallest valid n)

def test3_nums : Array Int := #[5]

def test3_Expected : Int := 5

-- Test case 4: Two elements, both same

def test4_nums : Array Int := #[7, 7]

def test4_Expected : Int := 7

-- Test case 5: Majority is 0, includes 0 boundary value

def test5_nums : Array Int := #[0, 1, 0]

def test5_Expected : Int := 0

-- Test case 6: Majority is negative number

def test6_nums : Array Int := #[-1, -1, 2]

def test6_Expected : Int := -1

-- Test case 7: Larger odd length, clear majority

def test7_nums : Array Int := #[9, 9, 9, 1, 2]

def test7_Expected : Int := 9

-- Test case 8: Larger even length, majority just above n/2
-- n=6, threshold=3, so majority count must be >=4

def test8_nums : Array Int := #[1, 2, 2, 2, 2, 3]

def test8_Expected : Int := 2

-- Test case 9: Majority appears many times, other values mixed

def test9_nums : Array Int := #[4, 4, 4, 4, 4, 2, 3, 4, 1]

def test9_Expected : Int := 4
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((MajorityElement test1_nums).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((MajorityElement test2_nums).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((MajorityElement test3_nums).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((MajorityElement test4_nums).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((MajorityElement test5_nums).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((MajorityElement test6_nums).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((MajorityElement test7_nums).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((MajorityElement test8_nums).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((MajorityElement test9_nums).run), DivM.res test9_Expected ]
end Assertions

section Pbt
-- Decidable instance synthesis failed for this method's conditions. Giving up on PBT.

-- velvet_plausible_test MajorityElement (config := { maxMs := some 5000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000

theorem goal_0
    (nums : Array ℤ)
    (candidate : ℤ)
    (i : ℕ)
    (invariant_inv_i_bounds : i ≤ nums.size)
    (if_pos : i < nums.size)
    (invariant_inv_bm_accounting : ∃ cN, (OfNat.ofNat 0 : ℤ) = cN.cast ∧ ∃ x, i = OfNat.ofNat 2 * x + cN ∧ ∀ (v : ℤ), Array.count v (nums.extract (OfNat.ofNat 0) i) ≤ x + if v = candidate then cN else OfNat.ofNat 0)
    : ∃ cN, (OfNat.ofNat 1 : ℤ) = cN.cast ∧ ∃ x, i + OfNat.ofNat 1 = OfNat.ofNat 2 * x + cN ∧ ∀ (v : ℤ), Array.count v (nums.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) ≤ x + if v = nums[i]! then cN else OfNat.ofNat 0 := by
  rcases invariant_inv_bm_accounting with ⟨cN0, hcN0, x, hi, hcnt⟩

  have hcN0' : cN0 = 0 := by exact_mod_cast hcN0.symm
  subst hcN0'

  have hi' : i = 2 * x := by
    simpa using hi

  have hcnt' : ∀ v : ℤ, Array.count v (nums.extract 0 i) ≤ x := by
    intro v
    simpa using hcnt v

  refine ⟨1, by simp, ⟨x, ?_, ?_⟩⟩

  · -- index accounting
    simpa [hi']

  · intro v

    have loop_snoc :
        ∀ (n start : Nat) (ys : Array ℤ),
          start + n < nums.size →
            Array.extract.loop nums (n + 1) start ys =
              (Array.extract.loop nums n start ys).push (nums[start + n]!) := by
      intro n
      induction n with
      | zero =>
          intro start ys hlt
          have hstart : start < nums.size := by simpa using hlt
          simpa [Nat.add_zero, Array.extract.loop, Array.get!, hstart] using
            (Array.extract_loop_succ (xs := nums) (ys := ys) (size := 0) (start := start) hstart)
      | succ n ih =>
          intro start ys hlt
          have hstart : start < nums.size := by
            have : start ≤ start + Nat.succ n := Nat.le_add_right start (Nat.succ n)
            exact lt_of_le_of_lt this hlt
          have hlt' : start + 1 + n < nums.size := by
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hlt

          have h₁ :
              Array.extract.loop nums (n + 2) start ys =
                Array.extract.loop nums (n + 1) (start + 1) (ys.push (nums[start])) := by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              (Array.extract_loop_succ (xs := nums) (ys := ys) (size := n + 1) (start := start) hstart)

          have h₂ :
              Array.extract.loop nums (n + 1) start ys =
                Array.extract.loop nums n (start + 1) (ys.push (nums[start])) := by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              (Array.extract_loop_succ (xs := nums) (ys := ys) (size := n) (start := start) hstart)

          have h₃ :
              Array.extract.loop nums (n + 1) (start + 1) (ys.push (nums[start])) =
                (Array.extract.loop nums n (start + 1) (ys.push (nums[start]))).push (nums[(start + 1) + n]!) := by
            exact ih (start := start + 1) (ys := ys.push (nums[start])) hlt'

          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            (by
              rw [h₁, h₃]
              simpa [h₂, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm])

    have hExtract : nums.extract 0 (i + 1) = (nums.extract 0 i).push (nums[i]!) := by
      have hi1_le : i + 1 ≤ nums.size := Nat.succ_le_of_lt if_pos
      have hsz0 : 0 < nums.size := Nat.lt_of_lt_of_le (Nat.zero_lt_succ i) hi1_le

      have hloop :
          Array.extract.loop nums (i + 1) 0 #[] =
            (Array.extract.loop nums i 0 #[]).push (nums[i]!) := by
        simpa using (loop_snoc (n := i) (start := 0) (ys := (#[] : Array ℤ)) (by simpa using if_pos))

      simpa [Array.extract, invariant_inv_i_bounds, hi1_le, hsz0, hloop]

    have hcount_eq :
        Array.count v (nums.extract 0 (i + 1)) =
          Array.count v (nums.extract 0 i) + (if nums[i]! == v then 1 else 0) := by
      simpa [hExtract, Array.count_push, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

    calc
      Array.count v (nums.extract 0 (i + 1))
          = Array.count v (nums.extract 0 i) + (if nums[i]! == v then 1 else 0) := hcount_eq
      _ ≤ x + (if nums[i]! == v then 1 else 0) := by
          exact Nat.add_le_add_right (hcnt' v) _
      _ = x + (if v = nums[i]! then 1 else 0) := by
          by_cases hv : v = nums[i]!
          · subst hv; simp [beq_iff_eq]
          · have hv' : nums[i]! ≠ v := by
              intro h; exact hv h.symm
            simp [hv, hv', beq_iff_eq]

theorem goal_1_0
    (nums : Array ℤ)
    (count : ℤ)
    (i : ℕ)
    (invariant_inv_i_bounds : i ≤ nums.size)
    (if_pos : i < nums.size)
    (v : ℤ)
    (hcountNew : Array.count v (nums.extract 0 (i + 1)) = Array.count v (nums.extract 0 i) + Array.count v (nums.extract i (i + 1)))
    : Array.count v (nums.extract i (i + 1)) = if v = nums[i]! then 1 else 0 := by
  classical

  -- `getElem!` agrees with `getElem` when the index is in bounds.
  have hget : nums[i]! = nums[i] := by
    simpa [if_pos]

  -- The degenerate slice `extract i i` is empty.
  have hEmpty : nums.extract i i = (#[] : Array ℤ) := by
    apply Array.ext (by
      simp [Array.size_extract_of_le invariant_inv_i_bounds])
    intro k hk1 hk2
    have hk : k < 0 := by
      simpa [Array.size_extract_of_le invariant_inv_i_bounds] using hk1
    exact (False.elim (Nat.not_lt_zero k hk))

  -- The slice `extract i (i+1)` is a singleton.
  have hextract : nums.extract i (i + 1) = #[nums[i]] := by
    have h := (@Array.extract_succ_right ℤ nums i i (Nat.lt_succ_self i) if_pos)
    calc
      nums.extract i (i + 1) = (nums.extract i i).push nums[i] := by
        simpa using h
      _ = (#[] : Array ℤ).push nums[i] := by
        simp [hEmpty]
      _ = #[nums[i]] := by
        simp

  -- Compute the count in a singleton.
  have hcountSingleton : Array.count v #[nums[i]] = (if v = nums[i] then 1 else 0) := by
    by_cases hv : v = nums[i]
    · subst hv
      simp [Array.count_singleton]
    · simp [Array.count_singleton, hv, eq_comm]

  -- Put everything together.
  calc
    Array.count v (nums.extract i (i + 1))
        = Array.count v #[nums[i]] := by
            simpa [hextract]
    _ = (if v = nums[i] then 1 else 0) := hcountSingleton
    _ = (if v = nums[i]! then 1 else 0) := by
            simpa [hget]

theorem goal_1
    (nums : Array ℤ)
    (count : ℤ)
    (i : ℕ)
    (invariant_inv_i_bounds : i ≤ nums.size)
    (if_pos : i < nums.size)
    (invariant_inv_bm_accounting : ∃ cN, count = cN.cast ∧ ∃ x, i = OfNat.ofNat 2 * x + cN ∧ ∀ (v : ℤ), Array.count v (nums.extract (OfNat.ofNat 0) i) ≤ x + if v = nums[i]! then cN else OfNat.ofNat 0)
    : ∃ cN, count + OfNat.ofNat 1 = cN.cast ∧ ∃ x, i + OfNat.ofNat 1 = OfNat.ofNat 2 * x + cN ∧ ∀ (v : ℤ), Array.count v (nums.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) ≤ x + if v = nums[i]! then cN else OfNat.ofNat 0 := by
  rcases invariant_inv_bm_accounting with ⟨cN, hcount, x, hi, hbound⟩
  refine ⟨cN + 1, ?_, x, ?_, ?_⟩
  · simpa [hcount, Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm]
  · simpa [hi, Nat.mul_assoc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  · intro v
    have hdecomp : nums.extract 0 i ++ nums.extract i (i + 1) = nums.extract 0 (i + 1) := by
      simpa [Nat.min_eq_left (Nat.zero_le _), Nat.max_eq_right (Nat.le_succ _)] using
        (@Array.extract_append_extract ℤ nums 0 i (i + 1))
    have hcountNew : Array.count v (nums.extract 0 (i + 1)) =
        Array.count v (nums.extract 0 i) + Array.count v (nums.extract i (i + 1)) := by
      -- count over append
      simpa [hdecomp] using (Array.count_append (a := v) (xs := nums.extract 0 i) (ys := nums.extract i (i + 1)))
    have hsliceCount : Array.count v (nums.extract i (i + 1)) = (if v = nums[i]! then 1 else 0) := by
      expose_names; exact (goal_1_0 nums count i invariant_inv_i_bounds if_pos v hcountNew)
    -- finish inequality
    calc
      Array.count v (nums.extract 0 (i + 1))
          = Array.count v (nums.extract 0 i) + Array.count v (nums.extract i (i + 1)) := hcountNew
      _ = Array.count v (nums.extract 0 i) + (if v = nums[i]! then 1 else 0) := by simp [hsliceCount]
      _ ≤ (x + (if v = nums[i]! then cN else 0)) + (if v = nums[i]! then 1 else 0) := by
            exact Nat.add_le_add_right (hbound v) _
      _ = x + (if v = nums[i]! then (cN + 1) else 0) := by
            by_cases hv : v = nums[i]!
            · subst hv; simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
            · simp [hv, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem goal_2
    (nums : Array ℤ)
    (candidate : ℤ)
    (count : ℤ)
    (i : ℕ)
    (invariant_inv_bm_accounting : ∃ cN, count = cN.cast ∧ ∃ x, i = OfNat.ofNat 2 * x + cN ∧ ∀ (v : ℤ), Array.count v (nums.extract (OfNat.ofNat 0) i) ≤ x + if v = candidate then cN else OfNat.ofNat 0)
    (if_pos : i < nums.size)
    (if_neg : ¬count = OfNat.ofNat 0)
    (if_neg_1 : ¬nums[i]! = candidate)
    : ∃ cN, count - OfNat.ofNat 1 = cN.cast ∧ ∃ x, i + OfNat.ofNat 1 = OfNat.ofNat 2 * x + cN ∧ ∀ (v : ℤ), Array.count v (nums.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) ≤ x + if v = candidate then cN else OfNat.ofNat 0 := by
  rcases invariant_inv_bm_accounting with ⟨cN, hcEq, x, hiEq, hcountBound⟩

  have hcN_ne0 : cN ≠ 0 := by
    intro hcN0
    apply if_neg
    simpa [hcEq, hcN0]
  have hcN_pos : 0 < cN := Nat.pos_of_ne_zero hcN_ne0
  have h1le : 1 ≤ cN := Nat.succ_le_of_lt hcN_pos
  have hcN_sub_add : cN - 1 + 1 = cN := Nat.sub_add_cancel h1le

  have hi1le : i + 1 ≤ nums.size := Nat.succ_le_of_lt if_pos

  -- relate get! to getElem, since i is in bounds
  have hget_eq : nums[i]! = nums[i]'if_pos := by
    -- unfold the bounds-checked get
    simp [Array.get!, if_pos]

  have hget_ne : nums[i]'if_pos ≠ candidate := by
    intro h
    apply if_neg_1
    -- rewrite via hget_eq
    simpa [hget_eq] using h

  -- slice 0..(i+1) splits at i
  have hextract_split : nums.extract 0 (i + 1) = nums.extract 0 i ++ nums.extract i (i + 1) := by
    have h := (@Array.extract_append_extract ℤ nums 0 i (i + 1))
    have h' : nums.extract 0 i ++ nums.extract i (i + 1) = nums.extract 0 (i + 1) := by
      simpa [Nat.min_eq_left (Nat.zero_le i), Nat.max_eq_right (Nat.le_succ i)] using h
    exact h'.symm

  refine ⟨cN - 1, ?_, ?_⟩
  · calc
      count - (1 : ℤ) = (cN.cast : ℤ) - 1 := by simpa [hcEq]
      _ = ((cN - 1 : Nat) : ℤ) := by
        simpa using (Nat.cast_pred (R := ℤ) (n := cN) hcN_pos).symm
  · refine ⟨x + 1, ?_, ?_⟩
    · -- i+1 decomposition
      have hcN_plus1 : cN + 1 = (cN - 1) + 2 := by
        calc
          cN + 1 = (cN - 1 + 1) + 1 := by simpa [hcN_sub_add]
          _ = (cN - 1) + (1 + 1) := by simp [Nat.add_assoc]
          _ = (cN - 1) + 2 := by simp
      calc
        i + 1 = 2 * x + cN + 1 := by
          simpa [hiEq, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        _ = 2 * x + (cN + 1) := by simp [Nat.add_assoc]
        _ = 2 * x + ((cN - 1) + 2) := by simpa [hcN_plus1]
        _ = 2 * (x + 1) + (cN - 1) := by
          simp [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    · intro v
      have hcount_succ : Array.count v (nums.extract 0 (i + 1)) = Array.count v (nums.extract 0 i) + Array.count v (nums.extract i (i + 1)) := by
        -- rewrite with append
        rw [hextract_split]
        simpa using (Array.count_append (a := v) (xs := nums.extract 0 i) (ys := nums.extract i (i + 1)))

      by_cases hv : v = candidate
      · cases hv
        have hold : Array.count candidate (nums.extract 0 i) ≤ x + cN := by
          simpa using (hcountBound candidate)

        -- show count on the 1-element suffix is 0
        have hone : Array.count candidate (nums.extract i (i + 1)) = 0 := by
          have hsuffix : nums.extract i (i + 1) = #[nums[i]'if_pos] := by
            apply Array.ext
            · -- size
              have : (nums.extract i (i + 1)).size = 1 := by
                simp [Array.size_extract, Nat.min_eq_left hi1le]
              simpa [this]
            · intro j hj1 hj2
              have hj0 : j = 0 := by
                have : j < 1 := by
                  simpa [Array.size_extract, Nat.min_eq_left hi1le] using hj1
                exact Nat.lt_one_iff.mp this
              subst hj0
              have hleft : (nums.extract i (i + 1))[0]'hj1 = nums[i]'if_pos := by
                simpa using (Array.getElem_extract (xs := nums) (start := i) (stop := i + 1) (i := 0) (h := hj1))
              have hright : (#[nums[i]'if_pos])[0]'hj2 = nums[i]'if_pos := by
                simpa using (Array.getElem_singleton (a := nums[i]'if_pos) (i := 0) (h := by decide))
              simpa [hleft, hright]

          have : Array.count candidate #[nums[i]'if_pos] = 0 := by
            simpa using
              (Array.count_push_of_ne (xs := (#[] : Array ℤ)) (a := candidate) (b := nums[i]'if_pos) (h := hget_ne))
          simpa [hsuffix] using this

        have hrhs : x + 1 + (cN - 1) = x + cN := by
          calc
            x + 1 + (cN - 1) = x + ((cN - 1) + 1) := by
              simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
            _ = x + cN := by simp [hcN_sub_add]

        have : Array.count candidate (nums.extract 0 (i + 1)) ≤ x + cN := by
          simpa [hcount_succ, hone, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hold
        simpa [hrhs] using this

      · have hold : Array.count v (nums.extract 0 i) ≤ x := by
          simpa [hv] using (hcountBound v)

        have hone_le : Array.count v (nums.extract i (i + 1)) ≤ 1 := by
          have := (Array.count_le_size (a := v) (xs := nums.extract i (i + 1)))
          simpa [Array.size_extract, Nat.min_eq_left hi1le] using this

        have : Array.count v (nums.extract 0 (i + 1)) ≤ x + 1 := by
          have := Nat.add_le_add hold hone_le
          simpa [hcount_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

        simpa [hv, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

theorem goal_3 : ∃ cN, (OfNat.ofNat 0 : ℤ) = cN.cast ∧ ∃ x, OfNat.ofNat 0 = OfNat.ofNat 2 * x + cN := by
    exact ⟨0, by norm_cast, 0, by norm_num⟩

theorem goal_4
    (nums : Array ℤ)
    (i_1 : ℤ)
    (i_2 : ℤ)
    (i_3 : ℕ)
    (invariant_inv_i_bounds : i_3 ≤ nums.size)
    (invariant_inv_bm_accounting : ∃ cN, i_2 = cN.cast ∧ ∃ x, i_3 = OfNat.ofNat 2 * x + cN ∧ ∀ (v : ℤ), Array.count v (nums.extract (OfNat.ofNat 0) i_3) ≤ x + if v = i_1 then cN else OfNat.ofNat 0)
    (require_1 : ∃ x, nums.size / OfNat.ofNat 2 < Array.count x nums)
    (done_1 : nums.size ≤ i_3)
    : postcondition nums i_1 := by
  -- First, `i_3` is exactly the array size.
  have hi3 : i_3 = nums.size := Nat.le_antisymm invariant_inv_i_bounds done_1

  -- Unpack the Boyer–Moore accounting invariant.
  rcases invariant_inv_bm_accounting with ⟨cN, hcN_i2, x, hi3_eq, hcount⟩

  -- Turn the invariant into a statement about the whole array `nums`.
  have hcount' : ∀ (v : ℤ), Array.count v nums ≤ x + if v = i_1 then cN else 0 := by
    intro v
    simpa [hi3, Array.extract_size] using (hcount v)

  have hsizeEq : nums.size = 2 * x + cN := by
    simpa [hi3] using hi3_eq

  -- Relate `x` to the majority threshold `nums.size / 2`.
  have hx_le_half : x ≤ nums.size / 2 := by
    have h2x_le : 2 * x ≤ nums.size := by
      -- `2*x ≤ 2*x + cN = nums.size`.
      simpa [hsizeEq] using (Nat.le_add_right (2 * x) cN)
    have hdiv : (2 * x) / 2 ≤ nums.size / 2 := Nat.div_le_div_right (c := 2) h2x_le
    -- `(2*x)/2 = x`.
    simpa using (by
      simpa using (show (2 * x) / 2 ≤ nums.size / 2 from by
        simpa [Nat.mul_div_right x (m := 2) (by decide : 0 < 2)] using hdiv))

  -- Uniqueness: any majority element must be the candidate `i_1`.
  have huniq : ∀ y : ℤ, isMajority nums y → y = i_1 := by
    intro y hyMaj
    dsimp [isMajority, majorityThreshold] at hyMaj
    by_contra hne
    have hy_le_x : Array.count y nums ≤ x := by
      have := hcount' y
      -- For `y ≠ i_1`, the extra term is `0`.
      have : Array.count y nums ≤ x + 0 := by
        simpa [if_neg hne] using this
      simpa using this
    have hy_le_half : Array.count y nums ≤ nums.size / 2 := le_trans hy_le_x hx_le_half
    exact (Nat.not_lt_of_ge hy_le_half) hyMaj

  -- Existence of a majority element implies `i_1` is majority.
  rcases require_1 with ⟨m, hm⟩
  have hmMaj : isMajority nums m := by
    dsimp [isMajority, majorityThreshold]
    simpa using hm
  have hm_eq : m = i_1 := huniq m hmMaj
  have hi1Maj : isMajority nums i_1 := by
    dsimp [isMajority, majorityThreshold]
    -- rewrite the witness majority inequality along `hm_eq`.
    simpa [hm_eq] using hm

  -- Combine: majority + uniqueness.
  refine ⟨hi1Maj, ?_⟩
  intro y hy
  exact huniq y hy

macro_rules
| `(tactic|loom_solver) => `(tactic|(
  try injections
  try subst_vars
  try grind (gen := 4)))


set_option maxHeartbeats 10000000

set_option pp.all true in
prove_correct MajorityElement by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at *); try (conv => congr <;> simp) ; try expose_names)
  exact (goal_0 nums candidate i invariant_inv_i_bounds if_pos invariant_inv_bm_accounting)
  exact (goal_1 nums count i invariant_inv_i_bounds if_pos invariant_inv_bm_accounting)
  exact (goal_2 nums candidate count i invariant_inv_bm_accounting if_pos if_neg if_neg_1)
  exact goal_3
  exact (goal_4 nums i_1 i_2 i_3 invariant_inv_i_bounds invariant_inv_bm_accounting require_1 done_1)

end Proof
