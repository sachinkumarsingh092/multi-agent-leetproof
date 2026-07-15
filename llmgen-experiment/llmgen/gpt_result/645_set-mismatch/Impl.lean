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
    645. Set Mismatch: identify the duplicated number and the missing number in an array that should represent {1..n}.
    **Important: complexity should be O(n ^ 2) time and O(n) space**
    Natural language breakdown:
    1. The input is an array `nums` of length `n`.
    2. The intended correct set of values is exactly the integers from 1 to n (each appearing once).
    3. Due to an error, exactly one value in 1..n appears twice in `nums` (the duplicated value).
    4. As a consequence, exactly one value in 1..n appears zero times in `nums` (the missing value).
    5. Every element of `nums` is in the range 1..n.
    6. The output is an array of length 2: [duplicated, missing].
    7. The duplicated value must occur exactly twice in `nums`.
    8. The missing value must occur exactly zero times in `nums`.
    9. Every other value in 1..n must occur exactly once in `nums`.
-/

section Specs
-- Helper: membership in the intended domain {1,2,...,n}
def inOneToN (n : Nat) (x : Nat) : Prop :=
  1 ≤ x ∧ x ≤ n

-- Helper: the core characterization of a valid set-mismatch instance
-- (there exists exactly one duplicated value and one missing value).
def hasSetMismatch (nums : Array Nat) : Prop :=
  let n : Nat := nums.size
  (n > 0) ∧
  (∀ (i : Nat), i < n → inOneToN n nums[i]!) ∧
  (∃ (dup : Nat) (miss : Nat),
      dup ≠ miss ∧
      inOneToN n dup ∧
      inOneToN n miss ∧
      nums.count dup = 2 ∧
      nums.count miss = 0 ∧
      (∀ (x : Nat), inOneToN n x → x ≠ dup → x ≠ miss → nums.count x = 1))

-- Preconditions
-- We require exactly the set-mismatch structure described above.
def precondition (nums : Array Nat) : Prop :=
  hasSetMismatch nums

-- Postconditions
-- The result is an array [dup, miss] that matches the unique count-pattern.
def postcondition (nums : Array Nat) (result : Array Nat) : Prop :=
  let n : Nat := nums.size
  result.size = 2 ∧
  let dup : Nat := result[0]!
  let miss : Nat := result[1]!
  dup ≠ miss ∧
  inOneToN n dup ∧
  inOneToN n miss ∧
  nums.count dup = 2 ∧
  nums.count miss = 0 ∧
  (∀ (x : Nat), inOneToN n x → x ≠ dup → x ≠ miss → nums.count x = 1)
end Specs

section Impl
method SetMismatch (nums : Array Nat)
  return (result : Array Nat)
  require precondition nums
  ensures postcondition nums result
  do
  let n : Nat := nums.size

  -- Frequency table for values 1..n (stored at indices 0..n-1)
  let mut freq : Array Nat := Array.replicate n 0

  -- Populate frequency table by scanning nums once.
  let mut i : Nat := 0
  while i < n
    -- i stays within bounds of nums (initially 0, incremented by 1)
    invariant "sm_loop1_i_bounds" i ≤ n
    -- freq keeps the intended size
    invariant "sm_loop1_freq_size" freq.size = n
    -- freq records counts of each value x in the already-scanned prefix nums[0..i)
    invariant "sm_loop1_freq_prefix_counts"
      (∀ x : Nat, inOneToN n x → freq[x - 1]! = (Array.extract nums 0 i).count x)
    decreasing n - i
  do
    let v : Nat := nums[i]!
    -- v is in 1..n by precondition, so v-1 is a valid index into freq
    let idx : Nat := v - 1
    freq := freq.set! idx (freq[idx]! + 1)
    i := i + 1

  -- Scan freq to find dup (count=2) and miss (count=0)
  let mut dup : Nat := 1
  let mut miss : Nat := 1

  let mut x : Nat := 1
  while x ≤ n
    -- x scans from 1 up to n+1
    invariant "sm_loop2_x_bounds" 1 ≤ x ∧ x ≤ n + 1
    -- dup and miss always stay in the intended domain
    invariant "sm_loop2_dup_miss_domain" inOneToN n dup ∧ inOneToN n miss
    -- freq is the final count table for nums
    invariant "sm_loop2_freq_is_counts" (∀ y : Nat, inOneToN n y → freq[y - 1]! = nums.count y)
    -- any value y already scanned with count 2 is the duplicate
    invariant "sm_loop2_dup_characterized"
      (∀ y : Nat, 1 ≤ y ∧ y < x → (freq[y - 1]! = 2 → dup = y))
    -- any value y already scanned with count 0 is the missing value
    invariant "sm_loop2_miss_characterized"
      (∀ y : Nat, 1 ≤ y ∧ y < x → (freq[y - 1]! = 0 → miss = y))
    decreasing n + 1 - x
  do
    let c : Nat := freq[x - 1]!
    if c = 2 then
      dup := x
    else
      if c = 0 then
        miss := x
    x := x + 1

  let result : Array Nat := #[dup, miss]
  return result
end Impl

section TestCases
-- Test case 1: Example 1
def test1_nums : Array Nat := #[1, 2, 2, 4]
def test1_Expected : Array Nat := #[2, 3]

-- Test case 2: Example 2
def test2_nums : Array Nat := #[1, 1]
def test2_Expected : Array Nat := #[1, 2]

-- Test case 3: duplicate is the maximum, missing is the minimum
def test3_nums : Array Nat := #[2, 2]
def test3_Expected : Array Nat := #[2, 1]

-- Test case 4: n = 3, missing is the maximum
def test4_nums : Array Nat := #[1, 2, 2]
def test4_Expected : Array Nat := #[2, 3]

-- Test case 5: n = 3, duplicate appears at both ends
def test5_nums : Array Nat := #[3, 1, 3]
def test5_Expected : Array Nat := #[3, 2]

-- Test case 6: n = 4, duplicate in the middle, missing at the end
def test6_nums : Array Nat := #[1, 2, 3, 3]
def test6_Expected : Array Nat := #[3, 4]

-- Test case 7: n = 5, unsorted, duplicate is small, missing is maximum
def test7_nums : Array Nat := #[2, 1, 1, 4, 3]
def test7_Expected : Array Nat := #[1, 5]

-- Test case 8: n = 6, duplicate is interior, missing is interior
def test8_nums : Array Nat := #[1, 5, 3, 4, 2, 2]
def test8_Expected : Array Nat := #[2, 6]

-- Test case 9: n = 7, larger case, duplicate is maximum, missing is interior
def test9_nums : Array Nat := #[1, 2, 3, 4, 5, 7, 7]
def test9_Expected : Array Nat := #[7, 6]
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((SetMismatch test1_nums).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((SetMismatch test2_nums).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((SetMismatch test3_nums).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((SetMismatch test4_nums).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((SetMismatch test5_nums).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((SetMismatch test6_nums).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((SetMismatch test7_nums).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((SetMismatch test8_nums).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((SetMismatch test9_nums).run), DivM.res test9_Expected ]
end Assertions

section Pbt
-- Decidable instance synthesis failed for this method's conditions. Giving up on PBT.

-- velvet_plausible_test SetMismatch (config := { maxMs := some 5000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000

theorem goal_0
    (nums : Array ℕ)
    (freq : Array ℕ)
    (i : ℕ)
    (invariant_sm_loop1_i_bounds : i ≤ nums.size)
    (invariant_sm_loop1_freq_size : freq.size = nums.size)
    (if_pos : i < nums.size)
    (require_1 : OfNat.ofNat 0 < nums.size ∧ (∀ i < nums.size, OfNat.ofNat 1 ≤ nums[i]! ∧ nums[i]! ≤ nums.size) ∧ ∃ dup miss, ¬dup = miss ∧ (OfNat.ofNat 1 ≤ dup ∧ dup ≤ nums.size) ∧ (OfNat.ofNat 1 ≤ miss ∧ miss ≤ nums.size) ∧ Array.count dup nums = OfNat.ofNat 2 ∧ Array.count miss nums = OfNat.ofNat 0 ∧ ∀ (x : ℕ), OfNat.ofNat 1 ≤ x → x ≤ nums.size → ¬x = dup → ¬x = miss → Array.count x nums = OfNat.ofNat 1)
    (invariant_sm_loop1_freq_prefix_counts : ∀ (x : ℕ), OfNat.ofNat 1 ≤ x → x ≤ nums.size → freq[x - OfNat.ofNat 1]! = Array.count x (nums.extract (OfNat.ofNat 0) i))
    : ∀ (x : ℕ), OfNat.ofNat 1 ≤ x → x ≤ nums.size → (freq.setIfInBounds (nums[i]! - OfNat.ofNat 1) (freq[nums[i]! - OfNat.ofNat 1]! + OfNat.ofNat 1))[x - OfNat.ofNat 1]! = Array.count x (nums.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) := by
    sorry

theorem goal_1
    (nums : Array ℕ)
    (i_1 : Array ℕ)
    (x : ℕ)
    (a : OfNat.ofNat 1 ≤ x)
    (if_pos : x ≤ nums.size)
    (if_pos_1 : i_1[x - OfNat.ofNat 1]! = OfNat.ofNat 2)
    (require_1 : OfNat.ofNat 0 < nums.size ∧ (∀ i < nums.size, OfNat.ofNat 1 ≤ nums[i]! ∧ nums[i]! ≤ nums.size) ∧ ∃ dup miss, ¬dup = miss ∧ (OfNat.ofNat 1 ≤ dup ∧ dup ≤ nums.size) ∧ (OfNat.ofNat 1 ≤ miss ∧ miss ≤ nums.size) ∧ Array.count dup nums = OfNat.ofNat 2 ∧ Array.count miss nums = OfNat.ofNat 0 ∧ ∀ (x : ℕ), OfNat.ofNat 1 ≤ x → x ≤ nums.size → ¬x = dup → ¬x = miss → Array.count x nums = OfNat.ofNat 1)
    (invariant_sm_loop2_freq_is_counts : ∀ (y : ℕ), OfNat.ofNat 1 ≤ y → y ≤ nums.size → i_1[y - OfNat.ofNat 1]! = Array.count y nums)
    : ∀ (y : ℕ), OfNat.ofNat 1 ≤ y → y < x + OfNat.ofNat 1 → i_1[y - OfNat.ofNat 1]! = OfNat.ofNat 2 → x = y := by
    classical
    intro y hy hy_lt hy_freq

    -- Turn the table lookup facts into facts about `Array.count` on `nums`.
    have hx_count : Array.count x nums = 2 := by
      have hx_eq : i_1[x - 1]! = Array.count x nums :=
        invariant_sm_loop2_freq_is_counts x a if_pos
      calc
        Array.count x nums = i_1[x - 1]! := by simpa using hx_eq.symm
        _ = 2 := by simpa using if_pos_1

    have hy_le_x : y ≤ x := by
      have : y < Nat.succ x := by
        simpa [Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hy_lt
      exact (Nat.lt_succ_iff.mp this)

    have hy_le_size : y ≤ nums.size := le_trans hy_le_x if_pos

    have hy_count : Array.count y nums = 2 := by
      have hy_eq : i_1[y - 1]! = Array.count y nums :=
        invariant_sm_loop2_freq_is_counts y hy hy_le_size
      calc
        Array.count y nums = i_1[y - 1]! := by simpa using hy_eq.symm
        _ = 2 := by simpa using hy_freq

    -- Extract the (unique) duplicate/missing witnesses from the precondition.
    rcases require_1 with ⟨_hnpos, _hvals, ⟨dup0, miss0, _hne, _hdupDom, _hmissDom, hdup0_count,
      hmiss0_count, huniq⟩⟩

    -- Any value with count 2 must be the precondition's `dup0`.
    have count2_eq_dup0 : ∀ t : ℕ, 1 ≤ t → t ≤ nums.size → Array.count t nums = 2 → t = dup0 := by
      intro t ht1 htN htcount2
      by_contra htne
      have htne_dup : t ≠ dup0 := htne
      by_cases htmiss : t = miss0
      · have h0 : Array.count t nums = 0 := by simpa [htmiss] using hmiss0_count
        have : (2 : ℕ) = 0 := by simpa [htcount2] using h0
        exact (by decide : (2 : ℕ) ≠ 0) this
      · have h1 : Array.count t nums = 1 := huniq t ht1 htN htne_dup htmiss
        have : (2 : ℕ) = 1 := by simpa [htcount2] using h1
        exact (by decide : (2 : ℕ) ≠ 1) this

    have hx_eq_dup0 : x = dup0 := count2_eq_dup0 x a if_pos hx_count
    have hy_eq_dup0 : y = dup0 := count2_eq_dup0 y hy hy_le_size hy_count

    exact hx_eq_dup0.trans hy_eq_dup0.symm

theorem goal_2
    (nums : Array ℕ)
    (i_1 : Array ℕ)
    (i_2 : ℕ)
    (dup : ℕ)
    (miss : ℕ)
    (x : ℕ)
    (a : OfNat.ofNat 1 ≤ x)
    (a_2 : OfNat.ofNat 1 ≤ dup ∧ dup ≤ nums.size)
    (a_3 : OfNat.ofNat 1 ≤ miss ∧ miss ≤ nums.size)
    (invariant_sm_loop2_dup_characterized : ∀ (y : ℕ), OfNat.ofNat 1 ≤ y → y < x → i_1[y - OfNat.ofNat 1]! = OfNat.ofNat 2 → dup = y)
    (invariant_sm_loop2_miss_characterized : ∀ (y : ℕ), OfNat.ofNat 1 ≤ y → y < x → i_1[y - OfNat.ofNat 1]! = OfNat.ofNat 0 → miss = y)
    (if_pos : x ≤ nums.size)
    (if_pos_1 : i_1[x - OfNat.ofNat 1]! = OfNat.ofNat 0)
    (invariant_sm_loop1_freq_size : i_1.size = nums.size)
    (invariant_sm_loop1_i_bounds : i_2 ≤ nums.size)
    (require_1 : OfNat.ofNat 0 < nums.size ∧ (∀ i < nums.size, OfNat.ofNat 1 ≤ nums[i]! ∧ nums[i]! ≤ nums.size) ∧ ∃ dup miss, ¬dup = miss ∧ (OfNat.ofNat 1 ≤ dup ∧ dup ≤ nums.size) ∧ (OfNat.ofNat 1 ≤ miss ∧ miss ≤ nums.size) ∧ Array.count dup nums = OfNat.ofNat 2 ∧ Array.count miss nums = OfNat.ofNat 0 ∧ ∀ (x : ℕ), OfNat.ofNat 1 ≤ x → x ≤ nums.size → ¬x = dup → ¬x = miss → Array.count x nums = OfNat.ofNat 1)
    (invariant_sm_loop2_freq_is_counts : ∀ (y : ℕ), OfNat.ofNat 1 ≤ y → y ≤ nums.size → i_1[y - OfNat.ofNat 1]! = Array.count y nums)
    (done_1 : nums.size ≤ i_2)
    (invariant_sm_loop1_freq_prefix_counts : ∀ (x : ℕ), OfNat.ofNat 1 ≤ x → x ≤ nums.size → i_1[x - OfNat.ofNat 1]! = Array.count x (nums.extract (OfNat.ofNat 0) i_2))
    : ∀ (y : ℕ), OfNat.ofNat 1 ≤ y → y < x + OfNat.ofNat 1 → i_1[y - OfNat.ofNat 1]! = OfNat.ofNat 0 → x = y := by
    intros; expose_names; try simp_all; try grind

theorem goal_3
    (nums : Array ℕ)
    (i_1 : Array ℕ)
    (i_2 : ℕ)
    (invariant_sm_loop1_i_bounds : i_2 ≤ nums.size)
    (done_1 : nums.size ≤ i_2)
    (invariant_sm_loop1_freq_prefix_counts : ∀ (x : ℕ), OfNat.ofNat 1 ≤ x → x ≤ nums.size → i_1[x - OfNat.ofNat 1]! = Array.count x (nums.extract (OfNat.ofNat 0) i_2))
    : ∀ (y : ℕ), OfNat.ofNat 1 ≤ y → y ≤ nums.size → i_1[y - OfNat.ofNat 1]! = Array.count y nums := by
  intro y hy1 hy2
  have hi : i_2 = nums.size := Nat.le_antisymm invariant_sm_loop1_i_bounds done_1
  -- specialize the prefix-count invariant and rewrite using `i_2 = nums.size`
  simpa [hi, Array.extract_size] using invariant_sm_loop1_freq_prefix_counts y hy1 hy2


prove_correct SetMismatch by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at *); try (conv => congr <;> simp) ; try expose_names)
  exact (goal_0 nums freq i invariant_sm_loop1_i_bounds invariant_sm_loop1_freq_size if_pos require_1 invariant_sm_loop1_freq_prefix_counts)
  exact (goal_1 nums i_1 x a if_pos if_pos_1 require_1 invariant_sm_loop2_freq_is_counts)
  exact (goal_2 nums i_1 i_2 dup miss x a a_2 a_3 invariant_sm_loop2_dup_characterized invariant_sm_loop2_miss_characterized if_pos if_pos_1 invariant_sm_loop1_freq_size invariant_sm_loop1_i_bounds require_1 invariant_sm_loop2_freq_is_counts done_1 invariant_sm_loop1_freq_prefix_counts)
  exact (goal_3 nums i_1 i_2 invariant_sm_loop1_i_bounds done_1 invariant_sm_loop1_freq_prefix_counts)
end Proof
