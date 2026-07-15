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
    896. Monotonic Array: decide whether an integer array is monotone increasing or monotone decreasing.
    **Important: complexity should be O(n) time and O(1) space**
    Natural language breakdown:
    1. Input is an array of integers `nums`.
    2. `nums` is monotone increasing if for all indices i and j with i ≤ j, we have nums[i] ≤ nums[j].
    3. `nums` is monotone decreasing if for all indices i and j with i ≤ j, we have nums[i] ≥ nums[j].
    4. The array is monotonic if it is monotone increasing or monotone decreasing.
    5. The function returns `true` exactly when the input array is monotonic, otherwise `false`.
    6. Empty arrays and single-element arrays are monotonic (both conditions hold vacuously).
-/

-- A property-based definition of monotone increasing over Array Int using Nat indices.
-- We quantify over all i ≤ j that are valid indices.
def monotoneIncreasing (nums : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < nums.size → j < nums.size → i ≤ j → nums[i]! ≤ nums[j]!

-- A property-based definition of monotone decreasing over Array Int using Nat indices.
def monotoneDecreasing (nums : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < nums.size → j < nums.size → i ≤ j → nums[i]! ≥ nums[j]!

def monotonic (nums : Array Int) : Prop :=
  monotoneIncreasing nums ∨ monotoneDecreasing nums

def precondition (nums : Array Int) : Prop :=
  True

def postcondition (nums : Array Int) (result : Bool) : Prop :=
  (result = true ↔ monotonic nums) ∧
  (result = false ↔ ¬ monotonic nums)
end Specs

section Impl
def implementation (nums : Array Int) : Bool :=
  let rec check (i : Nat) (inc : Bool) (dec : Bool) : Bool :=
    if h : i + 1 < nums.size then
      let a := nums[i]'(by omega)
      let b := nums[i + 1]
      let inc' := inc && (a ≤ b)
      let dec' := dec && (a ≥ b)
      if !inc' && !dec' then false
      else check (i + 1) inc' dec'
    else
      inc || dec
  termination_by nums.size - i
  check 0 true true
end Impl

section TestCases
-- Test case 1: Example 1
-- Input: [1,2,2,3]
-- Output: true
def test1_nums : Array Int := #[1, 2, 2, 3]
def test1_Expected : Bool := true

-- Test case 2: Example 2
-- Input: [6,5,4,4]
-- Output: true
def test2_nums : Array Int := #[6, 5, 4, 4]
def test2_Expected : Bool := true

-- Test case 3: Example 3
-- Input: [1,3,2]
-- Output: false
def test3_nums : Array Int := #[1, 3, 2]
def test3_Expected : Bool := false

-- Test case 4: Empty array (vacuously monotonic)
def test4_nums : Array Int := #[]
def test4_Expected : Bool := true

-- Test case 5: Singleton array (vacuously monotonic)
def test5_nums : Array Int := #[0]
def test5_Expected : Bool := true

-- Test case 6: Constant array (both increasing and decreasing)
def test6_nums : Array Int := #[2, 2, 2, 2]
def test6_Expected : Bool := true

-- Test case 7: Strictly increasing with negatives and positives (covers -1,0,1)
def test7_nums : Array Int := #[-1, 0, 1]
def test7_Expected : Bool := true

-- Test case 8: Strictly decreasing with negatives and positives (covers 1,0,-1)
def test8_nums : Array Int := #[1, 0, -1]
def test8_Expected : Bool := true

-- Test case 9: Not monotonic due to a rise then fall
def test9_nums : Array Int := #[1, 2, 1, 2]
def test9_Expected : Bool := false
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
  return (result : Bool)
  require precondition nums
  ensures postcondition nums result
  do
  return (implementation nums)

velvet_plausible_test implementationPbt (config := { maxMs := some 20000 })
end Pbt

section Proof
theorem correctness_goal_0
    (nums : Array ℤ)
    : monotoneIncreasing nums ↔ ∀ (k : ℕ), k + 1 < nums.size → nums[k]! ≤ nums[k + 1]! := by
  unfold monotoneIncreasing
  constructor
  · -- Forward: global → consecutive
    intro h k hk
    exact h k (k + 1) (by omega) hk (by omega)
  · -- Backward: consecutive → global
    intro h i j hi hj hij
    have : ∀ d, j - i = d → nums[i]! ≤ nums[j]! := by
      intro d
      induction d generalizing j with
      | zero =>
        intro heq
        have : i = j := by omega
        subst this; exact le_refl _
      | succ n ih =>
        intro heq
        have hlt : i < j := by omega
        have hj1 : j - 1 < nums.size := by omega
        have hij1 : i ≤ j - 1 := by omega
        have step1 : nums[i]! ≤ nums[j - 1]! := ih (j - 1) hj1 hij1 (by omega)
        have hk : (j - 1) + 1 < nums.size := by omega
        have step2 : nums[j - 1]! ≤ nums[(j - 1) + 1]! := h (j - 1) hk
        have : (j - 1) + 1 = j := by omega
        rw [this] at step2
        exact le_trans step1 step2
    exact this (j - i) rfl

theorem correctness_goal_1
    (nums : Array ℤ)
    : monotoneDecreasing nums ↔ ∀ (k : ℕ), k + 1 < nums.size → nums[k]! ≥ nums[k + 1]! := by
  unfold monotoneDecreasing
  constructor
  · -- Forward: global ⇒ consecutive
    intro h k hk
    exact h k (k + 1) (by omega) hk (Nat.le_succ k)
  · -- Backward: consecutive ⇒ global
    intro h i j hi hj hij
    have key : ∀ d : ℕ, ∀ a : ℕ, a < nums.size → a + d < nums.size → nums[a]! ≥ nums[a + d]! := by
      intro d
      induction d with
      | zero => intro a ha _; simp
      | succ n ih =>
        intro a ha had
        have h1 : a + n < nums.size := by omega
        have h2 : nums[a]! ≥ nums[a + n]! := ih a ha h1
        have h3 : a + n + 1 < nums.size := by omega
        have h4 : nums[a + n]! ≥ nums[a + n + 1]! := h (a + n) h3
        have h5 : a + n + 1 = a + (n + 1) := by omega
        rw [h5] at h4
        exact ge_trans h2 h4
    have hd : j = i + (j - i) := by omega
    rw [hd]
    exact key (j - i) i hi (by omega)

theorem correctness_goal_2_0
    (nums : Array ℤ)
    : ∀ (fuel i : ℕ) (inc dec : Bool),
  fuel = nums.size - i →
    (inc = true ↔ ∀ k < i, k + 1 < nums.size → nums[k]! ≤ nums[k + 1]!) →
      (dec = true ↔ ∀ k < i, k + 1 < nums.size → nums[k]! ≥ nums[k + 1]!) →
        i ≤ nums.size →
          (implementation.check nums i inc dec = true ↔
            (∀ (k : ℕ), k + 1 < nums.size → nums[k]! ≤ nums[k + 1]!) ∨
              ∀ (k : ℕ), k + 1 < nums.size → nums[k]! ≥ nums[k + 1]!) := by
    intro fuel
    induction fuel with
    | zero =>
      intro i inc dec h_fuel h_inc h_dec h_bound
      have h_not_lt : ¬ (i + 1 < nums.size) := by omega
      unfold implementation.check
      split
      · omega
      · rw [Bool.or_eq_true]
        constructor
        · rintro (h | h)
          · left; exact fun k hk => h_inc.mp h k (by omega) hk
          · right; exact fun k hk => h_dec.mp h k (by omega) hk
        · rintro (h | h)
          · left; exact h_inc.mpr (fun k _ hk2 => h k hk2)
          · right; exact h_dec.mpr (fun k _ hk2 => h k hk2)
    | succ n ih =>
      intro i inc dec h_fuel h_inc h_dec h_bound
      unfold implementation.check
      split
      case isTrue h_lt =>
        have hi : i < nums.size := by omega
        have hconv_i : ∀ (h1 : i < nums.size), nums[i]'h1 = nums[i]! := by
          intro h1; exact (getElem!_pos nums i h1).symm
        have hconv_i1 : ∀ (h1 : i + 1 < nums.size), nums[i + 1]'h1 = nums[i + 1]! := by
          intro h1; exact (getElem!_pos nums (i + 1) h1).symm
        -- The goal has `have` bindings. Let's simplify them away.
        -- Use `show` to rewrite to the beta-reduced form
        show (if (!(inc && decide (nums[i]'hi ≤ nums[i + 1]'h_lt)) &&
                  !(dec && decide (nums[i]'hi ≥ nums[i + 1]'h_lt))) = true
             then false
             else implementation.check nums (i + 1)
                    (inc && decide (nums[i]'hi ≤ nums[i + 1]'h_lt))
                    (dec && decide (nums[i]'hi ≥ nums[i + 1]'h_lt))) = true ↔ _
        -- Build invariants
        have h_inc' : (inc && decide (nums[i]'hi ≤ nums[i + 1]'h_lt)) = true ↔
            ∀ k < i + 1, k + 1 < nums.size → nums[k]! ≤ nums[k + 1]! := by
          rw [Bool.and_eq_true_iff, decide_eq_true_iff]
          constructor
          · rintro ⟨h1, h2⟩ k hk hk2
            rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hk) with rfl | hlt
            · rwa [hconv_i hi, hconv_i1 h_lt] at h2
            · exact h_inc.mp h1 k hlt hk2
          · intro h
            refine ⟨h_inc.mpr (fun k hk hk2 => h k (by omega) hk2), ?_⟩
            rw [hconv_i hi, hconv_i1 h_lt]; exact h i (by omega) h_lt
        have h_dec' : (dec && decide (nums[i]'hi ≥ nums[i + 1]'h_lt)) = true ↔
            ∀ k < i + 1, k + 1 < nums.size → nums[k]! ≥ nums[k + 1]! := by
          rw [Bool.and_eq_true_iff, decide_eq_true_iff]
          constructor
          · rintro ⟨h1, h2⟩ k hk hk2
            rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hk) with rfl | hlt
            · rwa [hconv_i hi, hconv_i1 h_lt] at h2
            · exact h_dec.mp h1 k hlt hk2
          · intro h
            refine ⟨h_dec.mpr (fun k hk hk2 => h k (by omega) hk2), ?_⟩
            rw [hconv_i hi, hconv_i1 h_lt]; exact h i (by omega) h_lt
        -- Now split on the if
        split
        case isTrue h_both =>
          simp only [Bool.false_eq_true]
          rw [Bool.and_eq_true, Bool.not_eq_true', Bool.not_eq_true'] at h_both
          obtain ⟨h1, h2⟩ := h_both
          constructor
          · exact False.elim
          · rintro (h_all | h_all)
            · exact absurd (h_inc'.mpr (fun k hk hk2 => h_all k hk2)) (by rw [h1]; exact Bool.noConfusion)
            · exact absurd (h_dec'.mpr (fun k hk hk2 => h_all k hk2)) (by rw [h2]; exact Bool.noConfusion)
        case isFalse h_not_both =>
          exact ih (i + 1) _ _ (by omega) h_inc' h_dec' (by omega)
      case isFalse h_not_lt =>
        rw [Bool.or_eq_true]
        constructor
        · rintro (h | h)
          · left; exact fun k hk => h_inc.mp h k (by omega) hk
          · right; exact fun k hk => h_dec.mp h k (by omega) hk
        · rintro (h | h)
          · left; exact h_inc.mpr (fun k _ hk2 => h k hk2)
          · right; exact h_dec.mpr (fun k _ hk2 => h k hk2)

theorem correctness_goal_2
    (nums : Array ℤ)
    : ∀ (i : ℕ) (inc dec : Bool),
  (inc = true ↔ ∀ k < i, k + 1 < nums.size → nums[k]! ≤ nums[k + 1]!) →
    (dec = true ↔ ∀ k < i, k + 1 < nums.size → nums[k]! ≥ nums[k + 1]!) →
      i ≤ nums.size →
        (implementation.check nums i inc dec = true ↔
          (∀ (k : ℕ), k + 1 < nums.size → nums[k]! ≤ nums[k + 1]!) ∨
            ∀ (k : ℕ), k + 1 < nums.size → nums[k]! ≥ nums[k + 1]!) := by
    have h_main : ∀ (fuel : ℕ) (i : ℕ) (inc dec : Bool),
      fuel = nums.size - i →
      (inc = true ↔ ∀ k < i, k + 1 < nums.size → nums[k]! ≤ nums[k + 1]!) →
      (dec = true ↔ ∀ k < i, k + 1 < nums.size → nums[k]! ≥ nums[k + 1]!) →
      i ≤ nums.size →
      (implementation.check nums i inc dec = true ↔
        (∀ (k : ℕ), k + 1 < nums.size → nums[k]! ≤ nums[k + 1]!) ∨
          ∀ (k : ℕ), k + 1 < nums.size → nums[k]! ≥ nums[k + 1]!) := by
      expose_names; exact (correctness_goal_2_0 nums)
    intro i inc dec h_inc h_dec h_le
    exact h_main (nums.size - i) i inc dec rfl h_inc h_dec h_le

theorem correctness_goal
    (nums : Array Int)
    : postcondition nums (implementation nums) := by
    unfold postcondition
    have h_inc_equiv : monotoneIncreasing nums ↔ (∀ k : Nat, k + 1 < nums.size → nums[k]! ≤ nums[k+1]!) := by expose_names; exact (correctness_goal_0 nums)
    have h_dec_equiv : monotoneDecreasing nums ↔ (∀ k : Nat, k + 1 < nums.size → nums[k]! ≥ nums[k+1]!) := by expose_names; exact (correctness_goal_1 nums)
    have h_loop : ∀ (i : Nat) (inc dec : Bool),
      (inc = true ↔ ∀ k : Nat, k < i → k + 1 < nums.size → nums[k]! ≤ nums[k+1]!) →
      (dec = true ↔ ∀ k : Nat, k < i → k + 1 < nums.size → nums[k]! ≥ nums[k+1]!) →
      i ≤ nums.size →
      ((implementation.check nums i inc dec = true) ↔
        ((∀ k : Nat, k + 1 < nums.size → nums[k]! ≤ nums[k+1]!) ∨
         (∀ k : Nat, k + 1 < nums.size → nums[k]! ≥ nums[k+1]!))) := by expose_names; exact (correctness_goal_2 nums)
    have h_main : implementation nums = true ↔ monotonic nums := by
      unfold implementation monotonic
      rw [h_inc_equiv, h_dec_equiv]
      apply h_loop 0 true true
      · constructor
        · intro; intro k hk; omega
        · intro; rfl
      · constructor
        · intro; intro k hk; omega
        · intro; rfl
      · omega
    constructor
    · exact h_main
    · constructor
      · intro hf
        have : implementation nums ≠ true := by simp [hf]
        exact fun hm => this (h_main.mpr hm)
      · intro hn
        by_contra habs
        push_neg at habs
        have : implementation nums = true := by
          cases h : implementation nums
          · exact absurd h habs
          · rfl
        exact hn (h_main.mp this)
end Proof
