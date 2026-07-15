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
    CountingBits: Given a natural number n, return an array ans of length n + 1
    where ans[i] is the number of 1-bits in the binary representation of i.
    **Important: complexity should be O(n) time and O(n) space**
    Natural language breakdown:
    1. The input n is a natural number.
    2. The output ans is an array of natural numbers.
    3. The output array has length exactly n + 1.
    4. For every index i with 0 ≤ i ≤ n (equivalently i < ans.size), ans[i] equals the count of bit positions k
       where the k-th bit of i is 1.
    5. Because i ≤ n, it suffices to count 1-bits among bit positions k < n + 1 (a simple, explicit bound).
       This bound is used only for specification purposes.
-/

section Specs
-- Helper: count of 1-bits of i restricted to bit positions k < bnd.
-- We use `Nat.testBit i k : Bool` and count how many k in `Finset.range bnd` have `testBit = true`.
-- (This avoids relying on a library `Nat.popcount` constant that may not be available.)
def popcountUpTo (bnd : Nat) (i : Nat) : Nat :=
  ((Finset.range bnd).filter (fun k : Nat => i.testBit k)).card

def precondition (n : Nat) : Prop :=
  True

def postcondition (n : Nat) (ans : Array Nat) : Prop :=
  ans.size = n + 1 ∧
  (∀ (i : Nat), i < ans.size → ans[i]! = popcountUpTo (n + 1) i)
end Specs

section Impl
method CountingBits (n : Nat)
  return (ans : Array Nat)
  require precondition n
  ensures postcondition n ans
  do
  let mut ans : Array Nat := Array.mkArray (n + 1) 0
  let mut i : Nat := 1
  while i < ans.size
    -- Inv 1: array size is preserved through set! operations
    -- Init: Array.mkArray creates array of size n+1. Pres: set! preserves size. Suff: needed for postcondition.
    invariant "size_preserved" ans.size = n + 1
    -- Inv 2: loop variable bounds
    -- Init: i=1 and ans.size=n+1≥1. Pres: i increments by 1, exits when i≥ans.size. Suff: needed for termination and array access.
    invariant "i_bounds" 1 ≤ i ∧ i ≤ ans.size
    -- Inv 3: all entries below i have been correctly computed
    -- Init: i=1, ans[0]=0=popcountUpTo(n+1,0). Pres: ans[i]:=ans[i/2]+i%2=popcountUpTo(n+1,i/2)+i%2=popcountUpTo(n+1,i).
    -- Suff: when i=ans.size, all entries are correct → postcondition.
    invariant "entries_correct" ∀ j, j < i → ans[j]! = popcountUpTo (n + 1) j
    decreasing ans.size - i
  do
    ans := ans.set! i (ans[i / 2]! + i % 2)
    i := i + 1
  return ans
end Impl

section TestCases
-- Test case 1: Example 1
-- Input: n = 2
-- Output: [0,1,1]
def test1_n : Nat := 2
def test1_Expected : Array Nat := #[0, 1, 1]

-- Test case 2: Example 2
-- Input: n = 5
-- Output: [0,1,1,2,1,2]
def test2_n : Nat := 5
def test2_Expected : Array Nat := #[0, 1, 1, 2, 1, 2]

-- Test case 3: Edge case n = 0
-- Output: [0]
def test3_n : Nat := 0
def test3_Expected : Array Nat := #[0]

-- Test case 4: Edge case n = 1
-- Output: [0,1]
def test4_n : Nat := 1
def test4_Expected : Array Nat := #[0, 1]

-- Test case 5: Small n = 3
-- Output: [0,1,1,2]
def test5_n : Nat := 3
def test5_Expected : Array Nat := #[0, 1, 1, 2]

-- Test case 6: n = 8 (includes a power of two)
-- Output: [0,1,1,2,1,2,2,3,1]
def test6_n : Nat := 8
def test6_Expected : Array Nat := #[0, 1, 1, 2, 1, 2, 2, 3, 1]

-- Test case 7: n = 10 (typical mid-size)
-- Output: [0,1,1,2,1,2,2,3,1,2,2]
def test7_n : Nat := 10
def test7_Expected : Array Nat := #[0, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2]

-- Test case 8: n = 16 (includes another power of two)
-- Output: [0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,1]
def test8_n : Nat := 16
def test8_Expected : Array Nat := #[0, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 2, 3, 3, 4, 1]

-- Recommend to validate: test1_n, test2_n, test3_n
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((CountingBits test1_n).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((CountingBits test2_n).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((CountingBits test3_n).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((CountingBits test4_n).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((CountingBits test5_n).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((CountingBits test6_n).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((CountingBits test7_n).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((CountingBits test8_n).run), DivM.res test8_Expected ]
end Assertions

section Pbt
velvet_plausible_test CountingBits (config := { maxMs := some 20000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000

theorem goal_0_0_0
    (n : ℕ)
    (j : ℕ)
    (h_j_le_n : j ≤ n)
    : j / 2 < 2 ^ n := by
    have h1 : j / 2 ≤ n := Nat.le_trans (Nat.div_le_self j 2) h_j_le_n
    exact Nat.lt_of_le_of_lt h1 Nat.lt_two_pow_self

theorem goal_0_0_1
    (n : ℕ)
    (j : ℕ)
    (h_jdiv2_lt_pow : j / 2 < 2 ^ n)
    : {k ∈ Finset.range (n + 1) | (j / 2).testBit k = true}.card = {k ∈ Finset.range n | (j / 2).testBit k = true}.card := by
    congr 1
    rw [Finset.range_succ]
    rw [Finset.filter_insert]
    have hbit : (j / 2).testBit n = false := Nat.testBit_lt_two_pow h_jdiv2_lt_pow
    simp [hbit]

theorem goal_0_0_2
    (n : ℕ)
    (j : ℕ)
    : {k ∈ Finset.range (n + 1) | j.testBit k = true}.card = j % 2 + {k ∈ Finset.range n | (j / 2).testBit k = true}.card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_range_succ']
    simp only [Nat.testBit_succ]
    -- LHS: (if j.testBit 0 = true then 1 else 0) + ∑ x in range n, if (j/2).testBit x = true then 1 else 0
    -- RHS: j % 2 + ∑ x in range n, if (j/2).testBit x = true then 1 else 0
    suffices h : (if j.testBit 0 = true then 1 else 0) = j % 2 by linarith
    rw [Nat.testBit_zero]
    split
    · -- case: decide (j % 2 = 1) = true
      rename_i h
      simp at h
      omega
    · -- case: decide (j % 2 = 1) = false  
      rename_i h
      simp at h
      omega

theorem goal_0_0
    (n : ℕ)
    (ans : Array ℕ)
    (invariant_size_preserved : ans.size = n + OfNat.ofNat 1)
    (hsize : ans.size = n + 1)
    (j : ℕ)
    (if_pos : j < ans.size)
    (h3 : j % OfNat.ofNat 2 = j % 2)
    : {k ∈ Finset.range (n + OfNat.ofNat 1) | (j / 2).testBit k = true}.card + j % 2 =
  {k ∈ Finset.range (n + OfNat.ofNat 1) | j.testBit k = true}.card := by
    have h_ofnat : n + OfNat.ofNat 1 = n + 1 := by rfl
    have h_j_le_n : j ≤ n := by omega
    have h_jdiv2_lt_pow : j / 2 < 2 ^ n := by expose_names; exact (goal_0_0_0 n j h_j_le_n)
    have h_filter_eq : ((Finset.range (n + 1)).filter (fun k => (j / 2).testBit k = true)).card =
      ((Finset.range n).filter (fun k => (j / 2).testBit k = true)).card := by expose_names; exact (goal_0_0_1 n j h_jdiv2_lt_pow)
    have h_decomp : ((Finset.range (n + 1)).filter (fun k => j.testBit k = true)).card =
      j % 2 + ((Finset.range n).filter (fun k => (j / 2).testBit k = true)).card := by expose_names; exact (goal_0_0_2 n j)
    simp only [h_ofnat] at *
    omega

theorem goal_0
    (n : ℕ)
    (ans : Array ℕ)
    (i : ℕ)
    (invariant_size_preserved : ans.size = n + OfNat.ofNat 1)
    (a : OfNat.ofNat 1 ≤ i)
    (a_1 : i ≤ ans.size)
    (invariant_entries_correct : ∀ j < i, ans[j]! = {k ∈ Finset.range (n + OfNat.ofNat 1) | j.testBit k = true}.card)
    (if_pos : i < ans.size)
    : ∀ j < i + OfNat.ofNat 1, (ans.setIfInBounds i (ans[i / OfNat.ofNat 2]! + i % OfNat.ofNat 2))[j]! = {k ∈ Finset.range (n + OfNat.ofNat 1) | j.testBit k = true}.card := by
    have ha : 1 ≤ i := a
    have hsize : ans.size = n + 1 := invariant_size_preserved
    intro j hj
    have hjlt : j < i + 1 := hj
    by_cases hji : j < i
    · -- Case j < i: the setIfInBounds doesn't affect index j
      have h_unchanged : (ans.setIfInBounds i (ans[i / OfNat.ofNat 2]! + i % OfNat.ofNat 2))[j]! = ans[j]! := by expose_names; intros; expose_names; try simp_all; try grind
      rw [h_unchanged]
      exact invariant_entries_correct j hji
    · -- Case j = i: we must have j = i
      have hji_eq : j = i := by omega
      subst hji_eq
      have h_set_val : (ans.setIfInBounds j (ans[j / OfNat.ofNat 2]! + j % OfNat.ofNat 2))[j]! = ans[j / OfNat.ofNat 2]! + j % OfNat.ofNat 2 := by expose_names; intros; expose_names; try simp_all; try grind
      rw [h_set_val]
      have hj_div2_lt : j / 2 < j := Nat.div_lt_self (by omega) (by omega)
      have h_ih : ans[j / 2]! = ((Finset.range (n + OfNat.ofNat 1)).filter (fun k => (j / 2).testBit k = true)).card := by
        have := invariant_entries_correct (j / 2) hj_div2_lt
        convert this using 2
      have h2 : j / OfNat.ofNat 2 = j / 2 := by rfl
      have h3 : j % OfNat.ofNat 2 = j % 2 := by rfl
      rw [h2, h3, h_ih]
      have h_popcount_recurrence : ((Finset.range (n + OfNat.ofNat 1)).filter (fun k => (j / 2).testBit k = true)).card + j % 2 = ((Finset.range (n + OfNat.ofNat 1)).filter (fun k => j.testBit k = true)).card := by expose_names; exact (goal_0_0 n ans invariant_size_preserved hsize j if_pos h3)
      exact h_popcount_recurrence

theorem goal_1
    (n : ℕ)
    : (mkArray (n + OfNat.ofNat 1) (OfNat.ofNat 0)).size = n + OfNat.ofNat 1 := by
    exact Array.size_mkArray

theorem goal_2
    (n : ℕ)
    : OfNat.ofNat 1 ≤ (mkArray (n + OfNat.ofNat 1) (OfNat.ofNat 0)).size := by
    intros; expose_names; exact tsub_add_cancel_iff_le.mp rfl

theorem goal_3
    (n : ℕ)
    : (mkArray (n + OfNat.ofNat 1) (OfNat.ofNat 0))[OfNat.ofNat 0]! = OfNat.ofNat 0 := by
    simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem, Array.getElem_replicate, mkArray]


prove_correct CountingBits by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at *); try (conv => congr <;> simp) ; try expose_names)
  exact (goal_0 n ans i invariant_size_preserved a a_1 invariant_entries_correct if_pos)
  exact (goal_1 n)
  exact (goal_2 n)
  exact (goal_3 n)
end Proof
