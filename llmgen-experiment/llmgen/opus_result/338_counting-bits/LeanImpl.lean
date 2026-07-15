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
def implementation (n : Nat) : Array Nat :=
  let init : Array Nat := #[0]
  List.foldl (fun (acc : Array Nat) (i : Nat) =>
    let bits := acc[i / 2]! + (i % 2)
    acc.push bits
  ) init (List.range n |>.map (· + 1))
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
#assert_same_evaluation #[(implementation test1_n), test1_Expected]

-- Test case 2
#assert_same_evaluation #[(implementation test2_n), test2_Expected]

-- Test case 3
#assert_same_evaluation #[(implementation test3_n), test3_Expected]

-- Test case 4
#assert_same_evaluation #[(implementation test4_n), test4_Expected]

-- Test case 5
#assert_same_evaluation #[(implementation test5_n), test5_Expected]

-- Test case 6
#assert_same_evaluation #[(implementation test6_n), test6_Expected]

-- Test case 7
#assert_same_evaluation #[(implementation test7_n), test7_Expected]

-- Test case 8
#assert_same_evaluation #[(implementation test8_n), test8_Expected]
end Assertions

section Pbt
method implementationPbt (n : Nat)
  return (result : Array Nat)
  require precondition n
  ensures postcondition n result
  do
  return (implementation n)

velvet_plausible_test implementationPbt (config := { maxMs := some 20000 })
end Pbt

section Proof
theorem correctness_goal_0
    (n : ℕ)
    : popcountUpTo (n + 1) 0 = 0 := by
    unfold popcountUpTo
    simp [Nat.zero_testBit, Finset.filter_False, Finset.card_empty]

theorem correctness_goal_1_0
    (n : ℕ)
    (i : ℕ)
    : popcountUpTo (n + 1) i = popcountUpTo n (i / 2) + i % 2 := by
    unfold popcountUpTo
    have hdecomp : Finset.range (n + 1) = {0} ∪ (Finset.range n).image Nat.succ := by
      ext x
      simp only [Finset.mem_range, Finset.mem_union, Finset.mem_singleton, Finset.mem_image]
      constructor
      · intro hx
        rcases x with _ | x
        · left; rfl
        · right; exact ⟨x, by omega, rfl⟩
      · intro hx
        rcases hx with rfl | ⟨y, hy, rfl⟩
        · omega
        · omega
    have hdisjoint : Disjoint ({0} : Finset ℕ) ((Finset.range n).image Nat.succ) := by
      simp [Finset.disjoint_left, Finset.mem_image, Finset.mem_singleton]
    rw [hdecomp]
    rw [Finset.filter_union]
    rw [Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisjoint)]
    -- Now handle the {0} part
    have h0 : (({0} : Finset ℕ).filter (fun k => Nat.testBit i k)).card = i % 2 := by
      rw [Finset.filter_singleton]
      rcases h_bit0 : i.testBit 0 with _ | _
      · -- false case
        simp
        have := Nat.mod_two_eq_zero_iff_testBit_zero.mpr h_bit0
        omega
      · -- true case
        simp
        have := Nat.mod_two_eq_one_iff_testBit_zero.mpr h_bit0
        omega
    -- Now handle the image succ part
    have himg : (((Finset.range n).image Nat.succ).filter (fun k => Nat.testBit i k)).card = 
                ((Finset.range n).filter (fun k => Nat.testBit (i / 2) k)).card := by
      rw [Finset.filter_image]
      rw [Finset.card_image_of_injective _ Nat.succ_injective]
      congr 1
      ext k
      simp [Nat.testBit_succ]
    rw [h0, himg]
    omega

theorem correctness_goal_1_1
    (n : ℕ)
    (i : ℕ)
    (hi1 : i ≥ 1)
    (hin : i ≤ n)
    (h_main : popcountUpTo (n + 1) i = popcountUpTo n (i / 2) + i % 2)
    : popcountUpTo (n + 1) (i / 2) = popcountUpTo n (i / 2) := by
    unfold popcountUpTo
    congr 1
    have h_idiv2_lt_n : i / 2 < n := by
      calc i / 2 < i := Nat.div_lt_self (by omega) (by omega)
        _ ≤ n := hin
    have h_testbit_false : Nat.testBit (i / 2) n = false := by
      apply Nat.testBit_lt_two_pow
      calc i / 2 < n := h_idiv2_lt_n
        _ < 2 ^ n := Nat.lt_two_pow_self
    rw [Finset.range_succ, Finset.filter_insert]
    simp [h_testbit_false]

theorem correctness_goal_1
    (n : ℕ)
    : ∀ i ≥ 1, i ≤ n → popcountUpTo (n + 1) i = popcountUpTo (n + 1) (i / 2) + i % 2 := by
    intro i hi1 hin
    -- Key lemma: popcountUpTo (n+1) i = popcountUpTo n (i/2) + i % 2
    -- Step 1: split range (n+1) at position 0 and relate higher bits to i/2
    have h_main : popcountUpTo (n + 1) i = popcountUpTo n (i / 2) + i % 2 := by expose_names; exact (correctness_goal_1_0 n i)
    -- Step 2: show popcountUpTo (n+1) (i/2) = popcountUpTo n (i/2) because (i/2).testBit n = false
    have h_extra : popcountUpTo (n + 1) (i / 2) = popcountUpTo n (i / 2) := by expose_names; exact (correctness_goal_1_1 n i hi1 hin h_main)
    linarith

theorem correctness_goal_2_0
    (n : ℕ)
    (h_popcount_zero : popcountUpTo (n + 1) 0 = 0)
    (h_popcount_rec : ∀ i ≥ 1, i ≤ n → popcountUpTo (n + 1) i = popcountUpTo (n + 1) (i / 2) + i % 2)
    (f : Array ℕ → ℕ → Array ℕ)
    (hf_def : f = fun acc x => acc.push (acc[(x + 1) / 2]! + (x + 1) % 2))
    : ∀ k ≤ n,
  let arr := List.foldl f #[0] (List.range k);
  arr.size = k + 1 ∧ ∀ i < arr.size, arr[i]! = popcountUpTo (n + 1) i := by
    subst hf_def
    intro k hk
    induction k with
    | zero =>
      simp only [List.range_zero, List.foldl_nil]
      constructor
      · rfl
      · intro i hi
        have : #[(0 : ℕ)].size = 1 := by decide
        have hi0 : i = 0 := by omega
        subst hi0
        have : #[(0 : ℕ)][0]! = 0 := by decide
        rw [this, h_popcount_zero]
    | succ k ih =>
      have ihk := ih (by omega)
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      set arr_k := List.foldl (fun acc x => acc.push (acc[(x + 1) / 2]! + (x + 1) % 2)) #[0] (List.range k)
      obtain ⟨hsize_k, hvals_k⟩ := ihk
      change (arr_k.push (arr_k[(k + 1) / 2]! + (k + 1) % 2)).size = k + 1 + 1 ∧ _
      constructor
      · rw [Array.size_push, hsize_k]
      · intro i hi
        change _ at hi
        rw [Array.size_push, hsize_k] at hi
        by_cases hlt : i < arr_k.size
        · -- Old element
          have key : (arr_k.push (arr_k[(k + 1) / 2]! + (k + 1) % 2))[i]! = arr_k[i]! := by
            simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
            rw [Array.getElem?_push_lt hlt]
            simp [Array.getElem?_eq_getElem hlt]
          rw [key]
          exact hvals_k i hlt
        · -- New element: i = k + 1
          have hi_eq : i = k + 1 := by omega
          subst hi_eq
          have key : (arr_k.push (arr_k[(k + 1) / 2]! + (k + 1) % 2))[k + 1]! =
              arr_k[(k + 1) / 2]! + (k + 1) % 2 := by
            simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
            have hsz : k + 1 = arr_k.size := by omega
            rw [hsz, Array.getElem?_push_eq]
            simp
          rw [key]
          have h_div_bound : (k + 1) / 2 < arr_k.size := by
            rw [hsize_k]; omega
          rw [hvals_k _ h_div_bound]
          exact (h_popcount_rec (k + 1) (by omega) (by omega)).symm

theorem correctness_goal_2
    (n : ℕ)
    (h_popcount_zero : popcountUpTo (n + 1) 0 = 0)
    (h_popcount_rec : ∀ i ≥ 1, i ≤ n → popcountUpTo (n + 1) i = popcountUpTo (n + 1) (i / 2) + i % 2)
    : (List.foldl (fun acc i => acc.push (acc[i / 2]! + i % 2)) #[0] (List.map (fun x => x + 1) (List.range n))).size =
    n + 1 ∧
  ∀ i < (List.foldl (fun acc i => acc.push (acc[i / 2]! + i % 2)) #[0] (List.map (fun x => x + 1) (List.range n))).size,
    (List.foldl (fun acc i => acc.push (acc[i / 2]! + i % 2)) #[0] (List.map (fun x => x + 1) (List.range n)))[i]! =
      popcountUpTo (n + 1) i := by
    -- Use foldl_map to simplify
    have h_foldl_map : List.foldl (fun acc i => acc.push (acc[i / 2]! + i % 2)) #[0] (List.map (fun x => x + 1) (List.range n)) = 
      List.foldl (fun acc x => acc.push (acc[(x + 1) / 2]! + (x + 1) % 2)) #[0] (List.range n) := by
      rw [List.foldl_map]
    rw [h_foldl_map]
    -- Define the fold function
    set f := (fun (acc : Array ℕ) (x : ℕ) => acc.push (acc[(x + 1) / 2]! + (x + 1) % 2)) with hf_def
    -- State and use the loop invariant
    have h_inv : ∀ k ≤ n, 
      let arr := List.foldl f #[0] (List.range k)
      arr.size = k + 1 ∧ ∀ i < arr.size, arr[i]! = popcountUpTo (n + 1) i := by expose_names; exact (correctness_goal_2_0 n h_popcount_zero h_popcount_rec f hf_def)
    exact h_inv n (Nat.le_refl n)

theorem correctness_goal
    (n : Nat)
    : postcondition n (implementation n) := by
    unfold postcondition implementation
    have h_popcount_zero : popcountUpTo (n + 1) 0 = 0 := by expose_names; exact (correctness_goal_0 n)
    have h_popcount_rec : ∀ (i : Nat), i ≥ 1 → i ≤ n → popcountUpTo (n + 1) i = popcountUpTo (n + 1) (i / 2) + i % 2 := by expose_names; exact (correctness_goal_1 n)
    have h_main : (List.foldl (fun (acc : Array Nat) (i : Nat) =>
      acc.push (acc[i / 2]! + (i % 2))) #[0] (List.range n |>.map (· + 1))).size = n + 1 ∧
      ∀ (i : Nat), i < (List.foldl (fun (acc : Array Nat) (i : Nat) =>
      acc.push (acc[i / 2]! + (i % 2))) #[0] (List.range n |>.map (· + 1))).size →
      (List.foldl (fun (acc : Array Nat) (i : Nat) =>
      acc.push (acc[i / 2]! + (i % 2))) #[0] (List.range n |>.map (· + 1)))[i]! = popcountUpTo (n + 1) i := by expose_names; exact (correctness_goal_2 n h_popcount_zero h_popcount_rec)
    exact h_main
end Proof
