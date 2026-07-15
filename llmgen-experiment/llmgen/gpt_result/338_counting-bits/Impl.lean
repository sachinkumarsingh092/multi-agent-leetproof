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
  -- O(n) time / O(n) space DP based on:
  -- bits(i) = bits(i/2) + (i % 2)
  let mut res : Array Nat := Array.mkArray (n + 1) 0
  let mut i : Nat := 1
  while i < res.size
    -- Invariant: `res` keeps its intended fixed size throughout the loop.
    invariant "cb_size" res.size = n + 1
    -- Invariant: loop index stays in range; `1 ≤ i` also ensures `i/2 < i`,
    -- so `res[half]!` refers to an already-computed entry.
    invariant "cb_i_bounds" 1 ≤ i ∧ i ≤ res.size
    -- Invariant: all entries below `i` already equal the spec popcount value.
    invariant "cb_prefix_correct" (∀ k : Nat, k < i → res[k]! = popcountUpTo (n + 1) k)
    -- Decreasing: remaining distance to the loop upper bound.
    decreasing res.size - i
  do
    let half : Nat := i / 2
    let bit : Nat := i % 2
    let v : Nat := res[half]! + bit
    res := res.set! i v
    i := i + 1
  return res
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

theorem goal_0
    (n : ℕ)
    (i : ℕ)
    (res : Array ℕ)
    (invariant_cb_size : res.size = n + OfNat.ofNat 1)
    (a : OfNat.ofNat 1 ≤ i)
    (invariant_cb_prefix_correct : ∀ k < i, res[k]! = {k_1 ∈ Finset.range (n + OfNat.ofNat 1) | k.testBit k_1 = true}.card)
    (if_pos : i < res.size)
    : ∀ k < i + OfNat.ofNat 1, (res.setIfInBounds i (res[i / OfNat.ofNat 2]! + i % OfNat.ofNat 2))[k]! = {k_1 ∈ Finset.range (n + OfNat.ofNat 1) | k.testBit k_1 = true}.card := by
  intro k hk
  have hk' : k < i + 1 := by simpa using hk
  have hkle : k ≤ i := Nat.lt_succ_iff.mp hk'

  let spec (x : Nat) : Nat := {k_1 ∈ Finset.range (n + 1) | x.testBit k_1 = true}.card
  have hspec_prefix : ∀ k < i, res[k]! = spec k := by
    intro k hk
    simpa [spec] using invariant_cb_prefix_correct k hk

  set v : Nat := res[i / 2]! + i % 2

  have hklt_or : k < i ∨ k = i := lt_or_eq_of_le hkle
  cases hklt_or with
  | inl hlt =>
      have hik : i ≠ k := (ne_of_lt hlt).symm
      have hget : (res.setIfInBounds i v)[k]! = res[k]! := by
        change (res.setIfInBounds i v).get! k = res.get! k
        simp [Array.get!_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne, hik]
      simpa [spec, v] using (hget.trans (hspec_prefix k hlt))

  | inr hEq =>
      have hkEq : k = i := by simpa [eq_comm] using hEq

      have hgoal_i : (res.setIfInBounds i v)[i]! = spec i := by
        have hset : (res.setIfInBounds i v)[i]! = v := by
          change (res.setIfInBounds i v).get! i = v
          rw [Array.get!_eq_getD_getElem?]
          simp [Array.getElem?_setIfInBounds_self, if_pos]

        have hi0 : 0 < i := lt_of_lt_of_le (Nat.zero_lt_one) (by simpa using a)
        have hhalf_lt : i / 2 < i := by
          simpa using (Nat.div_lt_self hi0 (by decide : 1 < (2 : Nat)))
        have hhalf_spec : res[i / 2]! = spec (i / 2) := hspec_prefix (i / 2) hhalf_lt

        have hi_le_n : i ≤ n := by
          have : i < n + 1 := by
            simpa [invariant_cb_size, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using if_pos
          exact Nat.lt_succ_iff.mp this
        have hhalf_le_n : i / 2 ≤ n := le_trans (Nat.div_le_self i 2) hi_le_n
        have hhalf_lt_pow : i / 2 < 2 ^ n :=
          lt_of_le_of_lt hhalf_le_n (Nat.lt_two_pow_self (n := n))
        have hbitn_false : (i / 2).testBit n = false := by
          by_cases hb : (i / 2).testBit n = true
          · have hge : i / 2 ≥ 2 ^ n := Nat.testBit_implies_ge (x := i / 2) (i := n) hb
            exact (False.elim ((not_lt_of_ge hge) hhalf_lt_pow))
          · cases h' : (i / 2).testBit n <;> simp [h'] at hb
            · rfl

        have hmod_if : (if i % 2 = 1 then 1 else 0) = i % 2 := by
          have hlt : i % 2 < 2 := Nat.mod_lt i (by decide : 0 < (2 : Nat))
          cases hmod : i % 2 with
          | zero =>
              simp [hmod]
          | succ r =>
              have hr : r = 0 := by
                have : Nat.succ r < Nat.succ 1 := by simpa [hmod] using hlt
                have : r < 1 := Nat.succ_lt_succ_iff.mp this
                have : r ≤ 0 := Nat.lt_succ_iff.mp this
                exact Nat.eq_zero_of_le_zero this
              subst hr
              have : i % 2 = 1 := by simpa [hmod]
              simp [this]

        have hspec_rec : spec i = spec (i / 2) + i % 2 := by
          classical
          have hspec_half : spec (i / 2) = {k_1 ∈ Finset.range n | (i / 2).testBit k_1 = true}.card := by
            simp [spec, Finset.range_succ, Finset.filter_insert, hbitn_false]

          let T : Finset Nat := {k_1 ∈ Finset.range n | (i / 2).testBit k_1 = true}
          let A : Finset Nat := if i % 2 = 1 then {0} else (∅ : Finset Nat)
          let B : Finset Nat := T.image Nat.succ

          have hS : {k_1 ∈ Finset.range (n + 1) | i.testBit k_1 = true} = A ∪ B := by
            ext x
            cases x with
            | zero =>
                have hbit0 : i.testBit 0 = true ↔ i % 2 = 1 := by
                  simpa using (Nat.mod_two_eq_one_iff_testBit_zero (x := i)).symm
                by_cases hm : i % 2 = 1 <;> simp [A, B, T, hbit0, hm]
            | succ x =>
                by_cases hm : i % 2 = 1 <;>
                  simp [A, B, T, hm, Nat.testBit_succ, Nat.succ_lt_succ_iff, Finset.mem_image]

          have hdis : Disjoint A B := by
            classical
            by_cases h : i % 2 = 1
            · simp [A, B, h, Finset.disjoint_left, Finset.mem_image]
            · simp [A, h]

          have hcard :
              ({k_1 ∈ Finset.range (n + 1) | i.testBit k_1 = true}.card) = A.card + B.card := by
            simpa [hS] using (Finset.card_union_of_disjoint hdis)
          have hB : B.card = T.card := by
            simpa [B] using
              (Finset.card_image_of_injective (s := T) (f := Nat.succ) Nat.succ_injective)

          calc
            spec i = ({k_1 ∈ Finset.range (n + 1) | i.testBit k_1 = true}.card) := by rfl
            _ = A.card + T.card := by simpa [hcard, hB]
            _ = (if i % 2 = 1 then 1 else 0) + T.card := by
                  by_cases h : i % 2 = 1 <;> simp [A, h]
            _ = i % 2 + T.card := by simp [hmod_if, Nat.add_comm]
            _ = spec (i / 2) + i % 2 := by
                  simp [hspec_half, T, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

        have hv : v = spec i := by
          calc
            v = spec (i / 2) + i % 2 := by
                  simp [v, hhalf_spec, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
            _ = spec i := by
                  simpa [Nat.add_comm] using hspec_rec.symm

        calc
          (res.setIfInBounds i v)[i]! = v := hset
          _ = spec i := hv

      simpa [hkEq] using hgoal_i

theorem goal_1
    (n : ℕ)
    : (mkArray (n + OfNat.ofNat 1) (OfNat.ofNat 0)).size = n + OfNat.ofNat 1 := by
    -- unfold mkArray; then simp
    simp [Array.mkArray]

theorem goal_2
    (n : ℕ)
    : OfNat.ofNat 1 ≤ (mkArray (n + OfNat.ofNat 1) (OfNat.ofNat 0)).size := by
    intros; expose_names; exact tsub_add_cancel_iff_le.mp rfl

theorem goal_3
    (n : ℕ)
    : (mkArray (n + OfNat.ofNat 1) (OfNat.ofNat 0))[OfNat.ofNat 0]! = OfNat.ofNat 0 := by
  -- Try unfolding/simplifying `mkArray` and the indexing operations.
  simp [mkArray]


prove_correct CountingBits by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at *); try (conv => congr <;> simp) ; try expose_names)
  exact (goal_0 n i res invariant_cb_size a invariant_cb_prefix_correct if_pos)
  exact (goal_1 n)
  exact (goal_2 n)
  exact (goal_3 n)
end Proof
