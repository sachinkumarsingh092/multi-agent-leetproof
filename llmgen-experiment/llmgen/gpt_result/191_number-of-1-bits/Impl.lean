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
    191. Number of 1 Bits: return the number of set bits in the binary representation of a natural number.
    **Important: complexity should be O(k) time and O(1) space**, where k is the number of set bits in n.
    Natural language breakdown:
    1. Input is a natural number n (non-negative integer).
    2. Each natural number has a binary representation with bits indexed from 0 (least-significant bit) upward.
    3. A bit is set iff it equals 1, i.e. iff n.testBit i = true for that index i.
    4. The required output is the count of indices i for which the bit is set.
    5. For i ≥ n.size (the number of bits needed to represent n), n.testBit i is false, so counting up to n.size suffices.
    6. Edge cases: n = 0 has zero set bits; powers of two have exactly one set bit.
-/

section Specs
-- We count set bits among indices 0,1,...,n.size-1.
-- For i ≥ n.size, Nat.testBit is false, so the count over this range is the Hamming weight.

def precondition (n : Nat) : Prop :=
  True

def postcondition (n : Nat) (result : Nat) : Prop :=
  result = ((Finset.range n.size).filter (fun (i : Nat) => n.testBit i = true)).card ∧
  result ≤ n.size
end Specs

section Impl
method NumberOf1Bits (n : Nat)
  return (result : Nat)
  require precondition n
  ensures postcondition n result
  do
  let mut x := n
  let mut cnt : Nat := 0
  -- Brian Kernighan's algorithm: repeatedly clear the lowest set bit.
  -- Runs in O(k) iterations where k is the number of set bits.
  while x > 0
    -- Invariant: x is always obtained from n by repeatedly clearing 1-bits, so it never exceeds n.
    invariant "inv_x_le" x ≤ n
    -- Invariant: cnt counts how many 1-bits have been removed from x compared to n (measured over indices < n.size).
    -- This is the key functional invariant: it implies the desired result when the loop exits with x = 0.
    invariant "inv_cnt_plus_weight" cnt + ((Finset.range n.size).filter (fun (i : Nat) => x.testBit i = true)).card =
      ((Finset.range n.size).filter (fun (i : Nat) => n.testBit i = true)).card
    -- Invariant: the number of set bits cleared so far is bounded by the number of bit positions of n.
    invariant "inv_cnt_le_size" cnt ≤ n.size
    -- Termination: each iteration strictly decreases x (clears at least one set bit).
    decreasing x
  do
    x := x &&& (x - 1)
    cnt := cnt + 1
  return cnt
end Impl

section TestCases
-- Test case 1: Example 1
def test1_n : Nat := 11
def test1_Expected : Nat := 3

-- Test case 2: Example 2
def test2_n : Nat := 128
def test2_Expected : Nat := 1

-- Test case 3: Example 3
def test3_n : Nat := 2147483645
def test3_Expected : Nat := 30

-- Test case 4: boundary n = 0
def test4_n : Nat := 0
def test4_Expected : Nat := 0

-- Test case 5: boundary n = 1
def test5_n : Nat := 1
def test5_Expected : Nat := 1

-- Test case 6: all low bits set (15 = 0b1111)
def test6_n : Nat := 15
def test6_Expected : Nat := 4

-- Test case 7: power of two (16 = 0b10000)
def test7_n : Nat := 16
def test7_Expected : Nat := 1

-- Test case 8: all bits set in a byte (255 = 0b11111111)
def test8_n : Nat := 255
def test8_Expected : Nat := 8

-- Test case 9: all bits set in 10 bits (1023 = 0b1111111111)
def test9_n : Nat := 1023
def test9_Expected : Nat := 10
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((NumberOf1Bits test1_n).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((NumberOf1Bits test2_n).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((NumberOf1Bits test3_n).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((NumberOf1Bits test4_n).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((NumberOf1Bits test5_n).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((NumberOf1Bits test6_n).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((NumberOf1Bits test7_n).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((NumberOf1Bits test8_n).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((NumberOf1Bits test9_n).run), DivM.res test9_Expected ]
end Assertions

section Pbt
velvet_plausible_test NumberOf1Bits (config := { maxMs := some 20000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000

theorem goal_0
    (n : ℕ)
    (x : ℕ)
    (invariant_inv_x_le : x ≤ n)
    : x &&& x - OfNat.ofNat 1 ≤ n := by
  have hx : x &&& (x - (1 : Nat)) ≤ x := by
    simpa using (Nat.and_le_left (n := x) (m := x - (1 : Nat)))
  exact le_trans hx invariant_inv_x_le

theorem goal_1_0_0
    (n : ℕ)
    (require_1 : True)
    (cnt : ℕ)
    (x : ℕ)
    (invariant_inv_x_le : x ≤ n)
    (invariant_inv_cnt_plus_weight : cnt + {i ∈ Finset.range n.size | x.testBit i = true}.card = {i ∈ Finset.range n.size | n.testBit i = true}.card)
    (invariant_inv_cnt_le_size : cnt ≤ n.size)
    (if_pos : OfNat.ofNat 0 < x)
    (h_and_card : {i ∈ Finset.range n.size | x.testBit i = true ∧ (x - 1).testBit i = true}.card =
  {i ∈ Finset.range n.size | (x &&& x - 1).testBit i = true}.card)
    : {i ∈ Finset.range n.size | x.testBit i = true}.card =
  1 + {i ∈ Finset.range n.size | (x &&& x - 1).testBit i = true}.card := by
    sorry

theorem goal_1_0
    (n : ℕ)
    (require_1 : True)
    (cnt : ℕ)
    (x : ℕ)
    (invariant_inv_x_le : x ≤ n)
    (invariant_inv_cnt_plus_weight : cnt + {i ∈ Finset.range n.size | x.testBit i = true}.card = {i ∈ Finset.range n.size | n.testBit i = true}.card)
    (invariant_inv_cnt_le_size : cnt ≤ n.size)
    (if_pos : OfNat.ofNat 0 < x)
    : {i ∈ Finset.range n.size | x.testBit i = true}.card =
  OfNat.ofNat 1 + {i ∈ Finset.range n.size | x.testBit i = true ∧ (x - OfNat.ofNat 1).testBit i = true}.card := by
  classical
  have h_and_card :
      {i ∈ Finset.range n.size | x.testBit i = true ∧ (x - 1).testBit i = true}.card =
        {i ∈ Finset.range n.size | (x &&& (x - 1)).testBit i = true}.card := by
    expose_names; intros; expose_names; try simp_all; try grind
  have h_clear_lowest :
      {i ∈ Finset.range n.size | x.testBit i = true}.card =
        1 + {i ∈ Finset.range n.size | (x &&& (x - 1)).testBit i = true}.card := by
    expose_names; exact (goal_1_0_0 n require_1 cnt x invariant_inv_x_le invariant_inv_cnt_plus_weight invariant_inv_cnt_le_size if_pos h_and_card)
  -- conclude
  simpa [h_and_card, Nat.sub_eq] using h_clear_lowest

theorem goal_1
    (n : ℕ)
    (require_1 : True)
    (cnt : ℕ)
    (x : ℕ)
    (invariant_inv_x_le : x ≤ n)
    (invariant_inv_cnt_plus_weight : cnt + {i ∈ Finset.range n.size | x.testBit i = true}.card = {i ∈ Finset.range n.size | n.testBit i = true}.card)
    (invariant_inv_cnt_le_size : cnt ≤ n.size)
    (if_pos : OfNat.ofNat 0 < x)
    : cnt + OfNat.ofNat 1 + {i ∈ Finset.range n.size | x.testBit i = true ∧ (x - OfNat.ofNat 1).testBit i = true}.card = {i ∈ Finset.range n.size | n.testBit i = true}.card := by
  have h_pop : {i ∈ Finset.range n.size | x.testBit i = true}.card =
      OfNat.ofNat 1 + {i ∈ Finset.range n.size | x.testBit i = true ∧ (x - OfNat.ofNat 1).testBit i = true}.card := by
    expose_names; exact (goal_1_0 n require_1 cnt x invariant_inv_x_le invariant_inv_cnt_plus_weight invariant_inv_cnt_le_size if_pos)
  -- rewrite the invariant using h_pop
  -- invariant: cnt + weight(x) = weight(n)
  -- goal: cnt + 1 + stable = weight(n)
  calc
    cnt + OfNat.ofNat 1 + {i ∈ Finset.range n.size | x.testBit i = true ∧ (x - OfNat.ofNat 1).testBit i = true}.card
        = cnt + {i ∈ Finset.range n.size | x.testBit i = true}.card := by
            -- from h_pop
            linarith
    _ = {i ∈ Finset.range n.size | n.testBit i = true}.card := by
            simpa using invariant_inv_cnt_plus_weight

theorem goal_2_0_0
    (n : ℕ)
    (require_1 : True)
    (cnt : ℕ)
    (x : ℕ)
    (invariant_inv_x_le : x ≤ n)
    (invariant_inv_cnt_plus_weight : cnt + {i ∈ Finset.range n.size | x.testBit i = true}.card = {i ∈ Finset.range n.size | n.testBit i = true}.card)
    (invariant_inv_cnt_le_size : cnt ≤ n.size)
    (if_pos : OfNat.ofNat 0 < x)
    : n < 2 ^ n.size := by
    sorry

theorem goal_2_0
    (n : ℕ)
    (require_1 : True)
    (cnt : ℕ)
    (x : ℕ)
    (invariant_inv_x_le : x ≤ n)
    (invariant_inv_cnt_plus_weight : cnt + {i ∈ Finset.range n.size | x.testBit i = true}.card = {i ∈ Finset.range n.size | n.testBit i = true}.card)
    (invariant_inv_cnt_le_size : cnt ≤ n.size)
    (if_pos : OfNat.ofNat 0 < x)
    : 0 < {i ∈ Finset.range n.size | x.testBit i = true}.card := by
  classical

  have hnlt : n < 2 ^ n.size := by
    expose_names; exact (goal_2_0_0 n require_1 cnt x invariant_inv_x_le invariant_inv_cnt_plus_weight invariant_inv_cnt_le_size if_pos)

  have hx0 : x ≠ 0 := ne_of_gt if_pos
  obtain ⟨i, hbit⟩ := Nat.ne_zero_implies_bit_true (x := x) hx0

  have hxge : 2 ^ i ≤ x := by
    simpa [ge_iff_le] using (Nat.testBit_implies_ge (x := x) (i := i) (p := hbit))
  have hnge : 2 ^ i ≤ n := le_trans hxge invariant_inv_x_le

  have hi_nsize : i < n.size := by
    by_contra h
    have hni : n.size ≤ i := le_of_not_gt h
    have hpow : 2 ^ n.size ≤ 2 ^ i :=
      Nat.pow_le_pow_of_le_right (by decide : 0 < (2 : Nat)) hni
    have : 2 ^ n.size ≤ n := le_trans hpow hnge
    exact (Nat.not_lt_of_ge this hnlt)

  have hne : ({i ∈ Finset.range n.size | x.testBit i = true} : Finset Nat).Nonempty := by
    refine ⟨i, ?_⟩
    simp [Finset.mem_filter, Finset.mem_range, hi_nsize, hbit]

  exact (Finset.card_pos).2 hne

theorem goal_2
    (n : ℕ)
    (require_1 : True)
    (cnt : ℕ)
    (x : ℕ)
    (invariant_inv_x_le : x ≤ n)
    (invariant_inv_cnt_plus_weight : cnt + {i ∈ Finset.range n.size | x.testBit i = true}.card = {i ∈ Finset.range n.size | n.testBit i = true}.card)
    (invariant_inv_cnt_le_size : cnt ≤ n.size)
    (if_pos : OfNat.ofNat 0 < x)
    : cnt + OfNat.ofNat 1 ≤ n.size := by
  have h_wx_pos : 0 < {i ∈ Finset.range n.size | x.testBit i = true}.card := by
    expose_names; exact (goal_2_0 n require_1 cnt x invariant_inv_x_le invariant_inv_cnt_plus_weight invariant_inv_cnt_le_size if_pos)

  have h_wx_ge_one : 1 ≤ {i ∈ Finset.range n.size | x.testBit i = true}.card := by
    exact (Nat.succ_le_iff).2 h_wx_pos

  have hcnt1_le_wn : cnt + 1 ≤ {i ∈ Finset.range n.size | n.testBit i = true}.card := by
    calc
      cnt + 1 ≤ cnt + {i ∈ Finset.range n.size | x.testBit i = true}.card :=
        Nat.add_le_add_left h_wx_ge_one cnt
      _ = {i ∈ Finset.range n.size | n.testBit i = true}.card := by
        simpa using invariant_inv_cnt_plus_weight

  have hwn_le_size : {i ∈ Finset.range n.size | n.testBit i = true}.card ≤ n.size := by
    have hle : ({i ∈ Finset.range n.size | n.testBit i = true} : Finset ℕ).card ≤ (Finset.range n.size).card := by
      simpa using
        (Finset.card_filter_le (s := Finset.range n.size) (p := fun i : ℕ => n.testBit i = true))
    simpa using (le_trans hle (by simp [Finset.card_range]))

  exact le_trans hcnt1_le_wn hwn_le_size

theorem goal_3
    (x : ℕ)
    (if_pos : OfNat.ofNat 0 < x)
    : x &&& x - OfNat.ofNat 1 < x := by
    have hx0 : x ≠ 0 := Nat.ne_of_gt if_pos
    have hsub : x - 1 < x := Nat.sub_one_lt hx0
    have hand : x &&& (x - 1) ≤ x - 1 := Nat.and_le_right
    exact lt_of_le_of_lt hand hsub

theorem goal_4
    (n : ℕ)
    (i : ℕ)
    (x_1 : ℕ)
    (invariant_inv_cnt_le_size : i ≤ n.size)
    (invariant_inv_cnt_plus_weight : i + {i ∈ Finset.range n.size | x_1.testBit i = true}.card = {i ∈ Finset.range n.size | n.testBit i = true}.card)
    (done_1 : x_1 = OfNat.ofNat 0)
    : postcondition n i := by
    intros; expose_names; try simp_all; try grind


prove_correct NumberOf1Bits by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at *); try (conv => congr <;> simp) ; try expose_names)
  exact (goal_0 n x invariant_inv_x_le)
  exact (goal_1 n require_1 cnt x invariant_inv_x_le invariant_inv_cnt_plus_weight invariant_inv_cnt_le_size if_pos)
  exact (goal_2 n require_1 cnt x invariant_inv_x_le invariant_inv_cnt_plus_weight invariant_inv_cnt_le_size if_pos)
  exact (goal_3 x if_pos)
  exact (goal_4 n i x_1 invariant_inv_cnt_le_size invariant_inv_cnt_plus_weight done_1)
end Proof
