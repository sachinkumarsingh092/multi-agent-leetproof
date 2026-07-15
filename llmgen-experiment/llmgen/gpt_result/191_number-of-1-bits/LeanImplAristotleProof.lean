import Lean

import Mathlib

set_option maxHeartbeats 10000000

section Specs
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false

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

-- We count set bits among indices 0,1,...,n.size-1.
-- For i ≥ n.size, Nat.testBit is false, so the count over this range is the Hamming weight.

def precondition (n : Nat) : Prop :=
  True

def postcondition (n : Nat) (result : Nat) : Prop :=
  result = ((Finset.range n.size).filter (fun (i : Nat) => n.testBit i = true)).card ∧
  result ≤ n.size
end Specs

section Impl
def implementation (n : Nat) : Nat :=
  -- Brian Kernighan's algorithm: repeatedly clear the lowest set bit.
  -- Runs in O(k) iterations where k is the number of set bits in `n`.
  let rec go (m : Nat) (acc : Nat) : Nat :=
    if h0 : m = 0 then
      acc
    else
      go (m &&& (m - 1)) (acc + 1)
  termination_by m
  decreasing_by
    -- show `(m &&& (m - 1)) < m` when `m ≠ 0`
    have hmpos : 0 < m := Nat.pos_of_ne_zero h0
    have hlt : m - 1 < m := Nat.sub_lt hmpos (Nat.succ_pos 0)
    have hle : m &&& (m - 1) ≤ m - 1 := Nat.and_le_right
    exact Nat.lt_of_le_of_lt hle hlt
  go n 0
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

section Proof

/-- popcount defined as the number of set bits in range(n.size) -/
private noncomputable abbrev popcount (n : Nat) : Nat :=
  ((Finset.range n.size).filter (fun i => n.testBit i = true)).card

private lemma popcount_zero : popcount 0 = 0 := by
  simp [popcount, Nat.size]

/-
PROBLEM
For n > 0, size(Nat.bit b n) = n.size + 1

PROVIDED SOLUTION
Use the definition of Nat.size via binaryRec. For n ≠ 0, Nat.bit b n > 0 and size is defined as succ of the recursive call. Try simp [Nat.size, Nat.bit] or unfold size and use binaryRec properties. Try also Nat.binaryRec_eq.
-/
private lemma size_bit_pos (b : Bool) (n : Nat) (hn : n ≠ 0) :
    (Nat.bit b n).size = n.size + 1 := by
  induction n using Nat.binaryRec <;> aesop

/-
PROBLEM
size(Nat.bit true 0) = 1

PROVIDED SOLUTION
Nat.bit true 0 = 1, and Nat.size 1 = 1. Try native_decide or norm_num or simp.
-/
private lemma size_bit_true_zero : (Nat.bit true 0).size = 1 := by
  native_decide +revert

/-
PROBLEM
popcount(Nat.bit false n) = popcount n

PROVIDED SOLUTION
popcount(Nat.bit false n) = popcount(n). If n = 0, both sides are 0 (Nat.bit false 0 = 0). If n ≠ 0, use size_bit_pos to get size(bit false n) = n.size + 1. The filter over range(n.size + 1) for testBit of (bit false n): bit 0 is false (filtered out), and for i+1 testBit equals n.testBit i by Nat.testBit_bit_succ. So the filtered set is the image of the filtered set for n under (+1), which has the same cardinality. Use Finset.filter_map or show a bijection between the two filtered sets.
-/
private lemma popcount_bit_false (n : Nat) :
    popcount (Nat.bit false n) = popcount n := by
  unfold popcount;
  cases n <;> simp +decide [ Nat.testBit ];
  rw [ Nat.size ];
  rw [ Nat.binaryRec ] ; norm_num [ Nat.shiftRight_eq_div_pow ];
  rw [ Finset.card_filter, Finset.card_filter ];
  rw [ Finset.sum_range_succ' ] ; norm_num [ Nat.pow_succ', ← Nat.div_div_eq_div_mul ];
  rw [ Nat.size ]

/-
PROBLEM
popcount(Nat.bit true n) = popcount n + 1

PROVIDED SOLUTION
popcount(Nat.bit true n) = popcount(n) + 1. If n = 0: bit true 0 = 1, size = 1, filter = {0}, card = 1. popcount(0) + 1 = 0 + 1 = 1 ✓. If n ≠ 0: size(bit true n) = n.size + 1. The filter over range(n.size+1): bit 0 is true (included), and for i+1, testBit equals n.testBit i. So the filtered set is {0} ∪ image(+1)(filtered set for n). Since 0 is not in the image of (+1), the cardinality is 1 + popcount(n).
-/
private lemma popcount_bit_true (n : Nat) :
    popcount (Nat.bit true n) = popcount n + 1 := by
  unfold popcount;
  rcases n with ( _ | n ) <;> simp_all +decide [ Nat.testBit ];
  norm_num [ Nat.add_mod, Nat.mul_mod, Nat.shiftRight_eq_div_pow ];
  rw [ show ( 2 * ( n + 1 ) + 1 ).size = ( n + 1 ).size + 1 from ?_, Finset.card_filter, Finset.card_filter ];
  · rw [ Finset.sum_range_succ' ] ; norm_num [ Nat.add_mod, Nat.mul_mod, Nat.pow_succ', ← Nat.div_div_eq_div_mul ] ; ring;
    norm_num [ Nat.add_div, Nat.mul_div_assoc, Nat.pow_succ', ← Nat.div_div_eq_div_mul ];
  · convert size_bit_pos true ( n + 1 ) ( Nat.succ_ne_zero _ ) using 1

/-
PROBLEM
For m odd: m &&& (m - 1) = m - 1 (which clears bit 0)

PROVIDED SOLUTION
We need (2k+1) &&& (2k) = 2k. Use Nat.eq_of_testBit_eq and Nat.testBit_and. For each bit i: ((2k+1) &&& (2k)).testBit i = (2k+1).testBit i && (2k).testBit i. For i = 0: true && false = false = (2k).testBit 0. For i > 0: k.testBit (i-1) && k.testBit (i-1) = k.testBit (i-1) = (2k).testBit i. So they agree on all bits. Use ext_iff or bitwise extensionality.
-/
private lemma and_sub_one_odd (k : Nat) :
    (2 * k + 1) &&& (2 * k) = 2 * k := by
  refine' Nat.eq_of_testBit_eq _;
  intro i; cases i <;> simp +decide [ Nat.testBit_and ] ;
  simp +decide [ Nat.testBit, Nat.shiftRight_eq_div_pow ];
  norm_num [ Nat.add_div, Nat.pow_succ', ← Nat.div_div_eq_div_mul ]

/-
PROBLEM
For m = 2k with k ≥ 1: m &&& (m - 1) = 2 * (k &&& (k - 1))

PROVIDED SOLUTION
We need (2k) &&& (2k - 1) = 2 * (k &&& (k-1)) for k ≥ 1. Since k ≥ 1, 2k ≥ 2, so 2k - 1 = 2*(k-1) + 1. Use Nat.eq_of_testBit_eq and Nat.testBit_and. For bit 0: (2k).testBit 0 = false, so LHS bit 0 = false. RHS = 2*(k&(k-1)), bit 0 = false. OK. For bit (i+1): LHS = k.testBit i && (k-1).testBit i = (k &&& (k-1)).testBit i. RHS = (k&&(k-1)).testBit i. They agree.
-/
private lemma and_sub_one_even (k : Nat) (hk : k ≥ 1) :
    (2 * k) &&& (2 * k - 1) = 2 * (k &&& (k - 1)) := by
  rcases k with ( _ | _ | k ) <;> simp_all +decide [ Nat.mul_succ, pow_succ' ];
  refine' Nat.eq_of_testBit_eq fun i => _;
  rcases i with ( _ | i ) <;> simp +arith +decide [ Nat.testBit_and, Nat.testBit_succ ];
  rw [ Nat.testBit_div_two ] ; simp +arith +decide [ Nat.testBit_and ] ; ring;
  grind

/-
PROBLEM
The main Kernighan property: popcount(m &&& (m-1)) + 1 = popcount(m) for m ≠ 0

PROVIDED SOLUTION
Prove by strong induction on m. Since m ≠ 0, write m using Nat.bitCasesOn as m = Nat.bit b k for some b and k.

Case 1: b = true (m is odd, m = 2k+1). Then m - 1 = 2k. By and_sub_one_odd, m &&& (m-1) = 2k = Nat.bit false k. popcount(Nat.bit false k) + 1 = popcount(k) + 1 (by popcount_bit_false) = popcount(Nat.bit true k) (by popcount_bit_true). Done since m = Nat.bit true k.

Case 2: b = false (m is even, m = 2k, k ≥ 1 since m ≠ 0). By and_sub_one_even, m &&& (m-1) = 2*(k &&& (k-1)) = Nat.bit false (k &&& (k-1)). popcount(Nat.bit false (k&&(k-1))) + 1 = popcount(k &&& (k-1)) + 1 (by popcount_bit_false) = popcount(k) (by the induction hypothesis on k, since k < m = 2k and k ≠ 0) = popcount(Nat.bit false k) (by popcount_bit_false). Done since m = Nat.bit false k.

For the IH application: k < 2k when k ≥ 1. k ≠ 0 since m = 2k ≠ 0 implies k ≥ 1.

Key steps: use Nat.bitCasesOn to decompose m, then apply the helper lemmas and_sub_one_odd, and_sub_one_even, popcount_bit_false, popcount_bit_true. Use Nat.bit_val to convert between Nat.bit b n and 2*n + b.toNat.
-/
private lemma kernighan_popcount (m : Nat) (hm : m ≠ 0) :
    popcount (m &&& (m - 1)) + 1 = popcount m := by
  induction' m using Nat.strong_induction_on with m ih;
  rcases Nat.even_or_odd' m with ⟨ k, rfl | rfl ⟩;
  · by_cases hk : k = 0 <;> simp_all +decide [ Nat.mul_succ ];
    rw [ and_sub_one_even k ( Nat.pos_of_ne_zero hk ) ];
    -- By definition of popcount, we know that popcount(2 * m) = popcount(m) for any m.
    have h_popcount_2m : ∀ m : ℕ, popcount (2 * m) = popcount m := by
      intro m; exact (by
      convert popcount_bit_false m using 1);
    rw [ h_popcount_2m, h_popcount_2m, ih k ( by linarith [ Nat.pos_of_ne_zero hk ] ) hk ];
  · simp_all +decide [ and_sub_one_odd, popcount_bit_false, popcount_bit_true ];
    rw [ show popcount ( 2 * k + 1 ) = popcount ( 2 * k ) + 1 from ?_ ];
    convert popcount_bit_true _ using 2;
    convert popcount_bit_false _ using 2

theorem correctness_goal_0_0 (n : ℕ) (h_precond : precondition n) (m : ℕ) (ih : ∀ m_1 < m, ∀ (acc : ℕ), implementation.go m_1 acc = acc + {i ∈ Finset.range m_1.size | m_1.testBit i = true}.card) (acc : ℕ) (h0 : ¬m = 0) (hlt : m &&& m - 1 < m) : {i ∈ Finset.range (m &&& m - 1).size | (m &&& m - 1).testBit i = true}.card + 1 =
  {i ∈ Finset.range m.size | m.testBit i = true}.card := by
    exact kernighan_popcount m h0
end Proof