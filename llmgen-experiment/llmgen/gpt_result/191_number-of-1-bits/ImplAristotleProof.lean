import Mathlib.Tactic

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

section Specs
-- We count set bits among indices 0,1,...,n.size-1.
-- For i ≥ n.size, Nat.testBit is false, so the count over this range is the Hamming weight.

def precondition (n : Nat) : Prop :=
  True

def postcondition (n : Nat) (result : Nat) : Prop :=
  result = ((Finset.range n.size).filter (fun (i : Nat) => n.testBit i = true)).card ∧
  result ≤ n.size
end Specs

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

/-
PROVIDED SOLUTION
The key identity is: for x > 0, x &&& (x-1) clears the lowest set bit of x. So the number of set bits of x equals 1 + the number of set bits of (x &&& (x-1)).

We're given h_and_card which says the count of bits that are set in both x and (x-1) equals the count of set bits of (x &&& (x-1)).

The key step: when we clear the lowest set bit, exactly one bit changes from 1 to 0. So the filtered set for x has exactly one more element than the filtered set for (x &&& (x-1)).

We need to show: card(filter(x.testBit)) = 1 + card(filter((x &&& (x-1)).testBit)).

Using h_and_card, it suffices to show: card(filter(x.testBit)) = 1 + card(filter(x.testBit ∧ (x-1).testBit)).

The key fact about x &&& (x-1): for x > 0, the lowest set bit position j satisfies x.testBit j = true and (x-1).testBit j = false, and for all other positions i ≠ j, x.testBit i = (x-1).testBit i (either both true or both false for bits above j, and for bits below j in x they were 0 and become 1 in x-1 but x.testBit was false there anyway).

So the set {i | x.testBit i = true ∧ (x-1).testBit i = true} = {i | x.testBit i = true} \ {j} where j is the lowest set bit. This means the card differs by exactly 1.

Try using Nat.bitwise_and, Nat.testBit_and, and properties of x &&& (x-1). The approach: rewrite using h_and_card, then show that the filter with the conjunction has one fewer element.
-/
theorem goal_1_0_0 (n : ℕ) (require_1 : True) (cnt : ℕ) (x : ℕ) (invariant_inv_x_le : x ≤ n) (invariant_inv_cnt_plus_weight : cnt + {i ∈ Finset.range n.size | x.testBit i = true}.card = {i ∈ Finset.range n.size | n.testBit i = true}.card) (invariant_inv_cnt_le_size : cnt ≤ n.size) (if_pos : OfNat.ofNat 0 < x) (h_and_card : {i ∈ Finset.range n.size | x.testBit i = true ∧ (x - 1).testBit i = true}.card =
  {i ∈ Finset.range n.size | (x &&& x - 1).testBit i = true}.card) : {i ∈ Finset.range n.size | x.testBit i = true}.card =
  1 + {i ∈ Finset.range n.size | (x &&& x - 1).testBit i = true}.card := by
    -- The set of indices where x.testBit i is true but (x-1).testBit i is false is exactly the set of indices where the least significant bit of x is set.
    have h_least_significant_bit : {i ∈ Finset.range n.size | x.testBit i = true ∧ (x - 1).testBit i = false} = {Nat.factorization x 2} := by
      ext i; simp [Nat.testBit];
      constructor <;> intro hi <;> simp_all +decide [ Nat.shiftRight_eq_div_pow ];
      · -- Since $x$ is divisible by $2^i$, we have $x = 2^i \cdot m$ for some integer $m$.
        obtain ⟨m, hm⟩ : ∃ m, x = 2^i * m := by
          use x / 2^i;
          rw [ Nat.mul_div_cancel' ];
          contrapose! hi; simp_all +decide [ Nat.dvd_iff_mod_eq_zero ] ;
          cases x <;> simp_all +decide [ Nat.succ_div ];
          split_ifs <;> simp_all +decide [ Nat.dvd_iff_mod_eq_zero ];
        simp_all +decide [ Nat.factorization_mul, show m ≠ 0 by aesop_cat ];
        erw [ Nat.factorization_eq_zero_of_not_dvd ] ; erw [ Nat.dvd_iff_mod_eq_zero ] ; aesop_cat;
      · refine' ⟨ _, _, _ ⟩;
        · refine' Nat.le_trans ( Nat.le_of_lt_succ _ ) _;
          exact Nat.log 2 n + 1;
          · exact Nat.succ_lt_succ ( Nat.lt_succ_of_le ( Nat.le_log_of_pow_le ( by decide ) ( Nat.le_trans ( Nat.le_of_dvd if_pos ( Nat.ordProj_dvd _ _ ) ) invariant_inv_x_le ) ) );
          · rcases n with ( _ | _ | n ) <;> simp_all +arith +decide [ Nat.size ];
            refine' Nat.log_lt_of_lt_pow _ _ <;> norm_num [ Nat.pow_succ' ];
            -- By definition of binaryRec, we know that 2^binaryRec 0 (fun x x_1 => Nat.succ) (n + 2) is greater than n + 2.
            have h_binaryRec : ∀ m : ℕ, 2 ^ Nat.binaryRec 0 (fun x x_1 => Nat.succ) m > m := by
              intro m; induction' m using Nat.strong_induction_on with m ih; rcases m with ( _ | _ | m ) <;> simp_all +decide [ Nat.pow_succ' ] ;
              erw [ Nat.binaryRec ] ; norm_num;
              norm_num [ Nat.shiftRight_eq_div_pow ] at *;
              have := ih ( ( m + 1 + 1 ) / 2 ) ( by linarith [ Nat.div_mul_le_self ( m + 1 + 1 ) 2 ] ) ; norm_num [ Nat.pow_succ' ] at * ; linarith [ Nat.div_add_mod ( m + 1 + 1 ) 2, Nat.mod_lt ( m + 1 + 1 ) two_pos ] ;
            exact h_binaryRec _;
        · rw [ Nat.odd_iff.mp ];
          exact Nat.odd_iff.mpr ( Nat.mod_two_ne_zero.mp fun h => absurd ( Nat.dvd_of_mod_eq_zero h ) ( Nat.not_dvd_ordCompl ( by norm_num ) ( by aesop ) ) );
        · -- Since $x$ is divisible by $2^k$ but not by $2^{k+1}$, we have $x = 2^k * m$ for some odd $m$.
          obtain ⟨m, hm⟩ : ∃ m, x = 2 ^ (Nat.factorization x 2) * m ∧ Odd m := by
            exact ⟨ x / 2 ^ Nat.factorization x 2, by erw [ mul_comm, Nat.div_mul_cancel ( Nat.ordProj_dvd _ _ ) ], by exact Nat.odd_iff.mpr ( Nat.mod_two_ne_zero.mp fun h => absurd ( Nat.dvd_of_mod_eq_zero h ) ( Nat.not_dvd_ordCompl ( by norm_num ) ( by aesop ) ) ) ⟩;
          rcases hm.2 with ⟨ k, rfl ⟩ ; norm_num [ Nat.add_div, Nat.mul_div_assoc, Nat.mul_mod, Nat.pow_mod ] at hm ⊢;
          norm_num [ show x - 1 = 2 ^ ( Nat.factorization x 2 ) * ( 2 * k ) + ( 2 ^ ( Nat.factorization x 2 ) - 1 ) by rw [ tsub_eq_of_eq_add ] ; nlinarith [ Nat.sub_add_cancel ( Nat.one_le_pow ( Nat.factorization x 2 ) 2 zero_lt_two ) ] ];
          norm_num [ Nat.add_div, Nat.mul_div_assoc, Nat.pow_succ' ];
          rw [ Nat.div_eq_of_lt, if_neg ] <;> norm_num;
    rw [ ← h_and_card, ← Finset.card_singleton ( Nat.factorization x 2 ), ← h_least_significant_bit ] ; rw [ Finset.card_filter ] ; rw [ Finset.card_filter ] ; rw [ Finset.card_filter ] ; rw [ ← Finset.sum_add_distrib ] ; rw [ Finset.sum_congr rfl ] ; aesop;

/-
PROVIDED SOLUTION
This is exactly Nat.lt_size_self or follows directly from Nat.size definition. n < 2^n.size is a basic property. Try Nat.lt_two_pow_size or Nat.lt_size_self, or use exact Nat.lt_two_pow_size n, or look for the right lemma name.
-/
theorem goal_2_0_0 (n : ℕ) (require_1 : True) (cnt : ℕ) (x : ℕ) (invariant_inv_x_le : x ≤ n) (invariant_inv_cnt_plus_weight : cnt + {i ∈ Finset.range n.size | x.testBit i = true}.card = {i ∈ Finset.range n.size | n.testBit i = true}.card) (invariant_inv_cnt_le_size : cnt ≤ n.size) (if_pos : OfNat.ofNat 0 < x) : n < 2 ^ n.size := by
    convert Nat.lt_pow_of_log_lt _ _ <;> norm_num;
    rw [ Nat.log_lt_iff_lt_pow ] <;> norm_num [ Nat.size ];
    · -- By definition of binary length, we know that $n < 2^{Nat.binaryRec 0 (fun x x_1 => Nat.succ) n}$.
      have h_binary_length : ∀ n : ℕ, n < 2 ^ (Nat.binaryRec 0 (fun x x_1 => Nat.succ) n) := by
        intro n; induction' n using Nat.strong_induction_on with n ih; rcases n with ( _ | _ | n ) <;> simp +arith +decide [ Nat.pow_succ' ] ;
        erw [ Nat.binaryRec ] ; norm_num;
        have := ih ( ( n + 2 ) / 2 ) ( by linarith [ Nat.div_mul_le_self ( n + 2 ) 2 ] ) ; norm_num [ Nat.pow_succ', Nat.shiftRight_eq_div_pow ] at * ; omega;
      exact h_binary_length n;
    · aesop

end Proof