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
    Pow(x, n, p): compute x raised to the power n modulo p.
    **Important: complexity should be O(log n) time and O(1) space**
    Natural language breakdown:
    1. Inputs are an integer base x, a natural-number exponent n, and an integer modulus p.
    2. The modulus must be positive (p > 0) so that the modulo operation has a standard range of remainders.
    3. The output is the remainder of x^n upon division by p.
    4. The output must be the unique integer r such that 0 ≤ r < p and r ≡ x^n (mod p).
    5. Edge cases include n = 0 (so x^0 = 1), x = 0, negative x, and p = 1 (so the only remainder is 0).
-/

section Specs
-- The standard modular exponentiation result is characterized by:
-- (i) range constraints 0 ≤ result < p, and
-- (ii) congruence result ≡ x^n [ZMOD p].
-- These jointly make the result unique.

def precondition (x : Int) (n : Nat) (p : Int) : Prop :=
  p > 0

def postcondition (x : Int) (n : Nat) (p : Int) (result : Int) : Prop :=
  0 ≤ result ∧ result < p ∧ Int.ModEq p result (x ^ n)
end Specs

section Impl
method PowMod (x : Int) (n : Nat) (p : Int)
  return (result : Int)
  require precondition x n p
  ensures postcondition x n p result
  do
  let mut base := x % p
  let mut exp := n
  let mut res := 1 % p
  while exp > 0
    -- Invariant 1: p is positive (preserved from precondition)
    -- Init: from require p > 0. Pres: not modified. Suff: needed for range constraints in postcondition.
    invariant "p_pos" p > 0
    -- Invariant 2: res is in range [0, p)
    -- Init: 1 % p is in [0, p) when p > 0. Pres: (res * base) % p is in [0, p). Suff: gives 0 ≤ result < p.
    invariant "res_range" 0 ≤ res ∧ res < p
    -- Invariant 3: base is in range [0, p)
    -- Init: x % p is in [0, p) when p > 0. Pres: (base * base) % p is in [0, p). Suff: supports preservation of other invariants.
    invariant "base_range" 0 ≤ base ∧ base < p
    -- Invariant 4: congruence: res * base^exp ≡ x^n (mod p)
    -- Init: (1%p) * (x%p)^n ≡ 1 * x^n = x^n (mod p). Pres: both odd/even cases preserve via algebraic identity.
    -- Suff: when exp=0, res * base^0 = res ≡ x^n (mod p), giving the postcondition.
    invariant "congruence" Int.ModEq p (res * base ^ exp) (x ^ n)
    -- Decreasing: exp is halved each iteration (exp/2 < exp when exp > 0)
    decreasing exp
  do
    if exp % 2 = 1 then
      res := (res * base) % p
    base := (base * base) % p
    exp := exp / 2
  return res
end Impl

section TestCases
-- Test case 1: Example 1
-- x = 2, n = 10, p = 1000 => 24
-- 2^10 = 1024, 1024 mod 1000 = 24

def test1_x : Int := 2
def test1_n : Nat := 10
def test1_p : Int := 1000
def test1_Expected : Int := 24

-- Test case 2: Example 2

def test2_x : Int := 3
def test2_n : Nat := 5
def test2_p : Int := 13
def test2_Expected : Int := 9

-- Test case 3: Example 3

def test3_x : Int := 7
def test3_n : Nat := 1
def test3_p : Int := 7
def test3_Expected : Int := 0

-- Test case 4: Edge case n = 0 (x^0 = 1)

def test4_x : Int := 5
def test4_n : Nat := 0
def test4_p : Int := 7
def test4_Expected : Int := 1

-- Test case 5: Edge case p = 1 (only remainder is 0)

def test5_x : Int := 123
def test5_n : Nat := 456
def test5_p : Int := 1
def test5_Expected : Int := 0

-- Test case 6: Edge case x = 0 and n > 0

def test6_x : Int := 0
def test6_n : Nat := 5
def test6_p : Int := 17
def test6_Expected : Int := 0

-- Test case 7: Negative base
-- (-2)^3 = -8, (-8) mod 5 = 2

def test7_x : Int := -2
def test7_n : Nat := 3
def test7_p : Int := 5
def test7_Expected : Int := 2

-- Test case 8: Larger exponent
-- 2^100 mod 13 = 3

def test8_x : Int := 2
def test8_n : Nat := 100
def test8_p : Int := 13
def test8_Expected : Int := 3

-- Test case 9: Small modulus

def test9_x : Int := 10
def test9_n : Nat := 1
def test9_p : Int := 3
def test9_Expected : Int := 1

-- Test case 10: Base 1

def test10_x : Int := 1
def test10_n : Nat := 999
def test10_p : Int := 2
def test10_Expected : Int := 1
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((PowMod test1_x test1_n test1_p).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((PowMod test2_x test2_n test2_p).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((PowMod test3_x test3_n test3_p).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((PowMod test4_x test4_n test4_p).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((PowMod test5_x test5_n test5_p).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((PowMod test6_x test6_n test6_p).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((PowMod test7_x test7_n test7_p).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((PowMod test8_x test8_n test8_p).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((PowMod test9_x test9_n test9_p).run), DivM.res test9_Expected ]

-- Test case 10

#assert_same_evaluation #[((PowMod test10_x test10_n test10_p).run), DivM.res test10_Expected ]
end Assertions

section Pbt
velvet_plausible_test PowMod (config := { maxMs := some 20000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000

theorem goal_0
    (p : ℤ)
    (base : ℤ)
    (res : ℤ)
    (invariant_p_pos : OfNat.ofNat 0 < p)
    : OfNat.ofNat 0 ≤ res * base % p ∧ res * base % p < p := by
    exact ⟨Int.emod_nonneg _ (ne_of_gt invariant_p_pos), Int.emod_lt_of_pos _ invariant_p_pos⟩

theorem goal_1
    (p : ℤ)
    (base : ℤ)
    (require_1 : OfNat.ofNat 0 < p)
    : OfNat.ofNat 0 ≤ base * base % p ∧ base * base % p < p := by
    intros; expose_names; exact goal_0 p base base require_1

theorem goal_2
    (x : ℤ)
    (n : ℕ)
    (p : ℤ)
    (base : ℤ)
    (exp : ℕ)
    (res : ℤ)
    (invariant_congruence : res * base ^ exp ≡ x ^ n [ZMOD p])
    (if_pos_1 : exp % OfNat.ofNat 2 = OfNat.ofNat 1)
    : res * base % p * (base * base % p) ^ (exp / OfNat.ofNat 2) ≡ x ^ n [ZMOD p] := by
    have h1 : res * base % p ≡ res * base [ZMOD p] := Int.mod_modEq _ _
    have h2 : base * base % p ≡ base * base [ZMOD p] := Int.mod_modEq _ _
    have h3 : (base * base % p) ^ (exp / 2) ≡ (base * base) ^ (exp / 2) [ZMOD p] := h2.pow _
    have h4 : res * base % p * (base * base % p) ^ (exp / 2) ≡ res * base * (base * base) ^ (exp / 2) [ZMOD p] := h1.mul h3
    suffices h : res * base * (base * base) ^ (exp / 2) = res * base ^ exp by
      rw [h] at h4; exact h4.trans invariant_congruence
    have hmod : exp % 2 = 1 := by exact_mod_cast if_pos_1
    have hexp : 2 * (exp / 2) + exp % 2 = exp := Nat.div_add_mod exp 2
    rw [hmod] at hexp
    -- hexp : 2 * (exp / 2) + 1 = exp
    conv_rhs => rw [← hexp]
    rw [mul_pow, ← pow_add]
    ring_nf

theorem goal_3
    (p : ℤ)
    (base : ℤ)
    (require_1 : OfNat.ofNat 0 < p)
    : OfNat.ofNat 0 ≤ base * base % p ∧ base * base % p < p := by
    intros; expose_names; exact goal_1 p base require_1

theorem goal_4
    (x : ℤ)
    (n : ℕ)
    (p : ℤ)
    (base : ℤ)
    (exp : ℕ)
    (res : ℤ)
    (invariant_congruence : res * base ^ exp ≡ x ^ n [ZMOD p])
    (if_neg : exp % OfNat.ofNat 2 = OfNat.ofNat 0)
    : res * (base * base % p) ^ (exp / OfNat.ofNat 2) ≡ x ^ n [ZMOD p] := by
    have h_even : Even exp := by
      rw [Nat.even_iff]
      exact if_neg
    have h_two_mul : 2 * (exp / 2) = exp := Nat.two_mul_div_two_of_even h_even
    have h_mod_eq : base * base % p ≡ base * base [ZMOD p] := Int.mod_modEq (base * base) p
    have h_pow_eq : (base * base % p) ^ (exp / 2) ≡ (base * base) ^ (exp / 2) [ZMOD p] :=
      Int.ModEq.pow (exp / 2) h_mod_eq
    have h_mul_eq : res * (base * base % p) ^ (exp / 2) ≡ res * (base * base) ^ (exp / 2) [ZMOD p] :=
      Int.ModEq.mul_left res h_pow_eq
    have h_sq : (base * base) ^ (exp / 2) = base ^ exp := by
      rw [← sq, ← pow_mul, h_two_mul]
    rw [h_sq] at h_mul_eq
    exact Int.ModEq.trans h_mul_eq invariant_congruence

theorem goal_5
    (p : ℤ)
    (require_1 : OfNat.ofNat 0 < p)
    : OfNat.ofNat 0 ≤ OfNat.ofNat 1 % p ∧ OfNat.ofNat 1 % p < p := by
  constructor <;> expose_names
  intros; expose_names; try simp_all; try grind
  intros; expose_names; exact?
  intros; expose_names; exact?

theorem goal_6
    (x : ℤ)
    (p : ℤ)
    (require_1 : OfNat.ofNat 0 < p)
    : OfNat.ofNat 0 ≤ x % p ∧ x % p < p := by
    constructor
    · exact Int.emod_nonneg x (ne_of_gt require_1)
    · exact Int.emod_lt_of_pos x require_1

theorem goal_7
    (x : ℤ)
    (n : ℕ)
    (p : ℤ)
    : OfNat.ofNat 1 % p * (x % p) ^ n ≡ x ^ n [ZMOD p] := by
  have h1 : (1 : ℤ) % p ≡ 1 [ZMOD p] := Int.mod_modEq 1 p
  have h2 : x % p ≡ x [ZMOD p] := Int.mod_modEq x p
  have h3 : (x % p) ^ n ≡ x ^ n [ZMOD p] := h2.pow n
  have h4 : (1 : ℤ) % p * (x % p) ^ n ≡ 1 * x ^ n [ZMOD p] := h1.mul h3
  rwa [one_mul] at h4

theorem goal_8
    (x : ℤ)
    (n : ℕ)
    (p : ℤ)
    (i : ℤ)
    (i_1 : ℕ)
    (res_1 : ℤ)
    (a : OfNat.ofNat 0 ≤ res_1)
    (a_1 : res_1 < p)
    (invariant_congruence : res_1 * i ^ i_1 ≡ x ^ n [ZMOD p])
    (done_1 : i_1 = OfNat.ofNat 0)
    : postcondition x n p res_1 := by
    intros; expose_names; try simp_all; try grind


prove_correct PowMod by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at *); try (conv => congr <;> simp) ; try expose_names)
  exact (goal_0 p base res invariant_p_pos)
  exact (goal_1 p base require_1)
  exact (goal_2 x n p base exp res invariant_congruence if_pos_1)
  exact (goal_3 p base require_1)
  exact (goal_4 x n p base exp res invariant_congruence if_neg)
  exact (goal_5 p require_1)
  exact (goal_6 x p require_1)
  exact (goal_7 x n p)
  exact (goal_8 x n p i i_1 res_1 a a_1 invariant_congruence done_1)
end Proof
