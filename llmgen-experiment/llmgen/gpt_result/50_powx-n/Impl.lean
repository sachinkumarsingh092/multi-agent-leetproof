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
  -- fast modular exponentiation (binary exponentiation)
  -- Complexity: O(log n) multiplications, O(1) extra space.
  let mut base : Int := x % p
  -- normalize base into [0, p)
  if base < 0 then
    base := base + p

  let mut exp : Nat := n
  let mut acc : Int := 1 % p

  while exp > 0
    -- p stays positive throughout (from precondition; never modified)
    invariant "inv_p_pos" p > 0
    -- acc is always normalized into [0, p)
    -- initialization: acc = 1 % p and p > 0; preservation: after each update we re-normalize
    invariant "inv_acc_range" (0 ≤ acc ∧ acc < p)
    -- base is always normalized into [0, p)
    -- initialization: base = x % p and p > 0; preservation: after squaring we re-normalize
    invariant "inv_base_range" (0 ≤ base ∧ base < p)
    -- Main correctness invariant (binary exponentiation): acc * base^exp ≡ x^n (mod p)
    -- exit: exp = 0 implies acc ≡ x^n (mod p) since base^0 = 1
    invariant "inv_modEq" Int.ModEq p (acc * (base ^ exp)) (x ^ n)
    decreasing exp
  do
    if (exp % 2 = 1) then
      acc := (acc * base) % p
      if acc < 0 then
        acc := acc + p

    base := (base * base) % p
    if base < 0 then
      base := base + p

    exp := exp / 2

  return acc
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
    (acc : ℤ)
    (base : ℤ)
    (if_pos_3 : acc * base % p < OfNat.ofNat 0)
    (require_1 : OfNat.ofNat 0 < p)
    : OfNat.ofNat 0 ≤ acc * base % p + p ∧ acc * base % p < OfNat.ofNat 0 := by
    constructor
    · have hp0 : p ≠ 0 := by
        exact ne_of_gt require_1
      have hr : (0 : ℤ) ≤ acc * base % p := by
        -- `%` on Int is Euclidean modulus, hence nonnegative when the modulus is nonzero
        simpa [Int.mul_assoc] using (Int.emod_nonneg (acc * base) hp0)
      have hp : (0 : ℤ) ≤ p := by
        exact le_of_lt require_1
      simpa [Int.add_comm, Int.add_left_comm, Int.add_assoc] using (Int.add_nonneg hr hp)
    · exact if_pos_3

theorem goal_1
    (p : ℤ)
    (base : ℤ)
    (if_pos_4 : base * base % p < OfNat.ofNat 0)
    (require_1 : OfNat.ofNat 0 < p)
    : OfNat.ofNat 0 ≤ base * base % p + p ∧ base * base % p < OfNat.ofNat 0 := by
    intros; expose_names; exact goal_0 p base base if_pos_4 require_1

theorem goal_2
    (x : ℤ)
    (n : ℕ)
    (p : ℤ)
    (acc : ℤ)
    (base : ℤ)
    (exp : ℕ)
    (a : OfNat.ofNat 0 ≤ acc)
    (invariant_inv_modEq : acc * base ^ exp ≡ x ^ n [ZMOD p])
    (if_pos_2 : exp % OfNat.ofNat 2 = OfNat.ofNat 1)
    : (acc * base % p + p) * (base * base % p + p) ^ (exp / OfNat.ofNat 2) ≡ x ^ n [ZMOD p] := by
  have hAcc : acc * base % p + p ≡ acc * base [ZMOD p] := by
    exact
      Int.ModEq.trans (Int.add_modEq_right (a := acc * base % p) (n := p))
        (Int.mod_modEq (acc * base) p)

  have hBase : base * base % p + p ≡ base * base [ZMOD p] := by
    exact
      Int.ModEq.trans (Int.add_modEq_right (a := base * base % p) (n := p))
        (Int.mod_modEq (base * base) p)

  have hMul : (acc * base % p + p) * (base * base % p + p) ^ (exp / 2) ≡
      (acc * base) * (base * base) ^ (exp / 2) [ZMOD p] := by
    exact Int.ModEq.mul hAcc (Int.ModEq.pow (exp / 2) hBase)

  have hexp : exp = 2 * (exp / 2) + 1 := by
    -- `exp = 2*(exp/2) + exp%2` and `exp%2 = 1`
    simpa [if_pos_2] using (Nat.div_add_mod exp 2).symm

  have hEq : acc * base ^ exp = (acc * base) * (base * base) ^ (exp / 2) := by
    calc
      acc * base ^ exp = acc * base ^ (2 * (exp / 2) + 1) := by
        exact congrArg (fun k : Nat => acc * base ^ k) hexp
      _ = acc * (base ^ (2 * (exp / 2)) * base ^ 1) := by
        simp [pow_add, mul_assoc]
      _ = acc * (base ^ (2 * (exp / 2)) * base) := by simp
      _ = acc * (((base ^ 2) ^ (exp / 2)) * base) := by
        -- `base^(2*k) = (base^2)^k`
        simp [pow_mul, mul_assoc]
      _ = acc * (((base * base) ^ (exp / 2)) * base) := by
        simp [pow_two]
      _ = (acc * base) * (base * base) ^ (exp / 2) := by
        simp [mul_assoc, mul_left_comm, mul_comm]

  have hInv' : (acc * base) * (base * base) ^ (exp / 2) ≡ x ^ n [ZMOD p] := by
    simpa [hEq] using invariant_inv_modEq

  exact Int.ModEq.trans hMul hInv'

theorem goal_3
    (p : ℤ)
    (acc : ℤ)
    (base : ℤ)
    (if_pos_3 : acc * base % p < OfNat.ofNat 0)
    (require_1 : OfNat.ofNat 0 < p)
    : OfNat.ofNat 0 ≤ acc * base % p + p ∧ acc * base % p < OfNat.ofNat 0 := by
    intros; expose_names; exact goal_0 p acc base if_pos_3 require_1

theorem goal_4
    (p : ℤ)
    (base : ℤ)
    (invariant_inv_p_pos : OfNat.ofNat 0 < p)
    (if_neg : OfNat.ofNat 0 ≤ base * base % p)
    : OfNat.ofNat 0 ≤ base * base % p ∧ base * base % p < p := by
  intros; expose_names; try simp_all; try grind
  intros; expose_names; try ( simp at * ); try grind
  intros; expose_names; exact?

theorem goal_5
    (x : ℤ)
    (n : ℕ)
    (p : ℤ)
    (acc : ℤ)
    (base : ℤ)
    (exp : ℕ)
    (a : OfNat.ofNat 0 ≤ acc)
    (invariant_inv_modEq : acc * base ^ exp ≡ x ^ n [ZMOD p])
    (if_pos_2 : exp % OfNat.ofNat 2 = OfNat.ofNat 1)
    : (acc * base % p + p) * (base * base % p) ^ (exp / OfNat.ofNat 2) ≡ x ^ n [ZMOD p] := by
  have h2 : (acc * base % p + p) * (base * base % p + p) ^ (exp / OfNat.ofNat 2) ≡ x ^ n [ZMOD p] := by
    simpa using goal_2 x n p acc base exp a invariant_inv_modEq if_pos_2

  have hb : base * base % p ≡ base * base % p + p [ZMOD p] := by
    -- `Int.add_modEq_right` gives `(a + p) ≡ a (mod p)`
    simpa [add_comm, add_left_comm, add_assoc] using
      (Int.add_modEq_right (a := base * base % p) (n := p)).symm

  have hbpow : (base * base % p) ^ (exp / OfNat.ofNat 2) ≡ (base * base % p + p) ^ (exp / OfNat.ofNat 2) [ZMOD p] := by
    exact Int.ModEq.pow (exp / OfNat.ofNat 2) hb

  have hmul : (acc * base % p + p) * (base * base % p) ^ (exp / OfNat.ofNat 2)
      ≡ (acc * base % p + p) * (base * base % p + p) ^ (exp / OfNat.ofNat 2) [ZMOD p] := by
    simpa using Int.ModEq.mul (Int.ModEq.refl (acc * base % p + p)) hbpow

  exact hmul.trans h2

theorem goal_6
    (x : ℤ)
    (n : ℕ)
    (p : ℤ)
    (if_pos : x % p < OfNat.ofNat 0)
    (acc : ℤ)
    (base : ℤ)
    (exp : ℕ)
    (a : OfNat.ofNat 0 ≤ acc)
    (a_1 : acc < p)
    (a_2 : OfNat.ofNat 0 ≤ base)
    (a_3 : base < p)
    (invariant_inv_modEq : acc * base ^ exp ≡ x ^ n [ZMOD p])
    (if_pos_2 : exp % OfNat.ofNat 2 = OfNat.ofNat 1)
    (if_pos_3 : base * base % p < OfNat.ofNat 0)
    (require_1 : OfNat.ofNat 0 < p)
    (invariant_inv_p_pos : OfNat.ofNat 0 < p)
    (if_pos_1 : OfNat.ofNat 0 < exp)
    (if_neg : OfNat.ofNat 0 ≤ acc * base % p)
    : OfNat.ofNat 0 ≤ acc * base % p ∧ acc * base % p < p := by
  intros; expose_names; loom_auto
  intros; expose_names; try simp_all; try grind
  intros; expose_names; exact?

theorem goal_7
    (p : ℤ)
    (base : ℤ)
    (if_pos_3 : base * base % p < OfNat.ofNat 0)
    (require_1 : OfNat.ofNat 0 < p)
    : OfNat.ofNat 0 ≤ base * base % p + p ∧ base * base % p < OfNat.ofNat 0 := by
    intros; expose_names; exact goal_1 p base if_pos_3 require_1

theorem goal_8
    (x : ℤ)
    (n : ℕ)
    (p : ℤ)
    (acc : ℤ)
    (base : ℤ)
    (exp : ℕ)
    (a : OfNat.ofNat 0 ≤ acc)
    (invariant_inv_modEq : acc * base ^ exp ≡ x ^ n [ZMOD p])
    (if_pos_2 : exp % OfNat.ofNat 2 = OfNat.ofNat 1)
    : acc * base % p * (base * base % p + p) ^ (exp / OfNat.ofNat 2) ≡ x ^ n [ZMOD p] := by
  -- Use the already-proved normalized odd-step congruence
  have h_norm : (acc * base % p + p) * (base * base % p + p) ^ (exp / OfNat.ofNat 2) ≡ x ^ n [ZMOD p] :=
    goal_2 x n p acc base exp a invariant_inv_modEq if_pos_2

  -- Adding `p` does not change a value modulo `p`, so we can drop the `+ p` on the accumulator factor.
  have h_drop : acc * base % p * (base * base % p + p) ^ (exp / OfNat.ofNat 2)
      ≡ (acc * base % p + p) * (base * base % p + p) ^ (exp / OfNat.ofNat 2) [ZMOD p] := by
    -- start from `(acc*base%p + p) ≡ (acc*base%p)` and multiply by the common right factor
    have h_add : (acc * base % p + p) ≡ (acc * base % p) [ZMOD p] := by
      simpa using (Int.add_modEq_right (a := acc * base % p) (n := p))
    -- multiply on the right, then flip symmetry to match the desired direction
    simpa [mul_assoc] using (Int.ModEq.mul_right ((base * base % p + p) ^ (exp / OfNat.ofNat 2)) h_add).symm

  exact Int.ModEq.trans h_drop h_norm

theorem goal_9
    (p : ℤ)
    (acc : ℤ)
    (base : ℤ)
    (invariant_inv_p_pos : OfNat.ofNat 0 < p)
    (if_neg : OfNat.ofNat 0 ≤ acc * base % p)
    : OfNat.ofNat 0 ≤ acc * base % p ∧ acc * base % p < p := by
  intros; expose_names; try simp_all; try grind
  intros; expose_names; exact?

theorem goal_10
    (p : ℤ)
    (base : ℤ)
    (require_1 : OfNat.ofNat 0 < p)
    (if_neg_1 : OfNat.ofNat 0 ≤ base * base % p)
    : OfNat.ofNat 0 ≤ base * base % p ∧ base * base % p < p := by
    intros; expose_names; exact goal_9 p base base require_1 if_neg_1

theorem goal_11
    (x : ℤ)
    (n : ℕ)
    (p : ℤ)
    (acc : ℤ)
    (base : ℤ)
    (exp : ℕ)
    (a : OfNat.ofNat 0 ≤ acc)
    (invariant_inv_modEq : acc * base ^ exp ≡ x ^ n [ZMOD p])
    (if_pos_2 : exp % OfNat.ofNat 2 = OfNat.ofNat 1)
    : acc * base % p * (base * base % p) ^ (exp / OfNat.ofNat 2) ≡ x ^ n [ZMOD p] := by
    have h5 : (acc * base % p + p) * (base * base % p) ^ (exp / OfNat.ofNat 2) ≡ x ^ n [ZMOD p] := by
      simpa using (goal_5 x n p acc base exp a invariant_inv_modEq if_pos_2)

    have hacc : acc * base % p + p ≡ acc * base % p [ZMOD p] := by
      simpa using (Int.add_modEq_right (a := acc * base % p) (n := p))

    have hprod : (acc * base % p + p) * (base * base % p) ^ (exp / OfNat.ofNat 2)
        ≡ (acc * base % p) * (base * base % p) ^ (exp / OfNat.ofNat 2) [ZMOD p] := by
      simpa using (Int.ModEq.mul_right ((base * base % p) ^ (exp / OfNat.ofNat 2)) hacc)

    exact hprod.symm.trans h5

theorem goal_12
    (p : ℤ)
    (base : ℤ)
    (if_pos_2 : base * base % p < OfNat.ofNat 0)
    (require_1 : OfNat.ofNat 0 < p)
    : OfNat.ofNat 0 ≤ base * base % p + p ∧ base * base % p < OfNat.ofNat 0 := by
    intros; expose_names; exact goal_1 p base if_pos_2 require_1

theorem goal_13
    (x : ℤ)
    (n : ℕ)
    (p : ℤ)
    (acc : ℤ)
    (base : ℤ)
    (exp : ℕ)
    (a : OfNat.ofNat 0 ≤ acc)
    (invariant_inv_modEq : acc * base ^ exp ≡ x ^ n [ZMOD p])
    (if_neg : exp % OfNat.ofNat 2 = OfNat.ofNat 0)
    : acc * (base * base % p + p) ^ (exp / OfNat.ofNat 2) ≡ x ^ n [ZMOD p] := by
  -- `exp` is even
  have hexp_even : Even exp := (Nat.even_iff).2 (by simpa using if_neg)
  have hExp : 2 * (exp / 2) = exp := Nat.two_mul_div_two_of_even hexp_even

  -- rewrite `(base * base)^(exp/2)` as `base^exp`
  have hPow : (base * base) ^ (exp / 2) = base ^ exp := by
    have hmul : base * base = base ^ 2 := (pow_two base).symm
    calc
      (base * base) ^ (exp / 2) = (base ^ 2) ^ (exp / 2) := by
        simpa [hmul]
      _ = base ^ (2 * (exp / 2)) := by
        simpa using (pow_mul base 2 (exp / 2)).symm
      _ = base ^ exp := by
        simpa [hExp]

  -- normalize the squared base: adding `p` does not change the congruence class mod `p`
  have hAdd : base * base % p + p ≡ base * base % p [ZMOD p] := by
    -- `a + p*1 ≡ a`
    simpa using
      (Int.modEq_add_fac (a := base * base % p) (b := base * base % p) (n := p) (c := (1 : ℤ))
        (Int.ModEq.refl (base * base % p)))

  have hMod : base * base % p ≡ base * base [ZMOD p] := by
    simpa using (Int.mod_modEq (base * base) p)

  have hBase : base * base % p + p ≡ base * base [ZMOD p] := hAdd.trans hMod

  have hBasePow : (base * base % p + p) ^ (exp / 2) ≡ base ^ exp [ZMOD p] := by
    -- raise the congruence `hBase` to the power `exp/2` and rewrite
    simpa [hPow] using (Int.ModEq.pow (exp / 2) hBase)

  have hMul : acc * (base * base % p + p) ^ (exp / 2) ≡ acc * base ^ exp [ZMOD p] := by
    simpa [mul_assoc] using (Int.ModEq.mul_left acc hBasePow)

  exact hMul.trans invariant_inv_modEq

theorem goal_14
    (p : ℤ)
    (base : ℤ)
    (require_1 : OfNat.ofNat 0 < p)
    (if_neg_1 : OfNat.ofNat 0 ≤ base * base % p)
    : OfNat.ofNat 0 ≤ base * base % p ∧ base * base % p < p := by
    intros; expose_names; exact goal_10 p base require_1 if_neg_1

theorem goal_15
    (x : ℤ)
    (n : ℕ)
    (p : ℤ)
    (acc : ℤ)
    (base : ℤ)
    (exp : ℕ)
    (invariant_inv_modEq : acc * base ^ exp ≡ x ^ n [ZMOD p])
    (if_neg : exp % OfNat.ofNat 2 = OfNat.ofNat 0)
    : acc * (base * base % p) ^ (exp / OfNat.ofNat 2) ≡ x ^ n [ZMOD p] := by
  -- Reduce `base * base` modulo `p` (does not change the value modulo `p`).
  have hmod : (base * base % p) ≡ (base * base) [ZMOD p] := by
    simpa using (Int.mod_modEq (base * base) p)

  have hmul : acc * (base * base % p) ^ (exp / 2) ≡ acc * (base * base) ^ (exp / 2) [ZMOD p] := by
    exact Int.ModEq.mul_left acc (Int.ModEq.pow (exp / 2) hmod)

  -- Rewrite the even exponentiation step: (base*base)^(exp/2) = base^exp when exp is even.
  have hPowEq : (base * base) ^ (exp / 2) = base ^ exp := by
    have heven : Even exp := (Nat.even_iff).2 (by simpa using if_neg)
    have hExp : 2 * (exp / 2) = exp := Nat.two_mul_div_two_of_even heven
    calc
      (base * base) ^ (exp / 2)
          = (base ^ 2) ^ (exp / 2) := by simp [pow_two]
      _ = base ^ (2 * (exp / 2)) := by
          simpa using (pow_mul base 2 (exp / 2)).symm
      _ = base ^ exp := by simpa [hExp]

  have hstep : acc * (base * base % p) ^ (exp / 2) ≡ acc * base ^ exp [ZMOD p] := by
    simpa [hPowEq] using hmul

  -- Chain with the loop invariant.
  -- (Also normalize the goal's `/ OfNat.ofNat 2` into `/ 2`.)
  simpa using hstep.trans invariant_inv_modEq

theorem goal_16
    (p : ℤ)
    (require_1 : OfNat.ofNat 0 < p)
    : OfNat.ofNat 0 ≤ OfNat.ofNat 1 % p ∧ OfNat.ofNat 1 % p < p := by
    constructor
    · have hp0 : p ≠ 0 := by
        exact ne_of_gt require_1
      simpa using (Int.emod_nonneg (a := (1 : ℤ)) (b := p) hp0)
    · simpa using (Int.emod_lt_of_pos (a := (1 : ℤ)) (b := p) require_1)

theorem goal_17
    (x : ℤ)
    (p : ℤ)
    (if_pos : x % p < OfNat.ofNat 0)
    (require_1 : OfNat.ofNat 0 < p)
    : OfNat.ofNat 0 ≤ x % p + p ∧ x % p < OfNat.ofNat 0 := by
    
    have h :=
      goal_0 (p := p) (acc := (1 : ℤ)) (base := x)
        (if_pos_3 := by simpa using if_pos) (require_1 := require_1)
    simpa using h

theorem goal_18
    (x : ℤ)
    (n : ℕ)
    (p : ℤ)
    : OfNat.ofNat 1 % p * (x % p + p) ^ n ≡ x ^ n [ZMOD p] := by
  have h1 : (1 : ℤ) % p ≡ (1 : ℤ) [ZMOD p] := by
    simpa using (Int.mod_modEq (1 : ℤ) p)

  have hx : x % p ≡ x [ZMOD p] := by
    simpa using (Int.mod_modEq x p)

  have hp : p ≡ (0 : ℤ) [ZMOD p] := by
    -- `p % p = 0`, and `p % p ≡ p (mod p)`
    simpa using (Int.mod_modEq p p).symm

  have hbase : x % p + p ≡ x [ZMOD p] := by
    have hadd : x % p + p ≡ x + (0 : ℤ) [ZMOD p] := Int.ModEq.add hx hp
    simpa using hadd

  have hpow : (x % p + p) ^ n ≡ x ^ n [ZMOD p] :=
    Int.ModEq.pow n hbase

  have hmul : (1 : ℤ) % p * (x % p + p) ^ n ≡ (1 : ℤ) * x ^ n [ZMOD p] :=
    Int.ModEq.mul h1 hpow

  simpa using hmul

theorem goal_19
    (x : ℤ)
    (n : ℕ)
    (p : ℤ)
    (i : ℤ)
    (i_1 : ℤ)
    (exp_1 : ℕ)
    (a : OfNat.ofNat 0 ≤ i)
    (a_1 : i < p)
    (invariant_inv_modEq : i * i_1 ^ exp_1 ≡ x ^ n [ZMOD p])
    (done_1 : exp_1 = OfNat.ofNat 0)
    : postcondition x n p i := by
    intros; expose_names; try simp_all; try grind

theorem goal_20
    (p : ℤ)
    (acc : ℤ)
    (base : ℤ)
    (if_pos_2 : acc * base % p < OfNat.ofNat 0)
    (require_1 : OfNat.ofNat 0 < p)
    : OfNat.ofNat 0 ≤ acc * base % p + p ∧ acc * base % p < OfNat.ofNat 0 := by
    intros; expose_names; exact goal_0 p acc base if_pos_2 require_1

theorem goal_21
    (p : ℤ)
    (base : ℤ)
    (if_pos_3 : base * base % p < OfNat.ofNat 0)
    (require_1 : OfNat.ofNat 0 < p)
    : OfNat.ofNat 0 ≤ base * base % p + p ∧ base * base % p < OfNat.ofNat 0 := by
    intros; expose_names; exact goal_20 p base base if_pos_3 require_1

theorem goal_22
    (x : ℤ)
    (n : ℕ)
    (p : ℤ)
    (acc : ℤ)
    (base : ℤ)
    (exp : ℕ)
    (a : OfNat.ofNat 0 ≤ acc)
    (invariant_inv_modEq : acc * base ^ exp ≡ x ^ n [ZMOD p])
    (if_pos_1 : exp % OfNat.ofNat 2 = OfNat.ofNat 1)
    : (acc * base % p + p) * (base * base % p + p) ^ (exp / OfNat.ofNat 2) ≡ x ^ n [ZMOD p] := by
    intros; expose_names; exact goal_2 x n p acc base exp a invariant_inv_modEq if_pos_1

theorem goal_23
    (p : ℤ)
    (acc : ℤ)
    (base : ℤ)
    (if_pos_2 : acc * base % p < OfNat.ofNat 0)
    (require_1 : OfNat.ofNat 0 < p)
    : OfNat.ofNat 0 ≤ acc * base % p + p ∧ acc * base % p < OfNat.ofNat 0 := by
    intros; expose_names; exact goal_20 p acc base if_pos_2 require_1

theorem goal_24
    (p : ℤ)
    (base : ℤ)
    (require_1 : OfNat.ofNat 0 < p)
    (if_neg_1 : OfNat.ofNat 0 ≤ base * base % p)
    : OfNat.ofNat 0 ≤ base * base % p ∧ base * base % p < p := by
    intros; expose_names; exact goal_10 p base require_1 if_neg_1

theorem goal_25
    (x : ℤ)
    (n : ℕ)
    (p : ℤ)
    (acc : ℤ)
    (base : ℤ)
    (exp : ℕ)
    (a : OfNat.ofNat 0 ≤ acc)
    (invariant_inv_modEq : acc * base ^ exp ≡ x ^ n [ZMOD p])
    (if_pos_1 : exp % OfNat.ofNat 2 = OfNat.ofNat 1)
    : (acc * base % p + p) * (base * base % p) ^ (exp / OfNat.ofNat 2) ≡ x ^ n [ZMOD p] := by
    intros; expose_names; exact goal_5 x n p acc base exp a invariant_inv_modEq if_pos_1

theorem goal_26
    (p : ℤ)
    (acc : ℤ)
    (base : ℤ)
    (require_1 : OfNat.ofNat 0 < p)
    (if_neg_1 : OfNat.ofNat 0 ≤ acc * base % p)
    : OfNat.ofNat 0 ≤ acc * base % p ∧ acc * base % p < p := by
    intros; expose_names; exact goal_9 p acc base require_1 if_neg_1

theorem goal_27
    (p : ℤ)
    (base : ℤ)
    (if_pos_2 : base * base % p < OfNat.ofNat 0)
    (require_1 : OfNat.ofNat 0 < p)
    : OfNat.ofNat 0 ≤ base * base % p + p ∧ base * base % p < OfNat.ofNat 0 := by
    intros; expose_names; exact goal_20 p base base if_pos_2 require_1

theorem goal_28
    (x : ℤ)
    (n : ℕ)
    (p : ℤ)
    (acc : ℤ)
    (base : ℤ)
    (exp : ℕ)
    (a : OfNat.ofNat 0 ≤ acc)
    (invariant_inv_modEq : acc * base ^ exp ≡ x ^ n [ZMOD p])
    (if_pos_1 : exp % OfNat.ofNat 2 = OfNat.ofNat 1)
    : acc * base % p * (base * base % p + p) ^ (exp / OfNat.ofNat 2) ≡ x ^ n [ZMOD p] := by
    intros; expose_names; exact goal_8 x n p acc base exp a invariant_inv_modEq if_pos_1

theorem goal_29
    (p : ℤ)
    (acc : ℤ)
    (base : ℤ)
    (require_1 : OfNat.ofNat 0 < p)
    (if_neg_1 : OfNat.ofNat 0 ≤ acc * base % p)
    : OfNat.ofNat 0 ≤ acc * base % p ∧ acc * base % p < p := by
    intros; expose_names; exact goal_9 p acc base require_1 if_neg_1

theorem goal_30
    (p : ℤ)
    (base : ℤ)
    (require_1 : OfNat.ofNat 0 < p)
    (if_neg_2 : OfNat.ofNat 0 ≤ base * base % p)
    : OfNat.ofNat 0 ≤ base * base % p ∧ base * base % p < p := by
    intros; expose_names; exact goal_24 p base require_1 if_neg_2

theorem goal_31
    (x : ℤ)
    (n : ℕ)
    (p : ℤ)
    (acc : ℤ)
    (base : ℤ)
    (exp : ℕ)
    (a : OfNat.ofNat 0 ≤ acc)
    (invariant_inv_modEq : acc * base ^ exp ≡ x ^ n [ZMOD p])
    (if_pos_1 : exp % OfNat.ofNat 2 = OfNat.ofNat 1)
    : acc * base % p * (base * base % p) ^ (exp / OfNat.ofNat 2) ≡ x ^ n [ZMOD p] := by
    intros; expose_names; exact goal_11 x n p acc base exp a invariant_inv_modEq if_pos_1

theorem goal_32
    (p : ℤ)
    (base : ℤ)
    (if_pos_1 : base * base % p < OfNat.ofNat 0)
    (require_1 : OfNat.ofNat 0 < p)
    : OfNat.ofNat 0 ≤ base * base % p + p ∧ base * base % p < OfNat.ofNat 0 := by
    intros; expose_names; exact goal_20 p base base if_pos_1 require_1

theorem goal_33
    (x : ℤ)
    (n : ℕ)
    (p : ℤ)
    (acc : ℤ)
    (base : ℤ)
    (exp : ℕ)
    (a : OfNat.ofNat 0 ≤ acc)
    (invariant_inv_modEq : acc * base ^ exp ≡ x ^ n [ZMOD p])
    (if_neg_1 : exp % OfNat.ofNat 2 = OfNat.ofNat 0)
    : acc * (base * base % p + p) ^ (exp / OfNat.ofNat 2) ≡ x ^ n [ZMOD p] := by
    intros; expose_names; exact goal_13 x n p acc base exp a invariant_inv_modEq if_neg_1

theorem goal_34
    (p : ℤ)
    (base : ℤ)
    (require_1 : OfNat.ofNat 0 < p)
    (if_neg_2 : OfNat.ofNat 0 ≤ base * base % p)
    : OfNat.ofNat 0 ≤ base * base % p ∧ base * base % p < p := by
    intros; expose_names; exact goal_30 p base require_1 if_neg_2

theorem goal_35
    (x : ℤ)
    (n : ℕ)
    (p : ℤ)
    (acc : ℤ)
    (base : ℤ)
    (exp : ℕ)
    (invariant_inv_modEq : acc * base ^ exp ≡ x ^ n [ZMOD p])
    (if_neg_1 : exp % OfNat.ofNat 2 = OfNat.ofNat 0)
    : acc * (base * base % p) ^ (exp / OfNat.ofNat 2) ≡ x ^ n [ZMOD p] := by
    intros; expose_names; exact goal_15 x n p acc base exp invariant_inv_modEq if_neg_1

theorem goal_36
    (p : ℤ)
    (require_1 : OfNat.ofNat 0 < p)
    : OfNat.ofNat 0 ≤ OfNat.ofNat 1 % p ∧ OfNat.ofNat 1 % p < p := by
    intros; expose_names; exact goal_16 p require_1

theorem goal_37
    (x : ℤ)
    (p : ℤ)
    (require_1 : OfNat.ofNat 0 < p)
    (if_neg : OfNat.ofNat 0 ≤ x % p)
    : OfNat.ofNat 0 ≤ x % p ∧ x % p < p := by
  intros; expose_names; try ( simp at * ); try grind
  intros; expose_names; try simp_all; try grind
  rw [Int.ModEq.refl]
  intros; expose_names; exact?

theorem goal_38
    (x : ℤ)
    (n : ℕ)
    (p : ℤ)
    : OfNat.ofNat 1 % p * (x % p) ^ n ≡ x ^ n [ZMOD p] := by
    -- Remainders are congruent to the original numbers modulo `p`.
    have h1 : (1 % p : ℤ) ≡ (1 : ℤ) [ZMOD p] := by
      simpa using (Int.mod_modEq (1 : ℤ) p)
    have hx : (x % p : ℤ) ≡ x [ZMOD p] := by
      simpa using (Int.mod_modEq x p)
    have hxpow : (x % p : ℤ) ^ n ≡ x ^ n [ZMOD p] :=
      Int.ModEq.pow n hx
    -- Combine the congruences multiplicatively.
    have hmul : (1 % p : ℤ) * (x % p : ℤ) ^ n ≡ (1 : ℤ) * (x ^ n) [ZMOD p] :=
      Int.ModEq.mul h1 hxpow
    simpa [one_mul] using hmul

theorem goal_39
    (x : ℤ)
    (n : ℕ)
    (p : ℤ)
    (i : ℤ)
    (i_1 : ℤ)
    (exp_1 : ℕ)
    (a : OfNat.ofNat 0 ≤ i)
    (a_1 : i < p)
    (invariant_inv_modEq : i * i_1 ^ exp_1 ≡ x ^ n [ZMOD p])
    (done_1 : exp_1 = OfNat.ofNat 0)
    : postcondition x n p i := by
    intros; expose_names; try simp_all; try grind


prove_correct PowMod by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at *); try (conv => congr <;> simp) ; try expose_names)
  exact (goal_0 p acc base if_pos_3 require_1)
  exact (goal_1 p base if_pos_4 require_1)
  exact (goal_2 x n p acc base exp a invariant_inv_modEq if_pos_2)
  exact (goal_3 p acc base if_pos_3 require_1)
  exact (goal_4 p base invariant_inv_p_pos if_neg)
  exact (goal_5 x n p acc base exp a invariant_inv_modEq if_pos_2)
  exact (goal_6 x n p if_pos acc base exp a a_1 a_2 a_3 invariant_inv_modEq if_pos_2 if_pos_3 require_1 invariant_inv_p_pos if_pos_1 if_neg)
  exact (goal_7 p base if_pos_3 require_1)
  exact (goal_8 x n p acc base exp a invariant_inv_modEq if_pos_2)
  exact (goal_9 p acc base invariant_inv_p_pos if_neg)
  exact (goal_10 p base require_1 if_neg_1)
  exact (goal_11 x n p acc base exp a invariant_inv_modEq if_pos_2)
  exact (goal_12 p base if_pos_2 require_1)
  exact (goal_13 x n p acc base exp a invariant_inv_modEq if_neg)
  exact (goal_14 p base require_1 if_neg_1)
  exact (goal_15 x n p acc base exp invariant_inv_modEq if_neg)
  exact (goal_16 p require_1)
  exact (goal_17 x p if_pos require_1)
  exact (goal_18 x n p)
  exact (goal_19 x n p i i_1 exp_1 a a_1 invariant_inv_modEq done_1)
  exact (goal_20 p acc base if_pos_2 require_1)
  exact (goal_21 p base if_pos_3 require_1)
  exact (goal_22 x n p acc base exp a invariant_inv_modEq if_pos_1)
  exact (goal_23 p acc base if_pos_2 require_1)
  exact (goal_24 p base require_1 if_neg_1)
  exact (goal_25 x n p acc base exp a invariant_inv_modEq if_pos_1)
  exact (goal_26 p acc base require_1 if_neg_1)
  exact (goal_27 p base if_pos_2 require_1)
  exact (goal_28 x n p acc base exp a invariant_inv_modEq if_pos_1)
  exact (goal_29 p acc base require_1 if_neg_1)
  exact (goal_30 p base require_1 if_neg_2)
  exact (goal_31 x n p acc base exp a invariant_inv_modEq if_pos_1)
  exact (goal_32 p base if_pos_1 require_1)
  exact (goal_33 x n p acc base exp a invariant_inv_modEq if_neg_1)
  exact (goal_34 p base require_1 if_neg_2)
  exact (goal_35 x n p acc base exp invariant_inv_modEq if_neg_1)
  exact (goal_36 p require_1)
  exact (goal_37 x p require_1 if_neg)
  exact (goal_38 x n p)
  exact (goal_39 x n p i i_1 exp_1 a a_1 invariant_inv_modEq done_1)
end Proof
