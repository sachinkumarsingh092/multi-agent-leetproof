import Lean

import Mathlib.Tactic

set_option maxHeartbeats 10000000

section Specs
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false
set_option pp.funBinderTypes true

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
def powMod (base : Int) (exp : Nat) (p : Int) : Int :=
  match exp with
  | 0 => 1 % p
  | n + 1 =>
    if n + 1 == 1 then base % p
    else
      let half := powMod base (n / 2 + (if n % 2 == 0 then 0 else 0)) p
      if (n + 1) % 2 == 0 then
        (half * half) % p
      else
        (half * half % p * base) % p
termination_by exp

def implementation (x : Int) (n : Nat) (p : Int) : Int :=
  let rec go (base : Int) (exp : Nat) (acc : Int) : Int :=
    match exp with
    | 0 => acc % p
    | e + 1 =>
      let base' := base % p
      let acc' := if (e + 1) % 2 == 1 then (acc * base') % p else acc
      go ((base' * base') % p) ((e + 1) / 2) acc'
  termination_by exp
  go (x % p) n (1 % p)
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

section Proof

/-
PROVIDED SOLUTION
Prove by strong induction on `exp` using the `termination_by` measure.

Base case (exp = 0): `go p base 0 acc = acc % p`.
- Range: `0 ≤ acc % p` by `Int.emod_nonneg` and `acc % p < p` by `Int.emod_lt_of_pos`.
- Congruence: `acc % p ≡ acc [ZMOD p]` which equals `acc * base^0 = acc * 1 = acc`. Use `Int.ModEq` which is defined as `a % p = b % p`, so `(acc % p) % p = acc % p = (acc * 1) % p`.

Recursive case (exp = e + 1): `go` computes base' = base % p, then branches on parity.
- The key recursive call is `go ((base' * base') % p) ((e+1)/2) acc'` where acc' depends on parity.
- By IH (which applies since `(e+1)/2 < e+1`), the result satisfies range and `≡ acc' * ((base' * base') % p)^((e+1)/2) [ZMOD p]`.
- Since `(base' * base') % p ≡ base^2 [ZMOD p]` and `Int.ModEq` is compatible with `pow`, the result `≡ acc' * base^(2*((e+1)/2)) [ZMOD p]`.
- If odd: acc' = (acc * base') % p ≡ acc * base [ZMOD p], and `1 + 2*((e+1)/2) = e+1` (since e+1 is odd, (e+1)/2 = e/2, so 2*(e/2)+1 = e+1). Result ≡ acc * base * base^(2*(e/2)) = acc * base^(e+1).
- If even: acc' = acc, and `2*((e+1)/2) = e+1`. Result ≡ acc * base^(e+1).

Try using `intro base exp acc`, then `induction exp using Nat.strong_rec_on` or just unfold the definition and use the well-founded recursion.

Key Mathlib lemmas: `Int.emod_nonneg`, `Int.emod_lt_of_pos`, `Int.ModEq`, `Int.emod_emod_of_dvd`, `Int.mul_emod`, `Int.pow_emod`.
-/
theorem correctness_goal_0 (x : ℤ) (n : ℕ) (p : ℤ) (h_precond : precondition x n p) (hp_pos : 0 < p) (hp_ne : p ≠ 0) : ∀ (base : ℤ) (exp : ℕ) (acc : ℤ),
  0 ≤ implementation.go p base exp acc ∧
    implementation.go p base exp acc < p ∧ implementation.go p base exp acc ≡ acc * base ^ exp [ZMOD p] := by
    intros base exp acc; induction' exp using Nat.strong_induction_on with exp ih generalizing base acc; rcases Nat.even_or_odd' exp with ⟨ k, rfl | rfl ⟩ <;> norm_num [ pow_add, pow_mul, Nat.even_iff, Nat.odd_iff ] ;
    · -- By definition of `implementation.go`, we can rewrite the goal in terms of the induction hypothesis.
      have h_go_even : implementation.go p base (2 * k) acc = if 2 * k = 0 then acc % p else (implementation.go p ((base % p) * (base % p) % p) k (if 2 * k % 2 = 1 then (acc * (base % p)) % p else acc)) := by
        cases k <;> simp +decide [ *, Nat.mul_succ ] at *;
        · unfold implementation.go; aesop;
        · rw [ implementation.go ] ; simp +decide [ *, Nat.mul_succ ] ; ring;
          norm_num [ Nat.add_div ] ; ring;
      by_cases hk : k = 0 <;> simp_all +decide [ Int.ModEq ];
      · exact ⟨ Int.emod_nonneg _ hp_ne, Int.emod_lt_of_pos _ hp_pos ⟩;
      · convert ih k ( by linarith [ Nat.pos_of_ne_zero hk ] ) ( base % p * ( base % p ) % p ) acc using 1 ; ring;
        norm_num [ pow_mul', Int.mul_emod, pow_two ];
        simp +decide [ ← Int.mul_emod, pow_succ ];
        exact fun _ => by rw [ Int.ModEq.mul_left _ ( Int.ModEq.pow _ ( Int.emod_emod _ _ ) ) ] ;
    · specialize ih k ( by linarith ) ( base % p * ( base % p ) % p ) ( acc * ( base % p ) % p ) ; simp_all +decide [ pow_succ, pow_mul, ← ZMod.intCast_eq_intCast_iff ] ;
      unfold implementation.go; simp_all +decide [ ← ZMod.intCast_eq_intCast_iff, mul_assoc, mul_comm, mul_left_comm, pow_succ, pow_mul ] ;
      norm_num [ Nat.add_div, Int.ModEq, Int.mul_emod, pow_succ, pow_mul ] at *;
      simp_all +decide [ ← Int.mul_emod, ← Int.mul_assoc ];
      simp +decide [ mul_assoc, mul_comm, mul_left_comm, Int.mul_emod, pow_succ ];
      simp +decide [ ← Int.mul_emod, ← Int.mul_assoc ];
      exact Int.ModEq.mul_left _ ( Int.ModEq.pow _ ( Int.emod_emod _ _ ) )

end Proof