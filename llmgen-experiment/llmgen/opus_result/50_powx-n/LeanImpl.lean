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

section Assertions
-- Test case 1
#assert_same_evaluation #[(implementation test1_x test1_n test1_p), test1_Expected]

-- Test case 2
#assert_same_evaluation #[(implementation test2_x test2_n test2_p), test2_Expected]

-- Test case 3
#assert_same_evaluation #[(implementation test3_x test3_n test3_p), test3_Expected]

-- Test case 4
#assert_same_evaluation #[(implementation test4_x test4_n test4_p), test4_Expected]

-- Test case 5
#assert_same_evaluation #[(implementation test5_x test5_n test5_p), test5_Expected]

-- Test case 6
#assert_same_evaluation #[(implementation test6_x test6_n test6_p), test6_Expected]

-- Test case 7
#assert_same_evaluation #[(implementation test7_x test7_n test7_p), test7_Expected]

-- Test case 8
#assert_same_evaluation #[(implementation test8_x test8_n test8_p), test8_Expected]

-- Test case 9
#assert_same_evaluation #[(implementation test9_x test9_n test9_p), test9_Expected]

-- Test case 10
#assert_same_evaluation #[(implementation test10_x test10_n test10_p), test10_Expected]
end Assertions

section Pbt
method implementationPbt (x : Int) (n : Nat) (p : Int)
  return (result : Int)
  require precondition x n p
  ensures postcondition x n p result
  do
  return (implementation x n p)

velvet_plausible_test implementationPbt (config := { maxMs := some 20000 })
end Pbt

section Proof
theorem correctness_goal_0
    (x : ℤ)
    (n : ℕ)
    (p : ℤ)
    (h_precond : precondition x n p)
    (hp_pos : 0 < p)
    (hp_ne : p ≠ 0)
    : ∀ (base : ℤ) (exp : ℕ) (acc : ℤ),
  0 ≤ implementation.go p base exp acc ∧
    implementation.go p base exp acc < p ∧ implementation.go p base exp acc ≡ acc * base ^ exp [ZMOD p] := by
    sorry


theorem correctness_goal
    (x : Int)
    (n : Nat)
    (p : Int)
    (h_precond : precondition x n p)
    : postcondition x n p (implementation x n p) := by
    unfold precondition at h_precond
    unfold postcondition implementation
    have hp_pos : (0 : Int) < p := h_precond
    have hp_ne : p ≠ 0 := Int.ne_of_gt hp_pos
    -- The key invariant: go base exp acc returns a result r with
    -- 0 ≤ r ∧ r < p ∧ Int.ModEq p r (acc * base ^ exp)
    have h_go : ∀ (base : Int) (exp : Nat) (acc : Int),
      0 ≤ (implementation.go p base exp acc) ∧
      (implementation.go p base exp acc) < p ∧
      Int.ModEq p (implementation.go p base exp acc) (acc * base ^ exp) := by expose_names; exact (correctness_goal_0 x n p h_precond hp_pos hp_ne)
    have h_spec := h_go (x % p) n (1 % p)
    obtain ⟨h1, h2, h3⟩ := h_spec
    refine ⟨h1, h2, ?_⟩
    have h_mod_x : Int.ModEq p (x % p) x := by
      unfold Int.ModEq
      rw [Int.emod_emod_of_dvd x (dvd_refl p)]
    have h_mod_1 : Int.ModEq p (1 % p) 1 := by
      unfold Int.ModEq
      rw [Int.emod_emod_of_dvd 1 (dvd_refl p)]
    have h4 : Int.ModEq p (1 % p * (x % p) ^ n) (1 * x ^ n) :=
      Int.ModEq.mul h_mod_1 (Int.ModEq.pow n h_mod_x)
    rw [one_mul] at h4
    exact Int.ModEq.trans h3 h4
end Proof
