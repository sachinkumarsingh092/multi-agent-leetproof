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
def implementation (x : Int) (n : Nat) (p : Int) : Int :=
  -- fast modular exponentiation (repeated squaring)
  -- O(log n) multiplications, tail-recursive loop
  let rec go (base : Int) (exp : Nat) (acc : Int) : Int :=
    match exp with
    | 0 => acc
    | Nat.succ exp' =>
        let acc' := if (Nat.succ exp') % 2 = 1 then (acc * base).emod p else acc
        let base' := (base * base).emod p
        go base' ((Nat.succ exp') / 2) acc'
  termination_by exp
  decreasing_by
    simpa using Nat.div_lt_self (Nat.succ_pos exp') (by decide : 1 < 2)

  let base0 := x.emod p
  let acc0 := (1 : Int).emod p
  go base0 n acc0
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
theorem correctness_goal
    (x : Int)
    (n : Nat)
    (p : Int)
    (h_precond : precondition x n p)
    : postcondition x n p (implementation x n p) := by
  simp [precondition, postcondition, implementation] at h_precond ⊢
  have hp0 : p ≠ 0 := ne_of_gt h_precond

  have emod_modEq (a : Int) : Int.ModEq p (a % p) a := by
    rw [Int.modEq_iff_dvd]
    simpa using (Int.dvd_sub_of_emod_eq (a := a) (b := p) (c := a % p) rfl)

  have go_range :
      ∀ exp base acc,
        0 ≤ acc → acc < p →
          (0 ≤ implementation.go p base exp acc ∧ implementation.go p base exp acc < p) := by
    intro exp
    refine Nat.strongRecOn exp ?_ 
    intro exp ih base acc hacc_nonneg hacc_lt
    cases exp with
    | zero =>
        simpa [implementation.go] using And.intro hacc_nonneg hacc_lt
    | succ exp' =>
        have hk : Nat.succ exp' / 2 < Nat.succ exp' := by
          simpa using Nat.div_lt_self (Nat.succ_pos exp') (by decide : 1 < 2)
        by_cases hodd : (Nat.succ exp') % 2 = 1
        ·
          have hacc'_nonneg : 0 ≤ (acc * base) % p := Int.emod_nonneg _ hp0
          have hacc'_lt : (acc * base) % p < p := Int.emod_lt_of_pos _ h_precond
          have hrec := ih (Nat.succ exp' / 2) hk ((base * base) % p) ((acc * base) % p)
            hacc'_nonneg hacc'_lt
          simpa [implementation.go, hodd] using hrec
        ·
          have hrec := ih (Nat.succ exp' / 2) hk ((base * base) % p) acc hacc_nonneg hacc_lt
          simpa [implementation.go, hodd] using hrec

  have go_modEq :
      ∀ exp base acc,
        Int.ModEq p (implementation.go p base exp acc) (acc * base ^ exp) := by
    intro exp
    refine Nat.strongRecOn exp ?_
    intro exp ih base acc
    cases exp with
    | zero =>
        simp [implementation.go]
    | succ exp' =>
        set e : Nat := Nat.succ exp'
        have hk : e / 2 < e := by
          simpa [e] using Nat.div_lt_self (Nat.succ_pos exp') (by decide : 1 < 2)
        by_cases hodd : e % 2 = 1
        ·
          have hgo := ih (e / 2) hk ((base * base) % p) ((acc * base) % p)
          have hacc' : Int.ModEq p ((acc * base) % p) (acc * base) := emod_modEq (acc * base)
          have hbase' : Int.ModEq p ((base * base) % p) (base * base) := emod_modEq (base * base)
          have hpow : Int.ModEq p (((base * base) % p) ^ (e / 2)) ((base * base) ^ (e / 2)) :=
            Int.ModEq.pow (e / 2) hbase'
          have hmul : Int.ModEq p (((acc * base) % p) * (((base * base) % p) ^ (e / 2)))
              ((acc * base) * ((base * base) ^ (e / 2))) :=
            Int.ModEq.mul hacc' hpow

          have he : e = 2 * (e / 2) + 1 := by
            have h1le : 1 ≤ e := by
              simpa [e] using (Nat.succ_le_succ (Nat.zero_le exp'))
            have h2mul : 2 * (e / 2) = e - 1 := Nat.two_mul_odd_div_two (by simpa [e] using hodd)
            calc
              e = (e - 1) + 1 := (Nat.sub_add_cancel h1le).symm
              _ = 2 * (e / 2) + 1 := by simpa [h2mul]

          have hpowOdd : base ^ (2 * (e / 2) + 1) = base ^ (2 * (e / 2)) * base := by
            simpa [pow_one, Nat.add_assoc] using (pow_add base (2 * (e / 2)) 1)

          have hpowMul2 : (base ^ 2) ^ (e / 2) = base ^ (2 * (e / 2)) := by
            simpa using (pow_mul base 2 (e / 2)).symm

          have halg : (acc * base) * ((base * base) ^ (e / 2)) = acc * base ^ e := by
            calc
              (acc * base) * ((base * base) ^ (e / 2))
                  = (acc * base) * ((base ^ 2) ^ (e / 2)) := by
                      simp [pow_two]
              _ = (acc * base) * (base ^ (2 * (e / 2))) := by
                      simpa [hpowMul2]
              _ = acc * (base ^ (2 * (e / 2)) * base) := by
                      ac_rfl
              _ = acc * base ^ (2 * (e / 2) + 1) := by
                      simpa [hpowOdd, mul_assoc]
              _ = acc * base ^ e := by
                      -- rewrite only the *right* exponent using `he`
                      have : acc * base ^ e = acc * base ^ (2 * (e / 2) + 1) :=
                        congrArg (fun t => acc * base ^ t) he
                      simpa using this.symm

          have hstep : Int.ModEq p (((acc * base) % p) * (((base * base) % p) ^ (e / 2))) (acc * base ^ e) := by
            have : Int.ModEq p (((acc * base) % p) * (((base * base) % p) ^ (e / 2)))
                ((acc * base) * ((base * base) ^ (e / 2))) := hmul
            exact this.trans (by
              simpa [halg] using (Int.ModEq.refl ((acc * base) * ((base * base) ^ (e / 2)))))

          have : Int.ModEq p (implementation.go p base e acc) (acc * base ^ e) := by
            simpa [implementation.go, e, hodd] using (hgo.trans hstep)
          simpa [e] using this
        ·
          have hgo := ih (e / 2) hk ((base * base) % p) acc
          have hbase' : Int.ModEq p ((base * base) % p) (base * base) := emod_modEq (base * base)
          have hpow : Int.ModEq p (((base * base) % p) ^ (e / 2)) ((base * base) ^ (e / 2)) :=
            Int.ModEq.pow (e / 2) hbase'
          have hmul : Int.ModEq p (acc * (((base * base) % p) ^ (e / 2))) (acc * ((base * base) ^ (e / 2))) :=
            Int.ModEq.mul (Int.ModEq.refl acc) hpow

          have h0 : e % 2 = 0 := (Nat.mod_two_ne_one).1 hodd
          have heven : Even e := (Nat.even_iff).2 h0
          have he : e = 2 * (e / 2) := by
            simpa using (Nat.two_mul_div_two_of_even heven).symm

          have hpowMul2 : (base ^ 2) ^ (e / 2) = base ^ (2 * (e / 2)) := by
            simpa using (pow_mul base 2 (e / 2)).symm

          have halg : acc * ((base * base) ^ (e / 2)) = acc * base ^ e := by
            calc
              acc * ((base * base) ^ (e / 2))
                  = acc * ((base ^ 2) ^ (e / 2)) := by
                      simp [pow_two]
              _ = acc * base ^ (2 * (e / 2)) := by
                      simp [hpowMul2]
              _ = acc * base ^ e := by
                      have : acc * base ^ e = acc * base ^ (2 * (e / 2)) :=
                        congrArg (fun t => acc * base ^ t) he
                      simpa using this.symm

          have hstep : Int.ModEq p (acc * (((base * base) % p) ^ (e / 2))) (acc * base ^ e) := by
            have : Int.ModEq p (acc * (((base * base) % p) ^ (e / 2))) (acc * ((base * base) ^ (e / 2))) := hmul
            exact this.trans (by
              simpa [halg] using (Int.ModEq.refl (acc * ((base * base) ^ (e / 2)))))

          have : Int.ModEq p (implementation.go p base e acc) (acc * base ^ e) := by
            simpa [implementation.go, e, hodd] using (hgo.trans hstep)
          simpa [e] using this

  have hacc0_nonneg : 0 ≤ (1 : Int) % p := Int.emod_nonneg _ hp0
  have hacc0_lt : (1 : Int) % p < p := Int.emod_lt_of_pos _ h_precond
  have hrange := go_range n (x % p) ((1 : Int) % p) hacc0_nonneg hacc0_lt

  have hgo0 : Int.ModEq p (implementation.go p (x % p) n ((1 : Int) % p)) (((1 : Int) % p) * (x % p) ^ n) :=
    go_modEq n (x % p) ((1 : Int) % p)

  have hbase0 : Int.ModEq p (x % p) x := emod_modEq x
  have hacc0 : Int.ModEq p ((1 : Int) % p) (1 : Int) := emod_modEq (1 : Int)
  have hpow0 : Int.ModEq p ((x % p) ^ n) (x ^ n) := Int.ModEq.pow n hbase0
  have hmul0 : Int.ModEq p (((1 : Int) % p) * (x % p) ^ n) ((1 : Int) * (x ^ n)) :=
    Int.ModEq.mul hacc0 hpow0
  have htarget : Int.ModEq p (((1 : Int) % p) * (x % p) ^ n) (x ^ n) := by
    simpa using (hmul0.trans (by simpa using (Int.ModEq.refl (x ^ n))))

  have hcongr : Int.ModEq p (implementation.go p (x % p) n ((1 : Int) % p)) (x ^ n) :=
    hgo0.trans htarget

  exact And.intro hrange.1 (And.intro hrange.2 hcongr)
end Proof
