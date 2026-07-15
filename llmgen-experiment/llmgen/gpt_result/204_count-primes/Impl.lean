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
    204. Count Primes: given a non-negative integer n, return the number of prime numbers strictly less than n.
    **Important: complexity should be O(n log log n) time and O(n) space**
    Natural language breakdown:
    1. The input n is a natural number representing an exclusive upper bound.
    2. A number p is counted iff p is a natural prime (Nat.Prime p) and p < n.
    3. The output is the count of such primes; equivalently, the cardinality of the finite set of primes in {0,1,...,n-1}.
    4. For n ≤ 2, the count is 0 because there are no primes < 2.
    5. The specification characterizes the result purely by set cardinality (no algorithm mandated).
-/

section Specs
-- Helper: the finite set of primes strictly less than n.
-- Using Mathlib's Nat.Prime and Finset.range.
def primeSetBelow (n : Nat) : Finset Nat :=
  (Finset.range n).filter Nat.Prime

def precondition (n : Nat) : Prop :=
  True

def postcondition (n : Nat) (result : Nat) : Prop :=
  result = (primeSetBelow n).card ∧
  result ≤ n
end Specs

section Impl
method CountPrimes (n : Nat)
  return (result : Nat)
  require precondition n
  ensures postcondition n result
  do
  -- Sieve of Eratosthenes: O(n log log n) time, O(n) space.
  if n ≤ 2 then
    return 0
  else
    let mut isPrime : Array Bool := Array.replicate n true

    -- 0 and 1 are not prime (when in range)
    isPrime := isPrime.set! 0 false
    isPrime := isPrime.set! 1 false

    let mut p : Nat := 2
    while p * p < n
      -- Size is preserved by set!
      invariant "cp_outer_size" isPrime.size = n
      -- p starts at 2 and increases by 1 while condition holds
      invariant "cp_outer_p_bounds" 2 ≤ p ∧ p ≤ n
      -- We never update indices 0 or 1 in the sieve loops
      invariant "cp_outer_zero_one" isPrime[0]! = false ∧ isPrime[1]! = false
      -- Soundness: anything marked false is not prime
      invariant "cp_outer_sound" ∀ m, m < n → isPrime[m]! = false → ¬ Nat.Prime m
      -- Marking property for all prime divisors already processed (< p)
      invariant "cp_outer_marked" ∀ d m, Nat.Prime d → d < p → m < n → d * d ≤ m → d ∣ m → isPrime[m]! = false
      -- When the loop finishes (p*p ≥ n), the marking property is sufficient to characterize primes below n
      done_with (∀ m, m < n → (isPrime[m]! = true ↔ Nat.Prime m))
      decreasing n - p
    do
      if isPrime[p]! then
        let mut k : Nat := p * p
        while k < n
          invariant "cp_inner_size" isPrime.size = n
          invariant "cp_inner_p_bounds" 2 ≤ p ∧ p ≤ n
          -- k starts at p*p and increases by p
          invariant "cp_inner_k_lower" p * p ≤ k
          invariant "cp_inner_k_dvd" p ∣ k
          -- Preserve 0/1 markings: k ≥ p*p ≥ 4, so we never write index 0 or 1
          invariant "cp_inner_zero_one" isPrime[0]! = false ∧ isPrime[1]! = false
          -- Preserve soundness and marking info for smaller primes
          invariant "cp_inner_sound" ∀ m, m < n → isPrime[m]! = false → ¬ Nat.Prime m
          invariant "cp_inner_marked_lt_p" ∀ d m, Nat.Prime d → d < p → m < n → d * d ≤ m → d ∣ m → isPrime[m]! = false
          -- Progress for this p: all multiples of p in [p*p, k) have been marked
          invariant "cp_inner_marked_p" ∀ m, m < k → p * p ≤ m → p ∣ m → isPrime[m]! = false
          decreasing n - k
        do
          isPrime := isPrime.set! k false
          k := k + p
      p := p + 1

    let mut count : Nat := 0
    let mut i : Nat := 0
    while i < n
      invariant "cp_count_size" isPrime.size = n
      invariant "cp_count_i_le" i ≤ n
      -- From the outer loop's done_with, isPrime characterizes primality on [0,n)
      invariant "cp_count_sieve_correct" ∀ m, m < n → (isPrime[m]! = true ↔ Nat.Prime m)
      -- count is the number of primes below i
      invariant "cp_count_count_eq" count = (primeSetBelow i).card
      invariant "cp_count_count_le" count ≤ i
      decreasing n - i
    do
      if isPrime[i]! then
        count := count + 1
      i := i + 1

    return count
end Impl

section TestCases
-- Test case 1: example n = 10
-- Primes < 10 are 2,3,5,7 => 4

def test1_n : Nat := 10
def test1_Expected : Nat := 4

-- Test case 2: example n = 0

def test2_n : Nat := 0
def test2_Expected : Nat := 0

-- Test case 3: example n = 1

def test3_n : Nat := 1
def test3_Expected : Nat := 0

-- Test case 4: boundary n = 2

def test4_n : Nat := 2
def test4_Expected : Nat := 0

-- Test case 5: small n = 3, primes < 3 is {2}

def test5_n : Nat := 3
def test5_Expected : Nat := 1

-- Test case 6: small n = 4, primes < 4 are 2,3

def test6_n : Nat := 4
def test6_Expected : Nat := 2

-- Test case 7: small n = 5, primes < 5 are 2,3

def test7_n : Nat := 5
def test7_Expected : Nat := 2

-- Test case 8: moderate n = 20, primes < 20 are 2,3,5,7,11,13,17,19

def test8_n : Nat := 20
def test8_Expected : Nat := 8

-- Test case 9: larger n = 100, known count is 25

def test9_n : Nat := 100
def test9_Expected : Nat := 25
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((CountPrimes test1_n).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((CountPrimes test2_n).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((CountPrimes test3_n).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((CountPrimes test4_n).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((CountPrimes test5_n).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((CountPrimes test6_n).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((CountPrimes test7_n).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((CountPrimes test8_n).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((CountPrimes test9_n).run), DivM.res test9_Expected ]
end Assertions

section Pbt
velvet_plausible_test CountPrimes (config := { maxMs := some 20000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000

theorem goal_0
    (n : ℕ)
    (if_pos : n ≤ OfNat.ofNat 2)
    : postcondition n (OfNat.ofNat 0) := by
  unfold postcondition
  constructor
  · -- show that there are no primes strictly below n when n ≤ 2
    have hEmpty : primeSetBelow n = (∅ : Finset Nat) := by
      unfold primeSetBelow
      apply (Finset.filter_eq_empty_iff).2
      intro x hx
      have hxlt : x < n := Finset.mem_range.mp hx
      have hxlt2 : x < 2 :=
        Nat.lt_of_lt_of_le hxlt (by simpa using if_pos)
      intro hxprime
      exact (Nat.not_lt_of_ge hxprime.two_le) hxlt2
    have hcard : (primeSetBelow n).card = 0 := by
      have hc : (primeSetBelow n).card = (∅ : Finset Nat).card :=
        congrArg Finset.card hEmpty
      exact hc.trans (by simp)
    exact hcard.symm
  · exact Nat.zero_le n

theorem goal_1
    (p : ℕ)
    (k : ℕ)
    (invariant_cp_inner_k_dvd : p ∣ k)
    : p ∣ k := by
    intros; expose_names; try simp_all; try grind

theorem goal_2
    (isPrime : Array Bool)
    (p : ℕ)
    (isPrime_1 : Array Bool)
    (k : ℕ)
    (a_4 : OfNat.ofNat 2 ≤ p)
    (invariant_cp_inner_k_lower : p * p ≤ k)
    (invariant_cp_inner_k_dvd : p ∣ k)
    (invariant_cp_inner_sound : ∀ m < isPrime.size, isPrime_1[m]! = false → ¬Nat.Prime m)
    : ∀ m < isPrime.size, (isPrime_1.setIfInBounds k false)[m]! = false → ¬Nat.Prime m := by
    intro m hm hfalse
    by_cases hmk : m = k
    · cases hmk
      have hp1 : 1 < p := lt_of_lt_of_le (by decide : (1 : Nat) < 2) a_4
      have hp_lt_pp : p < p * p := (Nat.lt_mul_self_iff).2 hp1
      have hp_lt_k : p < k := lt_of_lt_of_le hp_lt_pp invariant_cp_inner_k_lower
      intro hkPrime
      have hdiv := Nat.Prime.eq_one_or_self_of_dvd hkPrime p invariant_cp_inner_k_dvd
      cases hdiv with
      | inl h =>
          exact (ne_of_gt hp1) h
      | inr h =>
          exact (ne_of_lt hp_lt_k) h
    · have hget : (isPrime_1.setIfInBounds k false).get! m = isPrime_1.get! m := by
        simp [Array.get!_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne (Ne.symm hmk)]
      have hfalse' : (isPrime_1.setIfInBounds k false).get! m = false := by
        simpa using hfalse
      have hmfalse : isPrime_1.get! m = false := by
        simpa [hget] using hfalse'
      -- switch back to bracket notation for the invariant
      have hmfalse' : isPrime_1[m]! = false := by
        simpa using hmfalse
      exact invariant_cp_inner_sound m hm hmfalse'

theorem goal_3
    (isPrime : Array Bool)
    (p : ℕ)
    (isPrime_1 : Array Bool)
    (k : ℕ)
    (invariant_cp_inner_k_lower : p * p ≤ k)
    (invariant_cp_inner_k_dvd : p ∣ k)
    (invariant_cp_inner_marked_p : ∀ m < k, p * p ≤ m → p ∣ m → isPrime_1[m]! = false)
    (invariant_cp_inner_size : isPrime_1.size = isPrime.size)
    (if_pos_2 : k < isPrime.size)
    : ∀ m < k + p, p * p ≤ m → p ∣ m → (isPrime_1.setIfInBounds k false)[m]! = false := by
  intro m hm hm_lower hm_dvd
  by_cases hmk : m < k
  · have hfalse : isPrime_1[m]! = false :=
      invariant_cp_inner_marked_p m hmk hm_lower hm_dvd
    have hkne : k ≠ m := Nat.ne_of_gt hmk
    have hmsize : m < isPrime_1.size := by
      have : m < isPrime.size := lt_trans hmk if_pos_2
      simpa [invariant_cp_inner_size] using this
    calc
      (isPrime_1.setIfInBounds k false)[m]! = isPrime_1[m]! := by
        simp [Array.getElem!_eq_getD, Array.getD, Array.getElem?_setIfInBounds_ne hkne,
          Array.getElem_setIfInBounds, hkne, hmsize]
      _ = false := hfalse
  · have hkm : k ≤ m := le_of_not_gt hmk
    have hsub_lt : m - k < p := (Nat.sub_lt_iff_lt_add' hkm).2 hm
    have hdiff_dvd : p ∣ m - k := Nat.dvd_sub hm_dvd invariant_cp_inner_k_dvd
    have hdiff0 : m - k = 0 := Nat.eq_zero_of_dvd_of_lt hdiff_dvd hsub_lt
    have hmk' : m ≤ k := (Nat.sub_eq_zero_iff_le).1 hdiff0
    have hm_eq : m = k := Nat.le_antisymm hmk' hkm
    subst hm_eq
    simp [Array.getElem!_eq_getD, Array.getD, Array.getElem?_setIfInBounds]

theorem goal_4
    (isPrime : Array Bool)
    (p : ℕ)
    (a_4 : OfNat.ofNat 2 ≤ p)
    (if_pos : p * p < isPrime.size)
    : OfNat.ofNat 1 ≤ p ∧ p + OfNat.ofNat 1 ≤ isPrime.size := by
  constructor
  · exact le_trans (by decide : (1 : Nat) ≤ 2) a_4
  · have hp0 : 0 < p := lt_of_lt_of_le Nat.zero_lt_two a_4
    have hp_le_pp : p ≤ p * p := by
      simpa using (Nat.le_mul_of_pos_right p hp0)
    have hp_lt : p < isPrime.size := lt_of_le_of_lt hp_le_pp if_pos
    -- convert strict inequality to successor bound
    simpa [Nat.succ_eq_add_one] using (Nat.succ_le_of_lt hp_lt)

theorem goal_5
    (isPrime : Array Bool)
    (p : ℕ)
    (a_4 : OfNat.ofNat 2 ≤ p)
    (if_pos : p * p < isPrime.size)
    : isPrime.size - (p + OfNat.ofNat 1) < isPrime.size - p := by
    have hp1 : (1 : Nat) ≤ p := by
      exact le_trans (by decide : (1 : Nat) ≤ 2) a_4
    have hp_le : p ≤ p * p := by
      -- multiply the inequality 1 ≤ p by p
      have : p * 1 ≤ p * p := Nat.mul_le_mul_left p hp1
      simpa [Nat.mul_one] using this
    have hp_lt : p < isPrime.size := lt_of_le_of_lt hp_le if_pos
    -- subtracting one more decreases the result
    simpa using (Nat.sub_succ_lt_self isPrime.size p hp_lt)

theorem goal_6
    (isPrime : Array Bool)
    (p : ℕ)
    (a : OfNat.ofNat 2 ≤ p)
    (if_pos : p * p < isPrime.size)
    : OfNat.ofNat 1 ≤ p ∧ p + OfNat.ofNat 1 ≤ isPrime.size := by
    intros; expose_names; exact goal_4 isPrime p a if_pos

theorem goal_7
    (isPrime : Array Bool)
    (p : ℕ)
    (a : OfNat.ofNat 2 ≤ p)
    (invariant_cp_outer_sound : ∀ m < isPrime.size, isPrime[m]! = false → ¬Nat.Prime m)
    (invariant_cp_outer_marked : ∀ (d m : ℕ), Nat.Prime d → d < p → m < isPrime.size → d * d ≤ m → d ∣ m → isPrime[m]! = false)
    (if_pos : p * p < isPrime.size)
    (if_neg_1 : isPrime[p]! = false)
    : ∀ (d m : ℕ), Nat.Prime d → d < p + OfNat.ofNat 1 → m < isPrime.size → d * d ≤ m → d ∣ m → isPrime[m]! = false := by
  intro d m hdPrime hdlt hm hdd hdvd
  have hdle : d ≤ p := by
    have : d < Nat.succ p := by
      simpa [Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hdlt
    exact Nat.lt_succ_iff.mp this
  have hcases : d < p ∨ d = p := lt_or_eq_of_le hdle
  cases hcases with
  | inl hlt =>
      exact invariant_cp_outer_marked d m hdPrime hlt hm hdd hdvd
  | inr heq =>
      -- d = p is impossible since isPrime[p] is false and the array is sound
      have heq' : d = p := by simpa [eq_comm] using heq
      have hpPrime : Nat.Prime p := by simpa [heq'] using hdPrime
      have hp0 : 0 < p := lt_of_lt_of_le (by decide : (0:Nat) < 2) a
      have hp_le_pp : p ≤ p * p := Nat.le_mul_of_pos_right p hp0
      have hp_lt : p < isPrime.size := lt_of_le_of_lt hp_le_pp if_pos
      have hnprime : ¬ Nat.Prime p :=
        invariant_cp_outer_sound p hp_lt (by simpa using if_neg_1)
      exact (False.elim (hnprime hpPrime))

theorem goal_8
    (isPrime : Array Bool)
    (p : ℕ)
    (a : OfNat.ofNat 2 ≤ p)
    (if_pos : p * p < isPrime.size)
    : isPrime.size - (p + OfNat.ofNat 1) < isPrime.size - p := by
    intros; expose_names; exact goal_5 isPrime p a if_pos

theorem goal_9
    (isPrime : Array Bool)
    (p : ℕ)
    (a_2 : isPrime[OfNat.ofNat 0]! = false)
    (a_3 : isPrime[OfNat.ofNat 1]! = false)
    (invariant_cp_outer_sound : ∀ m < isPrime.size, isPrime[m]! = false → ¬Nat.Prime m)
    (invariant_cp_outer_marked : ∀ (d m : ℕ), Nat.Prime d → d < p → m < isPrime.size → d * d ≤ m → d ∣ m → isPrime[m]! = false)
    (if_neg_1 : isPrime.size ≤ p * p)
    : ∀ m < isPrime.size, isPrime[m]! = true ↔ Nat.Prime m := by
  intro m hm
  cases m with
  | zero =>
    -- m = 0
    simp [a_2, Nat.not_prime_zero]
  | succ m =>
    cases m with
    | zero =>
      -- m = 1
      simp [a_3, Nat.not_prime_one]
    | succ m =>
      -- m = m.succ.succ ≥ 2
      set n : ℕ := Nat.succ (Nat.succ m)
      have hn_eq : n = Nat.succ (Nat.succ m) := rfl
      -- rewrite goal in terms of n
      subst n
      constructor
      · intro ht
        -- show n is prime; otherwise it would be marked false
        by_contra hnprime
        let d : ℕ := Nat.minFac (Nat.succ (Nat.succ m))
        have hdprime : Nat.Prime d := by
          -- n ≠ 1 is trivial for n ≥ 2
          simpa [d] using (Nat.minFac_prime (n := Nat.succ (Nat.succ m)) (by simp))
        have hdiv : d ∣ Nat.succ (Nat.succ m) := by
          simpa [d] using (Nat.minFac_dvd (Nat.succ (Nat.succ m)))
        have hdd : d * d ≤ Nat.succ (Nat.succ m) := by
          -- minFac^2 ≤ n
          simpa [d, pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
            (Nat.minFac_sq_le_self (n := Nat.succ (Nat.succ m)) (by simp) hnprime)
        have hmpp : Nat.succ (Nat.succ m) < p * p :=
          lt_of_lt_of_le hm if_neg_1
        have hddlt : d * d < p * p := lt_of_le_of_lt hdd hmpp
        have hdltp : d < p := by
          have : ¬ p ≤ d := by
            intro hpd
            have hp2 : p * p ≤ d * d := Nat.mul_le_mul hpd hpd
            exact (not_lt_of_ge hp2) hddlt
          exact lt_of_not_ge this
        have hmark : isPrime[Nat.succ (Nat.succ m)]! = false :=
          invariant_cp_outer_marked d (Nat.succ (Nat.succ m)) hdprime hdltp hm hdd hdiv
        exact (by simpa [hmark] using ht)
      · intro hprime
        have hne : isPrime[Nat.succ (Nat.succ m)]! ≠ false := by
          intro hfalse
          exact (invariant_cp_outer_sound (Nat.succ (Nat.succ m)) hm hfalse) hprime
        exact eq_true_of_ne_false hne

theorem goal_10
    (n : ℕ)
    : ∀ m < n, (((Array.replicate n true).setIfInBounds (OfNat.ofNat 0) false).setIfInBounds (OfNat.ofNat 1) false)[m]! = false → ¬Nat.Prime m := by
  intro m hm hfalse
  by_cases hm0 : m = 0
  · subst hm0
    exact Nat.not_prime_zero
  by_cases hm1 : m = 1
  · subst hm1
    intro hp
    exact Nat.prime_one_false hp
  -- m is neither 0 nor 1
  have hm0' : (0 : Nat) ≠ m := by
    simpa [eq_comm] using hm0
  have hm1' : (1 : Nat) ≠ m := by
    simpa [eq_comm] using hm1
  have htrue :
      (((Array.replicate n true).setIfInBounds 0 false).setIfInBounds 1 false)[m]! = true := by
    -- reduce get! to getD on getElem?
    simp [Array.get!_eq_getD_getElem?, Array.getElem?_setIfInBounds, Array.getElem?_replicate,
      hm0', hm1', hm]
  have hcontra : False := by
    have : (true : Bool) = false := by
      simpa [htrue] using hfalse
    cases this
  exact False.elim hcontra

theorem goal_11
    (n : ℕ)
    : ∀ (d m : ℕ), Nat.Prime d → d < OfNat.ofNat 2 → m < n → d * d ≤ m → d ∣ m → (((Array.replicate n true).setIfInBounds (OfNat.ofNat 0) false).setIfInBounds (OfNat.ofNat 1) false)[m]! = false := by
    intro d m hdPrime hdlt2 hm hn hdvd
    have h2le : (OfNat.ofNat 2) ≤ d := by
      simpa using hdPrime.two_le
    have : False := by
      exact Nat.not_lt_of_ge h2le hdlt2
    exact False.elim this

theorem goal_12
    (i : Array Bool)
    (p_1 : ℕ)
    (i_2 : ℕ)
    (if_pos_1 : i[i_2]! = true)
    (invariant_cp_count_sieve_correct : ∀ m < i.size, i[m]! = true ↔ Nat.Prime m)
    (if_pos : i_2 < i.size)
    (a : OfNat.ofNat 2 ≤ p_1)
    : (Finset.filter Nat.Prime (Finset.range i_2)).card + OfNat.ofNat 1 = (Finset.filter Nat.Prime (Finset.range (i_2 + OfNat.ofNat 1))).card := by
  have hi2prime : Nat.Prime i_2 :=
    (invariant_cp_count_sieve_correct i_2 if_pos).1 if_pos_1

  have hnotmem : i_2 ∉ Finset.filter Nat.Prime (Finset.range i_2) := by
    simp [Finset.mem_filter, Finset.mem_range]

  have hfilter :
      Finset.filter Nat.Prime (Finset.range (Nat.succ i_2)) =
        insert i_2 (Finset.filter Nat.Prime (Finset.range i_2)) := by
    simp [Finset.range_succ, Finset.filter_insert, hi2prime]

  calc
    (Finset.filter Nat.Prime (Finset.range i_2)).card + 1 =
        (insert i_2 (Finset.filter Nat.Prime (Finset.range i_2))).card := by
      simpa using
        (Finset.card_insert_of_not_mem
              (s := Finset.filter Nat.Prime (Finset.range i_2))
              (a := i_2)
              hnotmem).symm
    _ = (Finset.filter Nat.Prime (Finset.range (Nat.succ i_2))).card := by
      simpa using congrArg Finset.card hfilter.symm
    _ = (Finset.filter Nat.Prime (Finset.range (i_2 + 1))).card := by
      simp [Nat.succ_eq_add_one]

theorem goal_13
    (i : Array Bool)
    (i_2 : ℕ)
    (invariant_cp_count_sieve_correct : ∀ m < i.size, i[m]! = true ↔ Nat.Prime m)
    (if_pos : i_2 < i.size)
    (if_neg_1 : i[i_2]! = false)
    : (Finset.filter Nat.Prime (Finset.range i_2)).card = (Finset.filter Nat.Prime (Finset.range (i_2 + OfNat.ofNat 1))).card := by
  have hnot : ¬ Nat.Prime i_2 := by
    intro hp
    have htrue : i[i_2]! = true := (invariant_cp_count_sieve_correct i_2 if_pos).2 hp
    have : (false : Bool) = true := by
      simpa [if_neg_1] using htrue
    cases this

  -- `range (i_2+1)` adds the single element `i_2`; since `i_2` is not prime, the filter/card doesn't change.
  simpa [Finset.range_add_one, Finset.filter_insert, hnot]


prove_correct CountPrimes by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at *); try (conv => congr <;> simp) ; try expose_names)
  exact (goal_0 n if_pos)
  exact (goal_1 p k invariant_cp_inner_k_dvd)
  exact (goal_2 isPrime p isPrime_1 k a_4 invariant_cp_inner_k_lower invariant_cp_inner_k_dvd invariant_cp_inner_sound)
  exact (goal_3 isPrime p isPrime_1 k invariant_cp_inner_k_lower invariant_cp_inner_k_dvd invariant_cp_inner_marked_p invariant_cp_inner_size if_pos_2)
  exact (goal_4 isPrime p a_4 if_pos)
  exact (goal_5 isPrime p a_4 if_pos)
  exact (goal_6 isPrime p a if_pos)
  exact (goal_7 isPrime p a invariant_cp_outer_sound invariant_cp_outer_marked if_pos if_neg_1)
  exact (goal_8 isPrime p a if_pos)
  exact (goal_9 isPrime p a_2 a_3 invariant_cp_outer_sound invariant_cp_outer_marked if_neg_1)
  exact (goal_10 n)
  exact (goal_11 n)
  exact (goal_12 i p_1 i_2 if_pos_1 invariant_cp_count_sieve_correct if_pos a)
  exact (goal_13 i i_2 invariant_cp_count_sieve_correct if_pos if_neg_1)
end Proof
