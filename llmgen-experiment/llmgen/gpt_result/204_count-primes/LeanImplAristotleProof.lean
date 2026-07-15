/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: a6bdc02d-f010-4d7d-a75c-6c5ff642a2eb

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem correctness_goal_0 (n : ℕ) (h_precond : precondition n) : implementation n = (primeSetBelow n).card
-/

import Lean

import Mathlib.Tactic


set_option maxHeartbeats 10000000

section Specs

-- Never add new imports here

set_option maxHeartbeats 10000000

set_option pp.coercions false

set_option pp.funBinderTypes true

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

def implementation (n : Nat) : Nat :=
  -- Pure functional sieve of Eratosthenes using an Array Bool.
  -- Space: O(n). Marking work: sum_{p prime ≤ sqrt n} n/p = O(n log log n).
  if n ≤ 2 then
    0
  else
    let init : Array Bool :=
      ((Array.mkArray n true).set! 0 false).set! 1 false

    -- Mark multiples of p starting from j, for exactly `steps` iterations.
    -- We choose `steps = (n - j + p - 1) / p`, so we do O(n/p) work.
    let markSteps (arr : Array Bool) (p j steps : Nat) : Array Bool :=
      Nat.rec (motive := fun _ => Array Bool)
        arr
        (fun k acc =>
          let idx := j + k * p
          if h : idx < n then
            acc.set! idx false
          else
            acc)
        steps

    let limit : Nat := Nat.sqrt (n - 1)

    let sieve : Array Bool :=
      (List.range (limit + 1)).foldl
        (fun acc p =>
          if p < 2 then
            acc
          else if p * p ≥ n then
            acc
          else if acc.get! p then
            let start := p * p
            let steps := (n - start + p - 1) / p
            markSteps acc p start steps
          else
            acc)
        init

    (List.range n).foldl (fun acc i => acc + (if sieve.get! i then 1 else 0)) 0

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

section Proof

noncomputable section AristotleLemmas

/-
We define the sieve invariant `SieveInv` and a helper function `markSteps_aux` which mirrors the inner loop of the sieve. We then state a lemma `markSteps_spec` characterizing the behavior of `markSteps_aux`.
-/
section Helpers

def SieveInv (n : Nat) (p : Nat) (arr : Array Bool) : Prop :=
  arr.size = n ∧
  ∀ i < n, arr.get! i = true ↔ (2 ≤ i ∧ ∀ q < p, Nat.Prime q → q ∣ i → q = i)

def markSteps_aux (n : Nat) (arr : Array Bool) (p j steps : Nat) : Array Bool :=
  Nat.rec (motive := fun _ => Array Bool)
    arr
    (fun k acc =>
      let idx := j + k * p
      if h : idx < n then
        acc.set! idx false
      else
        acc)
    steps

lemma markSteps_spec (arr : Array Bool) (p j steps : Nat) (n : Nat)
    (h_sz : arr.size = n) :
    let res := markSteps_aux n arr p j steps
    res.size = n ∧
    ∀ i < n, res.get! i = (if (∃ k < steps, i = j + k * p) then false else arr.get! i) := by
  induction' steps with steps ih generalizing arr j <;> simp_all +decide [ markSteps_aux ];
  split_ifs <;> simp_all +decide [ Nat.lt_succ_iff ];
  · intro i hi; specialize ih arr j h_sz; simp_all +decide [ Array.get! ] ;
    by_cases hi' : i = j + steps * p <;> simp_all +decide [ Array.getElem_setIfInBounds ];
    · exact fun h => False.elim <| h steps le_rfl |>.1 rfl;
    · simp_all +decide [ eq_comm, Nat.lt_succ_iff ];
      convert ih i hi using 1;
      congr! 2;
      exact if_congr ( by exact ⟨ fun ⟨ k, hk₁, hk₂ ⟩ => ⟨ k, lt_of_le_of_ne hk₁ ( by aesop ), hk₂ ⟩, fun ⟨ k, hk₁, hk₂ ⟩ => ⟨ k, le_of_lt hk₁, hk₂ ⟩ ⟩ ) rfl rfl;
  · intro i hi; by_cases hi' : ∃ k < steps, i = j + k * p <;> simp_all +decide [ Nat.lt_succ_iff ] ;
    · exact fun h => False.elim <| h _ hi'.choose_spec.1.le hi'.choose_spec.2;
    · congr! 2;
      by_cases h : ∃ k ≤ steps, i = j + k * p <;> simp_all +decide [ Nat.lt_succ_iff ];
      · exact h.imp fun x hx => ⟨ lt_of_le_of_ne hx.1 ( by rintro rfl; exact hi' 0 ( by linarith ) ( by linarith ) ), hx.2 ⟩;
      · exact iff_of_false ( fun ⟨ k, hk₁, hk₂ ⟩ => hi' k hk₁ hk₂ ) ( fun ⟨ k, hk₁, hk₂ ⟩ => h k hk₁ hk₂ )

end Helpers

/-
We define `sieve_step` and prove `sieve_step_inv`. The proof considers four cases: `p < 2`, `p * p ≥ n`, `acc[p] = true`, and `acc[p] = false`. In each case, we show that the invariant `SieveInv` is preserved when moving from `p` to `p + 1`.
-/
section SieveSteps

def sieve_step (n : Nat) (acc : Array Bool) (p : Nat) : Array Bool :=
  if p < 2 then
    acc
  else if p * p ≥ n then
    acc
  else if acc.get! p then
    let start := p * p
    let steps := (n - start + p - 1) / p
    markSteps_aux n acc p start steps
  else
    acc

lemma sieve_step_inv (n : Nat) (p : Nat) (acc : Array Bool)
    (h_inv : SieveInv n p acc) :
    SieveInv n (p + 1) (sieve_step n acc p) := by
  unfold sieve_step
  split_ifs with h_lt_2 h_sq_ge h_prime
  · -- Case p < 2
    rcases p with ( _ | _ | p ) <;> simp_all +arith +decide [ SieveInv ];
    intro i hi hi' q hq hq' hq''; interval_cases q <;> trivial;
  · -- Case p * p >= n
    obtain ⟨ h₁, h₂ ⟩ := h_inv;
    refine' ⟨ h₁, fun i hi => _ ⟩;
    constructor <;> intro h <;> simp_all +decide [ Nat.lt_succ_iff ];
    · -- If $q = p$, then since $p^2 \geq n$, we have $p \mid i$ implies $i \geq p^2$, which contradicts $i < n$.
      intros q hq hq_prime hq_div
      by_cases hq_eq_p : q = p;
      · obtain ⟨ k, hk ⟩ := hq_div;
        rcases k with ( _ | _ | k ) <;> simp_all +decide [ Nat.prime_mul_iff ];
        contrapose! h;
        exact fun _ => ⟨ Nat.minFac ( k + 1 + 1 ), Nat.lt_of_le_of_lt ( Nat.minFac_le ( by linarith ) ) ( by nlinarith ), Nat.minFac_prime ( by linarith ), dvd_mul_of_dvd_right ( Nat.minFac_dvd _ ) _, by nlinarith [ Nat.minFac_le ( by linarith : k + 1 + 1 ≥ 1 ) ] ⟩;
      · exact h.2 q ( lt_of_le_of_ne hq hq_eq_p ) hq_prime hq_div;
    · exact fun q hq hq' hq'' => h.2 q hq.le hq' hq''
  · -- Case acc[p] = true
    -- By definition of `markSteps_aux`, we know that the elements at indices `p*p + k*p` for `k < steps` are set to `false`.
    have h_marked : ∀ i < n, (markSteps_aux n acc p (p * p) ((n - p * p + p - 1) / p)).get! i = (if (∃ k < (n - p * p + p - 1) / p, i = p * p + k * p) then false else acc.get! i) := by
      convert markSteps_spec acc p ( p * p ) ( ( n - p * p + p - 1 ) / p ) n h_inv.1 |> And.right using 1;
    refine' ⟨ _, _ ⟩ <;> simp_all +decide [ SieveInv ];
    · have := markSteps_spec acc p ( p * p ) ( ( n - p * p + p - 1 ) / p ) n; aesop;
    · intro i hi; constructor <;> intro h <;> simp_all +decide [ Nat.lt_succ_iff ] ;
      · -- Since $q \leq p$ and $q \neq p$, we have $q < p$.
        intros q hq hq_prime hq_div
        by_cases hq_eq_p : q = p;
        · obtain ⟨ k, hk ⟩ := hq_div; simp_all +decide [ Nat.prime_mul_iff ] ;
          contrapose! h;
          intro h₁ h₂; use Nat.minFac k; refine' ⟨ _, Nat.minFac_prime _, Nat.dvd_trans ( Nat.minFac_dvd _ ) ( dvd_mul_left _ _ ), _ ⟩ <;> rcases k with ( _ | _ | k ) <;> simp_all +decide [ Nat.prime_mul_iff ] ;
          · exact lt_of_le_of_lt ( Nat.minFac_le ( by linarith ) ) ( by contrapose! h₁; exact ⟨ k + 1 + 1 - p, by
              rw [ Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hq_prime.pos ] ; nlinarith only [ hi, h₁, Nat.sub_add_cancel ( by nlinarith : p ≤ k + 1 + 1 ), Nat.sub_add_cancel ( by nlinarith : p * p ≤ n ), Nat.sub_add_cancel ( by nlinarith [ Nat.sub_add_cancel ( by nlinarith : p * p ≤ n ) ] : 1 ≤ n - p * p + p ) ] ;, by
              nlinarith only [ Nat.sub_add_cancel h₁ ] ⟩ );
          · exact ne_of_lt ( lt_of_le_of_lt ( Nat.minFac_le ( by linarith ) ) ( by nlinarith only [ h_lt_2 ] ) );
        · exact h.2.2 q ( lt_of_le_of_ne hq hq_eq_p ) hq_prime hq_div ▸ rfl;
      · constructor <;> intros <;> simp_all +decide [ Nat.dvd_iff_mod_eq_zero ] ;
        · rintro rfl;
          contrapose! h;
          exact fun _ => ⟨ Nat.minFac p, Nat.minFac_le ( by linarith ), Nat.minFac_prime ( by linarith ), Nat.mod_eq_zero_of_dvd ( dvd_add ( dvd_mul_of_dvd_left ( Nat.minFac_dvd p ) _ ) ( dvd_mul_of_dvd_right ( Nat.minFac_dvd p ) _ ) ), by nlinarith [ Nat.minFac_le ( by linarith : 1 ≤ p ) ] ⟩;
        · exact h.2 _ ( Nat.le_of_lt ‹_› ) ‹_› ‹_› ▸ rfl
  · -- Case acc[p] = false
    refine' ⟨ h_inv.1, fun i hi => _ ⟩;
    apply Iff.intro;
    · intro hi_true
      have h_prime_i : 2 ≤ i ∧ ∀ q < p, Nat.Prime q → q ∣ i → q = i := by
        exact h_inv.2 i hi |>.1 hi_true;
      refine ⟨ h_prime_i.1, fun q hq hq' hq'' => ?_ ⟩;
      cases lt_or_eq_of_le ( Nat.le_of_lt_succ hq ) <;> simp_all +decide [ Nat.prime_dvd_prime_iff_eq ];
      · exact h_prime_i.2 q ‹_› hq' hq'';
      · have := h_inv.2 p ( by nlinarith ) ; simp_all +decide [ Nat.prime_dvd_prime_iff_eq ] ;
    · simp +zetaDelta at *;
      exact fun hi₁ hi₂ => h_inv.2 i hi |>.2 ⟨ hi₁, fun q hq₁ hq₂ hq₃ => hi₂ q ( Nat.lt_succ_of_lt hq₁ ) hq₂ hq₃ ⟩

end SieveSteps

/-
We prove `sieve_fold_inv` by induction on `limit`. The base case establishes that the initial array satisfies `SieveInv n 0`. The inductive step uses `sieve_step_inv` to show that if the invariant holds for `k`, it holds for `k+1` after applying `sieve_step`.
-/
lemma sieve_fold_inv (n : Nat) (limit : Nat) :
    let init := ((Array.mkArray n true).set! 0 false).set! 1 false
    let sieve := (List.range (limit + 1)).foldl (sieve_step n) init
    SieveInv n (limit + 1) sieve := by
      induction' limit with limit ih;
      · unfold SieveInv;
        rcases n with ( _ | _ | n ) <;> simp_all +decide [ Array.mkArray ];
        unfold sieve_step; simp +arith +decide [ Array.get! ] ;
        grind +ring;
      · convert sieve_step_inv n ( limit + 1 ) _ ih using 1;
        simp +decide [ List.range_succ ]

/-
We prove that if the sieve invariant holds for `limit = sqrt(n-1)`, then `sieve.get! i` is true if and only if `i` is prime, for all `i < n`. This relies on the fact that any composite number `i` has a prime factor `q ≤ sqrt(i) ≤ limit`.
-/
lemma sieve_iff_prime (n : Nat) (sieve : Array Bool) (limit : Nat)
    (h_inv : SieveInv n (limit + 1) sieve)
    (h_limit : limit = Nat.sqrt (n - 1)) :
    ∀ i < n, sieve.get! i = true ↔ Nat.Prime i := by
      intro i hi
      rw [h_inv.right i hi];
      constructor <;> intro h;
      · contrapose! h;
        intro hi2
        obtain ⟨q, hq_prime, hq_div⟩ : ∃ q, Nat.Prime q ∧ q ∣ i ∧ q ≤ Nat.sqrt i := by
          obtain ⟨ q, hq₁, hq₂ ⟩ := Nat.exists_prime_and_dvd ( by linarith : i ≠ 1 );
          obtain ⟨ k, rfl ⟩ := hq₂;
          exact ⟨ Nat.minFac ( q * k ), Nat.minFac_prime ( by linarith ), Nat.minFac_dvd _, by rw [ Nat.le_sqrt ] ; nlinarith [ Nat.minFac_le_of_dvd ( Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨ by aesop_cat, by aesop_cat ⟩ ) ( dvd_mul_right q k ), Nat.minFac_le_of_dvd ( Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨ by aesop_cat, by aesop_cat ⟩ ) ( dvd_mul_left k q ) ] ⟩;
        exact ⟨ q, Nat.lt_succ_of_le ( h_limit.symm ▸ Nat.le_trans hq_div.2 ( Nat.sqrt_le_sqrt ( Nat.le_sub_one_of_lt hi ) ) ), hq_prime, hq_div.1, by rintro rfl; exact h hq_prime ⟩;
      · exact ⟨ h.two_le, fun q hq hq' hq'' => by have := Nat.prime_dvd_prime_iff_eq hq' h; tauto ⟩

end AristotleLemmas

theorem correctness_goal_0 (n : ℕ) (h_precond : precondition n) : implementation n = (primeSetBelow n).card := by
    by_cases hn : n > 2;
    · -- Let's establish that the sieve computed in `implementation` satisfies `SieveInv`.
      have h_sieve_inv : SieveInv n (Nat.sqrt (n - 1) + 1) (List.foldl (sieve_step n) ((Array.mkArray n true).set! 0 false |>.set! 1 false) (List.range (Nat.sqrt (n - 1) + 1))) := by
        exact?;
      -- By definition of `implementation`, we know that it counts the number of true values in the sieve array.
      have h_count : (List.foldl (fun acc i => acc + (if (List.foldl (sieve_step n) ((Array.mkArray n true).set! 0 false |>.set! 1 false) (List.range (Nat.sqrt (n - 1) + 1))).get! i then 1 else 0)) 0 (List.range n)) = (primeSetBelow n).card := by
        have h_count : ∀ i < n, (List.foldl (sieve_step n) ((Array.mkArray n true).set! 0 false |>.set! 1 false) (List.range (Nat.sqrt (n - 1) + 1))).get! i = true ↔ Nat.Prime i := by
          exact?;
        -- By definition of `primeSetBelow`, we know that its cardinality is equal to the number of primes less than `n`.
        have h_primeSetBelow_card : (primeSetBelow n).card = Finset.card (Finset.filter (fun i => Nat.Prime i) (Finset.range n)) := by
          rfl;
        rw [ h_primeSetBelow_card, Finset.card_filter ];
        rw [ Finset.sum_eq_multiset_sum ];
        erw [ Multiset.map_coe ];
        rw [ show List.range n = List.map ( fun i : Fin n => i.val ) ( List.finRange n ) from ?_, List.foldl_map ];
        · induction' ( List.finRange n ) using List.reverseRecOn with i hi <;> aesop;
        · exact List.ext_get ( by simp +decide ) ( by simp +decide );
      unfold implementation;
      rw [ if_neg ( by linarith ), ← h_count ];
      unfold sieve_step; aesop;
    · interval_cases n <;> native_decide

end Proof