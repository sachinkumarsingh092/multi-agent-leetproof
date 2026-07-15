import Lean
import Mathlib.Tactic
import Velvet.Std

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

section Assertions
-- Test case 1
#assert_same_evaluation #[(implementation test1_n), test1_Expected]

-- Test case 2
#assert_same_evaluation #[(implementation test2_n), test2_Expected]

-- Test case 3
#assert_same_evaluation #[(implementation test3_n), test3_Expected]

-- Test case 4
#assert_same_evaluation #[(implementation test4_n), test4_Expected]

-- Test case 5
#assert_same_evaluation #[(implementation test5_n), test5_Expected]

-- Test case 6
#assert_same_evaluation #[(implementation test6_n), test6_Expected]

-- Test case 7
#assert_same_evaluation #[(implementation test7_n), test7_Expected]

-- Test case 8
#assert_same_evaluation #[(implementation test8_n), test8_Expected]

-- Test case 9
#assert_same_evaluation #[(implementation test9_n), test9_Expected]
end Assertions

section Proof
theorem correctness_goal_0
    (n : ℕ)
    (h_precond : precondition n)
    : implementation n = (primeSetBelow n).card := by
    sorry

theorem correctness_goal
    (n : Nat)
    (h_precond : precondition n)
    : postcondition n (implementation n) := by
  classical
  unfold postcondition
  have h_eq : implementation n = (primeSetBelow n).card := by
    expose_names; exact (correctness_goal_0 n h_precond)
  have h_le : implementation n ≤ n := by
    by_cases hn : n ≤ 2
    · simp [implementation, hn]
    · -- unfold the definition in the interesting branch
      simp [implementation, hn]
      -- general lemma: foldl increases by at most 1 per step
      have h_foldl_le :
          ∀ (l : List Nat) (init : Nat) (f : Nat → Nat → Nat),
            (∀ acc x, f acc x ≤ acc + 1) →
            List.foldl f init l ≤ init + l.length := by
        intro l
        induction l with
        | nil =>
            intro init f hf
            simp
        | cons x xs ih =>
            intro init f hf
            have h1 : List.foldl f (f init x) xs ≤ f init x + xs.length := ih (f init x) f hf
            have h2 : f init x + xs.length ≤ init + (x :: xs).length := by
              have hx : f init x ≤ init + 1 := hf init x
              have hx' : f init x + xs.length ≤ (init + 1) + xs.length := Nat.add_le_add_right hx xs.length
              simpa [List.length, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hx'
            simpa [List.foldl] using le_trans h1 h2
      -- define the particular fold function
      let f : Nat → Nat → Nat :=
        fun acc i =>
          acc +
            (if
                (List.foldl
                        (fun acc p =>
                          if p < 2 then acc
                          else
                            if n ≤ p * p then acc
                            else
                              if acc.get! p = true then
                                Nat.rec acc
                                  (fun k acc =>
                                    if p * p + k * p < n then acc.setIfInBounds (p * p + k * p) false else acc)
                                  ((n - p * p + p - 1) / p)
                              else acc)
                        (((Array.mkArray n true).setIfInBounds 0 false).setIfInBounds 1 false)
                        (List.range ((n - 1).sqrt + 1))).get!
                    i =
                  true then
              1
            else 0)
      have hf : ∀ acc i, f acc i ≤ acc + 1 := by
        intro acc i
        -- case split on the Bool test
        by_cases h :
            (List.foldl
                    (fun acc p =>
                      if p < 2 then acc
                      else
                        if n ≤ p * p then acc
                        else
                          if acc.get! p = true then
                            Nat.rec acc
                              (fun k acc =>
                                if p * p + k * p < n then acc.setIfInBounds (p * p + k * p) false else acc)
                              ((n - p * p + p - 1) / p)
                          else acc)
                    (((Array.mkArray n true).setIfInBounds 0 false).setIfInBounds 1 false)
                    (List.range ((n - 1).sqrt + 1))).get!
                i =
              true
        · simp [f, h, Nat.add_assoc]
        · simp [f, h, Nat.add_assoc]
      have hmain : List.foldl f 0 (List.range n) ≤ 0 + (List.range n).length :=
        h_foldl_le (List.range n) 0 f hf
      simpa [List.length_range, Nat.zero_add] using hmain
  exact ⟨h_eq, h_le⟩
end Proof
