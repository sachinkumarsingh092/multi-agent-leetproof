import Velvet.Std
import Extensions.Tactics
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false
set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

/- Problem Description
    459. Repeated Substring Pattern: decide whether a character sequence is a repetition of a shorter contiguous substring.
    **Important: complexity should be O(n^1.5) time and O(n) space**
    Natural language breakdown:
    1. Input is a sequence of characters s.
    2. We ask whether there exists a non-empty proper prefix length k (0 < k < n) such that n is a multiple of k.
    3. If such k exists, s is exactly repetitions of its first k characters iff every character at index i equals the character at index (i mod k).
    4. The output is a Bool: true exactly when such a k exists; otherwise false.
    5. For empty or length-1 inputs, the answer is false because no non-empty proper substring can repeat to form s.
-/

section Specs
-- A property-based characterization of being a repetition of a shorter block.
-- We avoid constructing the repeated string; instead we specify periodicity by modular indexing.

def precondition (s : List Char) : Prop :=
  True

def postcondition (s : List Char) (result : Bool) : Prop :=
  let n := s.length
  (result = true) ↔
    (∃ k : Nat,
      0 < k ∧
      k < n ∧
      n % k = 0 ∧
      (∀ i : Nat, i < n → s[i]! = s[i % k]!))
end Specs

section Impl
method RepeatedSubstringPattern (s : List Char)
  return (result : Bool)
  require precondition s
  ensures postcondition s result
  do
  let n : Nat := s.length
  if n ≤ 1 then
    return false
  else
    -- We search for a period k. To satisfy total-correctness termination checks,
    -- we use a loop counter `t` that always decreases.
    let mut k : Nat := 1
    let mut t : Nat := n - 1
    let mut found : Bool := false

    while (t > 0) ∧ (found = false)
      -- Bounds / lockstep for the search variables
      invariant "inv_outer_bounds" (1 ≤ k) ∧ (k ≤ n)
      invariant "inv_outer_lockstep" k + t = n
      -- If we already found a valid period, it is some period < current k
      invariant "inv_outer_found_witness"
        (found = true) →
          (∃ kp : Nat,
            0 < kp ∧
            kp < n ∧
            kp < k ∧
            n % kp = 0 ∧
            (∀ i : Nat, i < n → s[i]! = s[i % kp]!))
      -- Completeness of the search so far: if we haven't found a period yet,
      -- then no kp < k is a valid period.
      invariant "inv_outer_no_period_before_k"
        (found = false) →
          (∀ kp : Nat,
            0 < kp ∧ kp < k →
              ¬(n % kp = 0 ∧ (∀ i : Nat, i < n → s[i]! = s[i % kp]!)))
      decreasing t
    do
      -- Here, k ranges over 1..n-1 in lockstep with t.
      if n % k = 0 then
        -- Check k-periodicity: for all i < n, s[i] = s[i % k].
        -- Since i % k = i for i < k, we can start from i := k.
        let mut i : Nat := k
        let mut ok : Bool := true
        let mut t2 : Nat := n - k
        while (t2 > 0) ∧ (ok = true)
          -- i is the next index to check; it starts at k and never exceeds n
          invariant "inv_inner_bounds" k ≤ i ∧ i ≤ n
          -- While ok remains true, i and t2 stay in perfect lockstep
          invariant "inv_inner_lockstep" (ok = true → i + t2 = n)
          -- Indices already checked satisfy the k-periodicity equation
          invariant "inv_inner_checked"
            ∀ j : Nat, k ≤ j ∧ j < i → s[j]! = s[j % k]!
          -- If ok becomes false (only by failing at the current i), we have a concrete mismatch
          invariant "inv_inner_mismatch_witness"
            (ok = false → i < n ∧ s[i]! ≠ s[i % k]!)
          decreasing t2
        do
          -- `t2 > 0` implies `i < n` when i starts at k and we decrement t2 each step.
          if s[i]! = s[i % k]! then
            i := i + 1
            t2 := t2 - 1
          else
            ok := false
            -- still decrease to satisfy termination semantics
            t2 := t2 - 1

        if ok = true then
          found := true

      k := k + 1
      t := t - 1

    return found
end Impl

section TestCases
-- Test case 1: Example 1: "abab" -> true
def test1_s : List Char := ['a', 'b', 'a', 'b']
def test1_Expected : Bool := true

-- Test case 2: Example 2: "aba" -> false
def test2_s : List Char := ['a', 'b', 'a']
def test2_Expected : Bool := false

-- Test case 3: Example 3: "abcabcabcabc" -> true
def test3_s : List Char := ['a','b','c','a','b','c','a','b','c','a','b','c']
def test3_Expected : Bool := true

-- Test case 4: Edge case: empty input -> false
def test4_s : List Char := []
def test4_Expected : Bool := false

-- Test case 5: Edge case: single character -> false
def test5_s : List Char := ['x']
def test5_Expected : Bool := false

-- Test case 6: All same character, length 4 -> true ("a" repeated 4 times)
def test6_s : List Char := ['a','a','a','a']
def test6_Expected : Bool := true

-- Test case 7: Repetition with period 2, length 6 -> true ("ab" repeated 3 times)
def test7_s : List Char := ['a','b','a','b','a','b']
def test7_Expected : Bool := true

-- Test case 8: Not periodic though has some repeated prefix -> false
def test8_s : List Char := ['a','b','a','c']
def test8_Expected : Bool := false

-- Test case 9: Prime length with mixed chars -> false
def test9_s : List Char := ['a','b','c','a','b']
def test9_Expected : Bool := false
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((RepeatedSubstringPattern test1_s).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((RepeatedSubstringPattern test2_s).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((RepeatedSubstringPattern test3_s).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((RepeatedSubstringPattern test4_s).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((RepeatedSubstringPattern test5_s).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((RepeatedSubstringPattern test6_s).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((RepeatedSubstringPattern test7_s).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((RepeatedSubstringPattern test8_s).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((RepeatedSubstringPattern test9_s).run), DivM.res test9_Expected ]
end Assertions

section Pbt
velvet_plausible_test RepeatedSubstringPattern (config := { maxMs := some 5000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000

theorem goal_0
    (s : List Char)
    (k : ℕ)
    (t : ℕ)
    (a : OfNat.ofNat 1 ≤ k)
    (invariant_inv_outer_lockstep : k + t = s.length)
    (if_pos : s.length % k = OfNat.ofNat 0)
    (i_1 : ℕ)
    (t2_1 : ℕ)
    (a_2 : OfNat.ofNat 0 < t)
    (invariant_inv_inner_checked : ∀ (j : ℕ), k ≤ j → j < i_1 → s[j]?.getD 'A' = s[j % k]?.getD 'A')
    (done_2 : t2_1 = OfNat.ofNat 0)
    (invariant_inv_inner_lockstep : i_1 + t2_1 = s.length)
    : ∃ kp, OfNat.ofNat 0 < kp ∧ kp < s.length ∧ kp < k + OfNat.ofNat 1 ∧ s.length % kp = OfNat.ofNat 0 ∧ ∀ i < s.length, s[i]?.getD 'A' = s[i % kp]?.getD 'A' := by
  have hkpos : 0 < k := by
    exact lt_of_lt_of_le (Nat.zero_lt_one) a

  have hklt_len : k < s.length := by
    have hklt_add : k < k + t := Nat.lt_add_of_pos_right a_2
    simpa [invariant_inv_outer_lockstep] using hklt_add

  have hi1 : i_1 = s.length := by
    -- i_1 + t2_1 = s.length and t2_1 = 0
    simpa [done_2] using invariant_inv_inner_lockstep

  refine ⟨k, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hkpos
  · exact hklt_len
  · -- k < k + 1
    simpa [Nat.succ_eq_add_one] using (Nat.lt_succ_self k)
  · simpa using if_pos
  · intro i hi
    by_cases hik : i < k
    · have hmod : i % k = i := Nat.mod_eq_of_lt hik
      simp [hmod]
    · have hki : k ≤ i := Nat.le_of_not_gt hik
      have hii1 : i < i_1 := by
        simpa [hi1] using hi
      exact invariant_inv_inner_checked i hki hii1

set_option loom.solver "custom"

macro_rules
| `(tactic|loom_solver) => `(tactic|(
  try injections
  try subst_vars
  try grind (gen := 4)))


prove_correct RepeatedSubstringPattern by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at *); try (conv => congr <;> simp) ; try expose_names)
  exact (goal_0 s k t a invariant_inv_outer_lockstep if_pos i_1 t2_1 a_2 invariant_inv_inner_checked done_2 invariant_inv_inner_lockstep)
end Proof
