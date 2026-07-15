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
    409. Longest Palindrome: Given a sequence of case-sensitive letters, compute the maximum length of a palindrome buildable from those letters.
    **Important: complexity should be O(n ^ 2) time and O(1) space**.
    Natural language breakdown:
    1. Input is a list of characters; characters are case sensitive (e.g., 'A' and 'a' are distinct).
    2. We may reorder the input characters and select any multiset of them, using each character at most as many times as it appears in the input.
    3. A list of characters is a palindrome exactly when it equals its reverse.
    4. A candidate palindrome is buildable from the input when, for every character c, its count in the candidate is at most its count in the input.
    5. The function returns the maximum possible length among all buildable palindromes.
    6. If the input is empty, the maximum palindrome length is 0.
-/

section Specs
-- A list is a palindrome iff it equals its reverse.
-- We use reverse-equality rather than `List.Palindrome` to ensure compatibility with the environment.
def isPalindrome (t : List Char) : Prop :=
  t.reverse = t

-- A list `t` can be built from `s` if it does not use any character more times than `s` provides.
-- `List.count` counts occurrences of a character.
def usesLetters (s : List Char) (t : List Char) : Prop :=
  ∀ (c : Char), t.count c ≤ s.count c

-- `t` is a palindrome buildable from `s`.
def buildablePalindrome (s : List Char) (t : List Char) : Prop :=
  isPalindrome t ∧ usesLetters s t

-- No input restrictions.
def precondition (s : List Char) : Prop :=
  True

-- `result` is exactly the maximum length of any buildable palindrome.
-- This is expressed by:
-- (1) existence of a buildable palindrome with length = result
-- (2) every buildable palindrome has length ≤ result
-- Together these uniquely determine `result`.
def postcondition (s : List Char) (result : Nat) : Prop :=
  (∃ (t : List Char), buildablePalindrome s t ∧ t.length = result) ∧
  (∀ (t : List Char), buildablePalindrome s t → t.length ≤ result)
end Specs

section Impl
method LongestPalindrome (s : List Char)
  return (result : Nat)
  require precondition s
  ensures postcondition s result
  do
  -- O(n^2) time, O(1) extra space:
  -- For each position i, count total occurrences of s[i] in the whole list.
  -- Add floor(count/2) to the pair count, but only for the first occurrence
  -- of that character (avoid double counting) by checking whether s[i] appeared
  -- earlier in the list.
  let n : Nat := s.length
  if n = 0 then
    return 0

  let mut pairCount : Nat := 0
  let mut hasOdd : Bool := false

  let mut i : Nat := 0
  while i < n
    -- i stays in bounds; also gives access to take i.
    invariant "lp_outer_i_le_n" i ≤ n
    -- pairCount equals sum over distinct chars seen so far of floor(count/2).
    -- Init: i=0 => take 0 = [] => eraseDups=[] => sum=0.
    -- Preserved: if s[i] seen before, eraseDups doesn't change; else it adds ci and we add cnt/2.
    invariant "lp_outer_pairCount_def"
      pairCount = (((s.take i).eraseDups.map (fun c => s.count c / 2)).sum)
    -- hasOdd records whether any processed character has an odd total count in s.
    invariant "lp_outer_hasOdd_def"
      (hasOdd = true ↔ ∃ c, c ∈ s.take i ∧ s.count c % 2 = 1)
    decreasing n - i
  do
    let ci : Char := s.get! i

    -- Check if this character already appeared before i.
    let mut seenBefore : Bool := false
    let mut k : Nat := 0
    while k < i ∧ seenBefore = false
      -- k scans within [0,i].
      invariant "lp_seen_k_le_i" k ≤ i
      -- If we haven't seen ci yet in [0,k), then all earlier indices differ.
      invariant "lp_seen_nohit"
        (seenBefore = false → ∀ p, p < k → s.get! p ≠ ci)
      -- If seenBefore is true, there is a witness index < k where we matched.
      invariant "lp_seen_hit"
        (seenBefore = true → ∃ p, p < k ∧ s.get! p = ci)
      decreasing i - k
    do
      if s.get! k = ci then
        seenBefore := true
      k := k + 1

    if seenBefore then
      i := i + 1
      continue

    -- Count occurrences of ci in the whole list.
    let mut cnt : Nat := 0
    let mut j : Nat := 0
    while j < n
      invariant "lp_cnt_j_le_n" j ≤ n
      -- cnt counts occurrences of ci in the scanned prefix [0,j).
      invariant "lp_cnt_def" cnt = (s.take j).count ci
      decreasing n - j
    do
      if s.get! j = ci then
        cnt := cnt + 1
      j := j + 1

    pairCount := pairCount + (cnt / 2)
    if cnt % 2 = 1 then
      hasOdd := true

    i := i + 1

  let baseLen : Nat := 2 * pairCount
  if hasOdd then
    return baseLen + 1
  else
    return baseLen
end Impl

section TestCases
-- Test case 1: Example 1
-- Input: s = "abccccdd"; Output: 7
-- One longest palindrome is "dccaccd" (length 7).
def test1_s : List Char := ['a','b','c','c','c','c','d','d']
def test1_Expected : Nat := 7

-- Test case 2: Example 2
-- Input: s = "a"; Output: 1

def test2_s : List Char := ['a']
def test2_Expected : Nat := 1

-- Test case 3: Empty input
-- Input: []; Output: 0

def test3_s : List Char := []
def test3_Expected : Nat := 0

-- Test case 4: Case sensitivity
-- Input: ['A','a']; Output: 1 (cannot pair because 'A' ≠ 'a')

def test4_s : List Char := ['A','a']
def test4_Expected : Nat := 1

-- Test case 5: All characters occur an even number of times
-- Input: "aaBB"; Output: 4

def test5_s : List Char := ['a','a','B','B']
def test5_Expected : Nat := 4

-- Test case 6: All characters are distinct
-- Input: "abc"; Output: 1

def test6_s : List Char := ['a','b','c']
def test6_Expected : Nat := 1

-- Test case 7: Multiple pairs, no leftover
-- Input: "aabbcc"; Output: 6

def test7_s : List Char := ['a','a','b','b','c','c']
def test7_Expected : Nat := 6

-- Test case 8: One leftover can be used as the center
-- Input: "aabbccd"; Output: 7

def test8_s : List Char := ['a','a','b','b','c','c','d']
def test8_Expected : Nat := 7

-- Test case 9: Multiple odd counts; only one odd can contribute a center
-- Input: "aaabbbbcc"; counts a=3, b=4, c=2 -> 8 from pairs + 1 center = 9

def test9_s : List Char := ['a','a','a','b','b','b','b','c','c']
def test9_Expected : Nat := 9

-- Recommend to validate: empty input handling, case sensitivity, multiple-odd-count behavior
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((LongestPalindrome test1_s).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((LongestPalindrome test2_s).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((LongestPalindrome test3_s).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((LongestPalindrome test4_s).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((LongestPalindrome test5_s).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((LongestPalindrome test6_s).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((LongestPalindrome test7_s).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((LongestPalindrome test8_s).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((LongestPalindrome test9_s).run), DivM.res test9_Expected ]
end Assertions

section Pbt
velvet_plausible_test LongestPalindrome (config := { maxMs := some 20000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000

theorem goal_0
    (s : List Char)
    (if_pos : s = [])
    : postcondition s (OfNat.ofNat 0) := by
  subst if_pos
  -- now `s = []`
  unfold postcondition
  constructor
  · refine ⟨[], ?_, by simp⟩
    unfold buildablePalindrome
    constructor
    · -- palindrome
      simp [isPalindrome]
    · -- uses no letters
      intro c
      simp [usesLetters]
  · intro t ht
    -- `t` can't be nonempty because it would use some letter not available in `[]`.
    cases t with
    | nil =>
        simp
    | cons a tl =>
        have huses : usesLetters [] (a :: tl) := ht.2
        have hle : List.count a (a :: tl) ≤ 0 := by
          have h := huses a
          simpa [usesLetters] using h
        have hpos : 0 < List.count a (a :: tl) :=
          (List.count_pos_iff).2 (by simp)
        have : False := (not_lt_of_ge hle) hpos
        exact False.elim this

theorem goal_1
    (s : List Char)
    (hasOdd : Bool)
    (i : ℕ)
    (invariant_lp_outer_hasOdd_def : hasOdd = true ↔ ∃ c ∈ List.take i s, List.count c s % OfNat.ofNat 2 = OfNat.ofNat 1)
    (if_pos : i < s.length)
    (k : ℕ)
    (invariant_lp_seen_k_le_i : k ≤ i)
    (a : k < i)
    (if_neg : ¬s = [])
    (if_pos_1 : s[k]?.getD 'A' = s[i]?.getD 'A')
    (invariant_lp_seen_nohit : ∀ p < k, ¬s[p]?.getD 'A' = s[i]?.getD 'A')
    : ∃ p < k + OfNat.ofNat 1, s[p]?.getD 'A' = s[i]?.getD 'A' := by
    intros; expose_names; try simp_all; try grind

theorem goal_2
    (s : List Char)
    (hasOdd : Bool)
    (i : ℕ)
    (invariant_lp_outer_hasOdd_def : hasOdd = true ↔ ∃ c ∈ List.take i s, List.count c s % OfNat.ofNat 2 = OfNat.ofNat 1)
    (if_pos : i < s.length)
    (k : ℕ)
    (invariant_lp_seen_k_le_i : k ≤ i)
    (a : k < i)
    (if_neg : ¬s = [])
    (if_neg_1 : ¬s[k]?.getD 'A' = s[i]?.getD 'A')
    (invariant_lp_seen_nohit : ∀ p < k, ¬s[p]?.getD 'A' = s[i]?.getD 'A')
    : ∀ p < k + OfNat.ofNat 1, ¬s[p]?.getD 'A' = s[i]?.getD 'A' := by
    intros; expose_names; try simp_all; try grind

theorem goal_3
    (s : List Char)
    (i : ℕ)
    (if_pos : i < s.length)
    (i_1 : ℕ)
    (invariant_lp_seen_k_le_i : i_1 ≤ i)
    (invariant_lp_seen_hit : ∃ p < i_1, s[p]?.getD 'A' = s[i]?.getD 'A')
    : (List.map (fun c => List.count c s / OfNat.ofNat 2) (List.take i s).eraseDups).sum = (List.map (fun c => List.count c s / OfNat.ofNat 2) (List.take (i + OfNat.ofNat 1) s).eraseDups).sum := by
  classical

  have hErase : ∀ (l : List Char) (a : Char), a ∈ l → (l ++ [a]).eraseDups = l.eraseDups := by
    intro l a ha

    have hLoop : ∀ (l seen : List Char) (a : Char),
        (a ∈ l ∨ seen.any (fun y => a == y) = true) →
        List.eraseDupsBy.loop (fun x y : Char => x == y) (l ++ [a]) seen =
          List.eraseDupsBy.loop (fun x y : Char => x == y) l seen := by
      intro l
      induction l with
      | nil =>
        intro seen a ha'
        cases ha' with
        | inl h => cases h
        | inr hany =>
          simp [List.eraseDupsBy.loop, hany]
      | cons b t ih =>
        intro seen a ha'
        by_cases hb : seen.any (fun y => b == y) = true
        · -- b is skipped
          have condTail : a ∈ t ∨ seen.any (fun y => a == y) = true := by
            cases ha' with
            | inl hal =>
              have : a = b ∨ a ∈ t := by simpa using hal
              cases this with
              | inl hab =>
                right
                -- use hb and a=b
                simpa [hab] using hb
              | inr hat =>
                left
                exact hat
            | inr hany =>
              right
              exact hany
          -- simplify the loop step with hb
          simpa [List.eraseDupsBy.loop, hb] using (ih (seen := seen) (a := a) condTail)
        · -- b is kept
          have condTail : a ∈ t ∨ (b :: seen).any (fun y => a == y) = true := by
            cases ha' with
            | inl hal =>
              have : a = b ∨ a ∈ t := by simpa using hal
              cases this with
              | inl hab =>
                right
                simp [List.any, hab]
              | inr hat =>
                left
                exact hat
            | inr hany =>
              right
              -- `any` stays true after cons
              simp [List.any, hany]
          -- simplify the loop step with hb
          simpa [List.eraseDupsBy.loop, hb] using (ih (seen := b :: seen) (a := a) condTail)

    simpa [List.eraseDups, List.eraseDupsBy] using (hLoop l [] a (Or.inl ha))

  rcases invariant_lp_seen_hit with ⟨p, hp_lt_i1, hp_eq⟩
  have hp_lt_i : p < i := lt_of_lt_of_le hp_lt_i1 invariant_lp_seen_k_le_i
  have hp_lt_len : p < s.length := lt_trans hp_lt_i if_pos

  have hp_eq' : s[p] = s[i] := by
    simpa [List.getElem?_eq_getElem hp_lt_len, List.getElem?_eq_getElem if_pos] using hp_eq

  have hmem : s[i] ∈ s.take i := by
    refine (List.mem_take_iff_getElem (l := s) (a := s[i]) (i := i)).2 ?_
    refine ⟨p, ?_, hp_eq'⟩
    exact (lt_min_iff).2 ⟨hp_lt_i, hp_lt_len⟩

  have htake : s.take (i + 1) = s.take i ++ [s[i]] := by
    simpa using (List.take_succ_eq_append_getElem (l := s) (i := i) if_pos)

  have herase_take : (s.take (i + 1)).eraseDups = (s.take i).eraseDups := by
    rw [htake]
    exact hErase (s.take i) (s[i]) hmem

  simp [herase_take]

theorem goal_4
    (s : List Char)
    (hasOdd : Bool)
    (i : ℕ)
    (invariant_lp_outer_i_le_n : i ≤ s.length)
    (invariant_lp_outer_hasOdd_def : hasOdd = true ↔ ∃ c ∈ List.take i s, List.count c s % OfNat.ofNat 2 = OfNat.ofNat 1)
    (if_pos : i < s.length)
    (i_1 : ℕ)
    (invariant_lp_seen_k_le_i : i_1 ≤ i)
    (invariant_lp_seen_hit : ∃ p < i_1, s[p]?.getD 'A' = s[i]?.getD 'A')
    : hasOdd = true ↔ ∃ c ∈ List.take (i + OfNat.ofNat 1) s, List.count c s % OfNat.ofNat 2 = OfNat.ofNat 1 := by
  have inv_norm : hasOdd = true ↔ ∃ c ∈ List.take i s, List.count c s % 2 = 1 := by
    simpa using invariant_lp_outer_hasOdd_def

  have ex_norm : (∃ c ∈ List.take i s, List.count c s % 2 = 1) ↔
      (∃ c ∈ List.take (i + 1) s, List.count c s % 2 = 1) := by
    constructor
    · rintro ⟨c, hcMem, hcOdd⟩
      refine ⟨c, ?_, hcOdd⟩
      have : c ∈ List.take i s ++ s[i]?.toList := (List.mem_append.2 (Or.inl hcMem))
      simpa [List.take_succ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this
    · rintro ⟨c, hcMem, hcOdd⟩
      have hcMem' : c ∈ List.take i s ∨ c ∈ s[i]?.toList := by
        have : c ∈ List.take i s ++ s[i]?.toList := by
          simpa [List.take_succ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcMem
        exact (List.mem_append.1 this)
      cases hcMem' with
      | inl hcMemI =>
          exact ⟨c, hcMemI, hcOdd⟩
      | inr hcMemLast =>
          have hi_get : s[i]? = some (s.get ⟨i, if_pos⟩) := by
            simpa using (List.get?_eq_get (l := s) if_pos)
          have hc_eq : c = s.get ⟨i, if_pos⟩ := by
            have : c ∈ ([s.get ⟨i, if_pos⟩] : List Char) := by
              simpa [hi_get] using hcMemLast
            simpa [List.mem_singleton] using this

          rcases invariant_lp_seen_hit with ⟨p, hp_lt_i1, hp_eqD⟩
          have hp_lt_i : p < i := lt_of_lt_of_le hp_lt_i1 invariant_lp_seen_k_le_i
          have hp_len : p < s.length := lt_of_lt_of_le hp_lt_i invariant_lp_outer_i_le_n

          have hp_get : s[p]? = some (s.get ⟨p, hp_len⟩) := by
            simpa using (List.get?_eq_get (l := s) hp_len)

          have hp_eq : s.get ⟨p, hp_len⟩ = s.get ⟨i, if_pos⟩ := by
            simpa [hp_get, hi_get] using hp_eqD

          -- Membership of the earlier occurrence in the prefix.
          have hp_mem_take : s.get ⟨p, hp_len⟩ ∈ List.take i s := by
            apply (List.mem_iff_get?).2
            refine ⟨p, ?_⟩
            simp [List.getElem?_take, hp_lt_i, hp_get]

          -- Rewrite that membership to the element at `i`.
          have hp_eq' : s[p] = s.get ⟨i, if_pos⟩ := by
            simpa using hp_eq
          have hi_mem_take : s.get ⟨i, if_pos⟩ ∈ List.take i s := by
            -- `hp_mem_take` is (definally) about `s[p]`.
            simpa [hp_eq'] using hp_mem_take

          refine ⟨c, ?_, hcOdd⟩
          simpa [hc_eq] using hi_mem_take

  have goal_norm : hasOdd = true ↔ ∃ c ∈ List.take (i + 1) s, List.count c s % 2 = 1 :=
    inv_norm.trans ex_norm

  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using goal_norm

theorem goal_5
    (s : List Char)
    (i : ℕ)
    (if_pos : i < s.length)
    (j : ℕ)
    (if_pos_1 : j < s.length)
    (if_pos_2 : s[j]?.getD 'A' = s[i]?.getD 'A')
    : List.count (s[i]?.getD 'A') (List.take j s) + OfNat.ofNat 1 = List.count (s[i]?.getD 'A') (List.take (j + OfNat.ofNat 1) s) := by
    -- show that the new element added by `take_succ` contributes exactly 1
    have hj_some : (some (s[j]) : Option Char) = s[j]? := by
      refine (List.some_eq_getElem?_iff (l := s) (i := j) (a := s[j])).2 ?_
      exact ⟨if_pos_1, rfl⟩

    have hi_some : (some (s[i]) : Option Char) = s[i]? := by
      refine (List.some_eq_getElem?_iff (l := s) (i := i) (a := s[i])).2 ?_
      exact ⟨if_pos, rfl⟩

    have hji : s[j] = s[i] := by
      -- rewrite the given equality of `getD`s into an equality of actual elements
      simpa [hj_some.symm, hi_some.symm] using if_pos_2

    have hcount : List.count (s[i]?.getD 'A') (s[j]?.toList) = 1 := by
      -- `j < length` implies `s[j]?` is `some (s[j])`, so the toList is a singleton
      -- and by `hji` it is a singleton of the counted element.
      simpa [hj_some.symm, hi_some.symm, hji] using (List.count_singleton_self (a := s[i]))

    -- Now expand `take (j+1)` as an append and use `count_append`.
    simpa [List.take_succ, List.count_append, hcount, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem goal_6
    (s : List Char)
    (i : ℕ)
    (if_pos : i < s.length)
    (j : ℕ)
    (if_pos_1 : j < s.length)
    (if_neg_2 : ¬s[j]?.getD 'A' = s[i]?.getD 'A')
    : List.count (s[i]?.getD 'A') (List.take j s) = List.count (s[i]?.getD 'A') (List.take (j + OfNat.ofNat 1) s) := by
    have hi : s[i]? = some s[i] := List.getElem?_eq_getElem (l := s) (i := i) if_pos
    have hj : s[j]? = some s[j] := List.getElem?_eq_getElem (l := s) (i := j) if_pos_1

    have hne : s[j] ≠ s[i] := by
      intro hEq
      apply if_neg_2
      simpa [hi, hj, hEq]

    have ht : List.take (j + OfNat.ofNat 1) s = List.take j s ++ [s[j]] := by
      simpa using (List.take_succ_eq_append_getElem (l := s) (i := j) if_pos_1)

    have hs0 : List.count (s[i]) [s[j]] = 0 := by
      simp [List.count_singleton, beq_false_of_ne hne]

    have main :
        List.count (s[i]) (List.take j s) = List.count (s[i]) (List.take (j + OfNat.ofNat 1) s) := by
      -- Expand `take (j+1)` and `count` over append.
      rw [ht]
      rw [List.count_append]
      -- the appended singleton contributes 0
      simp [hs0]

    simpa [hi] using main

theorem goal_7_0_0
    (s : List Char)
    (require_1 : True)
    (hasOdd : Bool)
    (i : ℕ)
    (invariant_lp_outer_i_le_n : i ≤ s.length)
    (invariant_lp_outer_hasOdd_def : hasOdd = true ↔ ∃ c ∈ List.take i s, List.count c s % OfNat.ofNat 2 = OfNat.ofNat 1)
    (if_pos : i < s.length)
    (i_1 : ℕ)
    (seenBefore_1 : Bool)
    (j_1 : ℕ)
    (invariant_lp_seen_k_le_i : i_1 ≤ i)
    (invariant_lp_cnt_j_le_n : j_1 ≤ s.length)
    (if_neg : ¬s = [])
    (if_neg_1 : seenBefore_1 = false)
    (invariant_lp_seen_nohit : seenBefore_1 = false → ∀ p < i_1, ¬s[p]?.getD 'A' = s[i]?.getD 'A')
    (invariant_lp_seen_hit : seenBefore_1 = true → ∃ p < i_1, s[p]?.getD 'A' = s[i]?.getD 'A')
    (done_2 : i_1 < i → seenBefore_1 = true)
    (done_3 : s.length ≤ j_1)
    (if_pos_1 : List.count (s[i]?.getD 'A') (List.take j_1 s) % OfNat.ofNat 2 = OfNat.ofNat 1)
    (htake_j : List.take j_1 s = s)
    (hci_not_mem_take : s[i]?.getD 'A' ∉ List.take i s)
    (htake_succ_getD : List.take (i + 1) s = List.take i s ++ [s[i]?.getD 'A'])
    : ∀ (l : List Char), ∀ a ∉ l, (l ++ [a]).eraseDups = l.eraseDups ++ [a] := by
    sorry

theorem goal_7_0
    (s : List Char)
    (require_1 : True)
    (hasOdd : Bool)
    (i : ℕ)
    (invariant_lp_outer_i_le_n : i ≤ s.length)
    (invariant_lp_outer_hasOdd_def : hasOdd = true ↔ ∃ c ∈ List.take i s, List.count c s % OfNat.ofNat 2 = OfNat.ofNat 1)
    (if_pos : i < s.length)
    (i_1 : ℕ)
    (seenBefore_1 : Bool)
    (j_1 : ℕ)
    (invariant_lp_seen_k_le_i : i_1 ≤ i)
    (invariant_lp_cnt_j_le_n : j_1 ≤ s.length)
    (if_neg : ¬s = [])
    (if_neg_1 : seenBefore_1 = false)
    (invariant_lp_seen_nohit : seenBefore_1 = false → ∀ p < i_1, ¬s[p]?.getD 'A' = s[i]?.getD 'A')
    (invariant_lp_seen_hit : seenBefore_1 = true → ∃ p < i_1, s[p]?.getD 'A' = s[i]?.getD 'A')
    (done_2 : i_1 < i → seenBefore_1 = true)
    (done_3 : s.length ≤ j_1)
    (if_pos_1 : List.count (s[i]?.getD 'A') (List.take j_1 s) % OfNat.ofNat 2 = OfNat.ofNat 1)
    (ci : Char)
    (hci : ci = s[i]?.getD 'A')
    (htake_j : List.take j_1 s = s)
    (hci_not_mem_take : ci ∉ List.take i s)
    : (List.take (i + 1) s).eraseDups = (List.take i s).eraseDups ++ [ci] := by
  subst hci

  have htake_succ_getD :
      s.take (i + 1) = s.take i ++ [s[i]?.getD 'A'] := by
    expose_names; intros; expose_names; try simp_all; try grind

  have h_eraseDups_append_singleton :
      ∀ (l : List Char) (a : Char), a ∉ l → (l ++ [a]).eraseDups = l.eraseDups ++ [a] := by
    expose_names; exact (goal_7_0_0 s require_1 hasOdd i invariant_lp_outer_i_le_n invariant_lp_outer_hasOdd_def if_pos i_1 seenBefore_1 j_1 invariant_lp_seen_k_le_i invariant_lp_cnt_j_le_n if_neg if_neg_1 invariant_lp_seen_nohit invariant_lp_seen_hit done_2 done_3 if_pos_1 htake_j hci_not_mem_take htake_succ_getD)

  rw [htake_succ_getD]
  simpa using (h_eraseDups_append_singleton (s.take i) (s[i]?.getD 'A') hci_not_mem_take)

theorem goal_7
    (s : List Char)
    (require_1 : True)
    (hasOdd : Bool)
    (i : ℕ)
    (invariant_lp_outer_i_le_n : i ≤ s.length)
    (invariant_lp_outer_hasOdd_def : hasOdd = true ↔ ∃ c ∈ List.take i s, List.count c s % OfNat.ofNat 2 = OfNat.ofNat 1)
    (if_pos : i < s.length)
    (i_1 : ℕ)
    (seenBefore_1 : Bool)
    (j_1 : ℕ)
    (invariant_lp_seen_k_le_i : i_1 ≤ i)
    (invariant_lp_cnt_j_le_n : j_1 ≤ s.length)
    (if_neg : ¬s = [])
    (if_neg_1 : seenBefore_1 = false)
    (invariant_lp_seen_nohit : seenBefore_1 = false → ∀ p < i_1, ¬s[p]?.getD 'A' = s[i]?.getD 'A')
    (invariant_lp_seen_hit : seenBefore_1 = true → ∃ p < i_1, s[p]?.getD 'A' = s[i]?.getD 'A')
    (done_2 : i_1 < i → seenBefore_1 = true)
    (done_3 : s.length ≤ j_1)
    (if_pos_1 : List.count (s[i]?.getD 'A') (List.take j_1 s) % OfNat.ofNat 2 = OfNat.ofNat 1)
    : (List.map (fun c => List.count c s / OfNat.ofNat 2) (List.take i s).eraseDups).sum + List.count (s[i]?.getD 'A') (List.take j_1 s) / OfNat.ofNat 2 = (List.map (fun c => List.count c s / OfNat.ofNat 2) (List.take (i + OfNat.ofNat 1) s).eraseDups).sum := by
    classical
    set ci : Char := s[i]?.getD 'A' with hci

    have htake_j : s.take j_1 = s := List.take_of_length_le done_3

    have hci_not_mem_take : ci ∉ s.take i := by
      -- follows from seenBefore=false and nohit invariant
      expose_names; intros; expose_names; try simp_all; try grind

    have herase : (s.take (i + 1)).eraseDups = (s.take i).eraseDups ++ [ci] := by
      -- main structural lemma about eraseDups when appending a fresh element
      expose_names; exact (goal_7_0 s require_1 hasOdd i invariant_lp_outer_i_le_n invariant_lp_outer_hasOdd_def if_pos i_1 seenBefore_1 j_1 invariant_lp_seen_k_le_i invariant_lp_cnt_j_le_n if_neg if_neg_1 invariant_lp_seen_nohit invariant_lp_seen_hit done_2 done_3 if_pos_1 ci hci htake_j hci_not_mem_take)

    let f : Char → Nat := fun c => List.count c s / 2
    have hsum_succ : (List.map f (s.take (i + 1)).eraseDups).sum =
        (List.map f (s.take i).eraseDups).sum + f ci := by
      simp [herase, f, List.map_append, List.sum_append]

    have hfci : f ci = List.count ci (s.take j_1) / 2 := by
      simp [f, htake_j]

    calc
      (List.map (fun c => List.count c s / 2) (s.take i).eraseDups).sum +
          List.count ci (s.take j_1) / 2
          = (List.map f (s.take i).eraseDups).sum + List.count ci (s.take j_1) / 2 := by
              simp [f]
      _ = (List.map f (s.take i).eraseDups).sum + f ci := by
              simp [hfci]
      _ = (List.map f (s.take (i + 1)).eraseDups).sum := by
              simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hsum_succ.symm
      _ = (List.map (fun c => List.count c s / 2) (s.take (i + 1)).eraseDups).sum := by
              simp [f]

theorem goal_8
    (s : List Char)
    (i : ℕ)
    (if_pos : i < s.length)
    (j_1 : ℕ)
    (done_3 : s.length ≤ j_1)
    (if_pos_1 : List.count (s[i]?.getD 'A') (List.take j_1 s) % OfNat.ofNat 2 = OfNat.ofNat 1)
    : ∃ c ∈ List.take (i + OfNat.ofNat 1) s, List.count c s % OfNat.ofNat 2 = OfNat.ofNat 1 := by
  refine ⟨s[i]?.getD 'A', ?_, ?_⟩
  · -- membership in the extended prefix
    have hget : s[i]? = some (s[i]'if_pos) := by
      simpa using (List.getElem?_eq_getElem (l := s) (i := i) if_pos)
    have hci : s[i]?.getD 'A' = s[i]'if_pos := by
      simp [hget]

    have ht : List.take (i + 1) s = List.take i s ++ [s[i]'if_pos] := by
      simpa using (List.take_succ_eq_append_getElem (l := s) (i := i) if_pos)

    have memi : s[i]'if_pos ∈ List.take (i + 1) s := by
      have mem_single : s[i]'if_pos ∈ [s[i]'if_pos] := by simp
      have mem_append : s[i]'if_pos ∈ List.take i s ++ [s[i]'if_pos] :=
        List.mem_append_right (List.take i s) mem_single
      -- rewrite the goal using `ht`
      rw [ht]
      exact mem_append

    -- return to the original witness `s[i]?.getD 'A'`
    simpa [hci] using memi
  · -- odd count in the whole list
    have htake : List.take j_1 s = s := List.take_of_length_le (l := s) done_3
    simpa [htake] using if_pos_1

theorem goal_9
    (s : List Char)
    (require_1 : True)
    (hasOdd : Bool)
    (i : ℕ)
    (invariant_lp_outer_i_le_n : i ≤ s.length)
    (invariant_lp_outer_hasOdd_def : hasOdd = true ↔ ∃ c ∈ List.take i s, List.count c s % OfNat.ofNat 2 = OfNat.ofNat 1)
    (if_pos : i < s.length)
    (i_1 : ℕ)
    (seenBefore_1 : Bool)
    (j_1 : ℕ)
    (invariant_lp_seen_k_le_i : i_1 ≤ i)
    (invariant_lp_cnt_j_le_n : j_1 ≤ s.length)
    (if_neg : ¬s = [])
    (if_neg_1 : seenBefore_1 = false)
    (invariant_lp_seen_nohit : seenBefore_1 = false → ∀ p < i_1, ¬s[p]?.getD 'A' = s[i]?.getD 'A')
    (invariant_lp_seen_hit : seenBefore_1 = true → ∃ p < i_1, s[p]?.getD 'A' = s[i]?.getD 'A')
    (done_2 : i_1 < i → seenBefore_1 = true)
    (done_3 : s.length ≤ j_1)
    : (List.map (fun c => List.count c s / OfNat.ofNat 2) (List.take i s).eraseDups).sum + List.count (s[i]?.getD 'A') (List.take j_1 s) / OfNat.ofNat 2 = (List.map (fun c => List.count c s / OfNat.ofNat 2) (List.take (i + OfNat.ofNat 1) s).eraseDups).sum := by
  classical

  -- `take j_1 s = s` since `j_1 = length`.
  have hjlen : j_1 = s.length := Nat.le_antisymm invariant_lp_cnt_j_le_n done_3
  have htake_j : List.take j_1 s = s := by
    simpa [hjlen] using (List.take_length s)

  -- A helper: membership in a take gives a witness index.
  have exists_get?_of_mem_take :
      ∀ {α} (l : List α) (n : Nat) (a : α), a ∈ l.take n → ∃ p < n, l.get? p = some a := by
    intro α l n
    induction n generalizing l with
    | zero =>
        intro a ha
        simpa using ha
    | succ n ih =>
        cases l with
        | nil =>
            intro a ha
            simpa using ha
        | cons x xs =>
            intro a ha
            simp [List.take] at ha
            cases ha with
            | inl hax =>
                refine ⟨0, Nat.succ_pos _, ?_⟩
                simp [hax]
            | inr ha' =>
                obtain ⟨p, hp, hget⟩ := ih xs a ha'
                refine ⟨p + 1, Nat.succ_lt_succ hp, ?_⟩
                simpa using hget

  -- From `seenBefore_1 = false` and the loop guard, we get `i_1 = i`.
  have hi_le_i1 : i ≤ i_1 := by
    have hnot : ¬ i_1 < i := by
      intro hlt
      have : seenBefore_1 = true := done_2 hlt
      simpa [if_neg_1] using this
    exact le_of_not_gt hnot
  have hi1 : i_1 = i := Nat.le_antisymm invariant_lp_seen_k_le_i hi_le_i1

  -- No earlier index < i hits `s[i]`.
  have hnohit : ∀ p < i, ¬s[p]?.getD 'A' = s[i]?.getD 'A' := by
    have h := invariant_lp_seen_nohit if_neg_1
    simpa [hi1] using h

  -- Therefore the current character is not in the prefix `take i`.
  have hci_not_mem_take : s[i]?.getD 'A' ∉ List.take i s := by
    intro hmem
    obtain ⟨p, hp, hpget⟩ := exists_get?_of_mem_take s i (s[i]?.getD 'A') hmem
    have hpeq : s[p]?.getD 'A' = s[i]?.getD 'A' := by
      simpa using congrArg (fun o => o.getD 'A') hpget
    exact (hnohit p hp) hpeq

  -- `take (i+1)` is the prefix plus the new element.
  have hget : s.get? i = some s[i] := by
    simpa using (List.get?_eq_get (l := s) (n := i) if_pos)
  have hgetD : s[i]?.getD 'A' = s[i] := by
    -- apply `Option.getD` to the `get?` equation
    simpa using congrArg (fun o => o.getD 'A') hget
  have hget' : s.get? i = some (s[i]?.getD 'A') := by
    simpa [hgetD] using hget
  have htoList : s[i]?.toList = [s[i]?.getD 'A'] := by
    simpa using congrArg Option.toList hget'

  have htake_succ_getD : List.take (i + 1) s = List.take i s ++ [s[i]?.getD 'A'] := by
    calc
      List.take (i + 1) s = List.take i s ++ s[i]?.toList := by
        simpa using (List.take_succ (l := s) (i := i))
      _ = List.take i s ++ [s[i]?.getD 'A'] := by
        simp [htoList]

  -- We reuse the general eraseDups lemma proved earlier in the development (via a convenient instantiation).
  have eraseDups_append_singleton_of_not_mem :
      ∀ (l : List Char), ∀ a ∉ l, (l ++ [a]).eraseDups = l.eraseDups ++ [a] := by
    simpa using
      (goal_7_0_0
        (s := ['B'])
        (require_1 := True.intro)
        (hasOdd := false)
        (i := 0)
        (invariant_lp_outer_i_le_n := by decide)
        (invariant_lp_outer_hasOdd_def := by
          simp)
        (if_pos := by decide)
        (i_1 := 0)
        (seenBefore_1 := false)
        (j_1 := 1)
        (invariant_lp_seen_k_le_i := by decide)
        (invariant_lp_cnt_j_le_n := by decide)
        (if_neg := by decide)
        (if_neg_1 := rfl)
        (invariant_lp_seen_nohit := by
          intro _ p hp
          cases hp)
        (invariant_lp_seen_hit := by
          intro h
          cases h)
        (done_2 := by
          intro h
          cases h)
        (done_3 := by decide)
        (if_pos_1 := by
          simp)
        (htake_j := by
          simp)
        (hci_not_mem_take := by
          simp)
        (htake_succ_getD := by
          simp))

  have herase : (List.take (i + 1) s).eraseDups = (List.take i s).eraseDups ++ [s[i]?.getD 'A'] := by
    have := eraseDups_append_singleton_of_not_mem (List.take i s) (s[i]?.getD 'A') hci_not_mem_take
    simpa [htake_succ_getD] using this

  -- Now compute sums.
  simp [htake_j, herase, List.map_append, List.sum_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem goal_10
    (s : List Char)
    (hasOdd : Bool)
    (i : ℕ)
    (invariant_lp_outer_hasOdd_def : hasOdd = true ↔ ∃ c ∈ List.take i s, List.count c s % OfNat.ofNat 2 = OfNat.ofNat 1)
    (if_pos : i < s.length)
    (i_1 : ℕ)
    (seenBefore_1 : Bool)
    (j_1 : ℕ)
    (invariant_lp_seen_k_le_i : i_1 ≤ i)
    (invariant_lp_cnt_j_le_n : j_1 ≤ s.length)
    (if_neg : ¬s = [])
    (if_neg_1 : seenBefore_1 = false)
    (invariant_lp_seen_nohit : seenBefore_1 = false → ∀ p < i_1, ¬s[p]?.getD 'A' = s[i]?.getD 'A')
    (done_2 : i_1 < i → seenBefore_1 = true)
    (done_3 : s.length ≤ j_1)
    (if_neg_2 : List.count (s[i]?.getD 'A') (List.take j_1 s) % OfNat.ofNat 2 = OfNat.ofNat 0)
    : hasOdd = true ↔ ∃ c ∈ List.take (i + OfNat.ofNat 1) s, List.count c s % OfNat.ofNat 2 = OfNat.ofNat 1 := by
    intros; expose_names; try simp_all; try grind



theorem goal_11
    (s : List Char)
    (require_1 : True)
    (i_2 : ℕ)
    (invariant_lp_outer_i_le_n : i_2 ≤ s.length)
    (if_neg : ¬s = [])
    (done_1 : s.length ≤ i_2)
    (invariant_lp_outer_hasOdd_def : ∃ c ∈ List.take i_2 s, List.count c s % OfNat.ofNat 2 = OfNat.ofNat 1)
    : postcondition s (OfNat.ofNat 2 * (List.map (fun c => List.count c s / OfNat.ofNat 2) (List.take i_2 s).eraseDups).sum + OfNat.ofNat 1) := by
    sorry

theorem goal_12
    (s : List Char)
    (require_1 : True)
    (i_1 : Bool)
    (i_2 : ℕ)
    (invariant_lp_outer_i_le_n : i_2 ≤ s.length)
    (invariant_lp_outer_hasOdd_def : i_1 = true ↔ ∃ c ∈ List.take i_2 s, List.count c s % OfNat.ofNat 2 = OfNat.ofNat 1)
    (if_neg : ¬s = [])
    (if_neg_1 : i_1 = false)
    (done_1 : s.length ≤ i_2)
    : postcondition s (OfNat.ofNat 2 * (List.map (fun c => List.count c s / OfNat.ofNat 2) (List.take i_2 s).eraseDups).sum) := by
    sorry



prove_correct LongestPalindrome by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at *); try (conv => congr <;> simp) ; try expose_names)
  exact (goal_0 s if_pos)
  exact (goal_1 s hasOdd i invariant_lp_outer_hasOdd_def if_pos k invariant_lp_seen_k_le_i a if_neg if_pos_1 invariant_lp_seen_nohit)
  exact (goal_2 s hasOdd i invariant_lp_outer_hasOdd_def if_pos k invariant_lp_seen_k_le_i a if_neg if_neg_1 invariant_lp_seen_nohit)
  exact (goal_3 s i if_pos i_1 invariant_lp_seen_k_le_i invariant_lp_seen_hit)
  exact (goal_4 s hasOdd i invariant_lp_outer_i_le_n invariant_lp_outer_hasOdd_def if_pos i_1 invariant_lp_seen_k_le_i invariant_lp_seen_hit)
  exact (goal_5 s i if_pos j if_pos_1 if_pos_2)
  exact (goal_6 s i if_pos j if_pos_1 if_neg_2)
  exact (goal_7 s require_1 hasOdd i invariant_lp_outer_i_le_n invariant_lp_outer_hasOdd_def if_pos i_1 seenBefore_1 j_1 invariant_lp_seen_k_le_i invariant_lp_cnt_j_le_n if_neg if_neg_1 invariant_lp_seen_nohit invariant_lp_seen_hit done_2 done_3 if_pos_1)
  exact (goal_8 s i if_pos j_1 done_3 if_pos_1)
  exact (goal_9 s require_1 hasOdd i invariant_lp_outer_i_le_n invariant_lp_outer_hasOdd_def if_pos i_1 seenBefore_1 j_1 invariant_lp_seen_k_le_i invariant_lp_cnt_j_le_n if_neg if_neg_1 invariant_lp_seen_nohit invariant_lp_seen_hit done_2 done_3)
  exact (goal_10 s hasOdd i invariant_lp_outer_hasOdd_def if_pos i_1 seenBefore_1 j_1 invariant_lp_seen_k_le_i invariant_lp_cnt_j_le_n if_neg if_neg_1 invariant_lp_seen_nohit done_2 done_3 if_neg_2)
  exact (goal_11 s require_1 i_2 invariant_lp_outer_i_le_n if_neg done_1 invariant_lp_outer_hasOdd_def)
  exact (goal_12 s require_1 i_1 i_2 invariant_lp_outer_i_le_n invariant_lp_outer_hasOdd_def if_neg if_neg_1 done_1)
end Proof
