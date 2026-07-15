import Lean
import Mathlib.Tactic
import Velvet.Std
import Extensions.VelvetPBT

set_option maxHeartbeats 10000000

section Specs
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false

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
def implementation (s : List Char) : Nat :=
  let uniq := s.eraseDups
  let pairSum := uniq.foldl (fun acc c => acc + (s.count c) / 2 * 2) 0
  if pairSum < s.length then pairSum + 1 else pairSum
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
#assert_same_evaluation #[(implementation test1_s), test1_Expected]

-- Test case 2
#assert_same_evaluation #[(implementation test2_s), test2_Expected]

-- Test case 3
#assert_same_evaluation #[(implementation test3_s), test3_Expected]

-- Test case 4
#assert_same_evaluation #[(implementation test4_s), test4_Expected]

-- Test case 5
#assert_same_evaluation #[(implementation test5_s), test5_Expected]

-- Test case 6
#assert_same_evaluation #[(implementation test6_s), test6_Expected]

-- Test case 7
#assert_same_evaluation #[(implementation test7_s), test7_Expected]

-- Test case 8
#assert_same_evaluation #[(implementation test8_s), test8_Expected]

-- Test case 9
#assert_same_evaluation #[(implementation test9_s), test9_Expected]
end Assertions

section Pbt
method implementationPbt (s : List Char)
  return (result : Nat)
  require precondition s
  ensures postcondition s result
  do
  return (implementation s)

velvet_plausible_test implementationPbt (config := { maxMs := some 20000 })
end Pbt

section Proof
theorem correctness_goal_0
    (s : List Char)
    (uniq : List Char)
    (pairSum : ℕ)
    (hpairSum : pairSum = List.foldl (fun acc c => acc + List.count c s / 2 * 2) 0 uniq)
    : pairSum = (List.map (fun c => List.count c s / 2 * 2) uniq).sum := by
    subst hpairSum
    simp only [List.sum]
    rw [← List.foldl_map]
    rw [List.foldl_eq_foldr]

-- The key issue: (x == y) = decide (x = y) for Char
-- This should be provable. Then we can rewrite eraseDupsBy to use decide.
-- But the real issue is that eraseDupsBy and pwFilter have completely different algorithms.
-- eraseDupsBy processes left-to-right filtering already-seen elements
-- pwFilter processes right-to-left, keeping elements pairwise distinct

-- Let me try a completely different strategy: use List.Perm then Sublist.eq
-- Actually wait - both are sublists of l. If they are permutations of each other
-- AND sublists of the same list, they must be equal.

-- Actually for Char, maybe I can show this via List.Nodup.sublist_ext or similar
-- Let me try yet another approach

-- Both produce the same Multiset:
-- count c (l.eraseDups) = if c ∈ l then 1 else 0
-- count c (l.dedup) = if c ∈ l then 1 else 0
-- Both are sublists of l
-- Two sublists of the same list that have the same count for every element must be equal

theorem eraseDups_eq_dedup_char (l : List Char) : l.eraseDups = l.dedup := by
  apply List.Sublist.antisymm
  · -- eraseDups is a sublist of dedup
    -- Both are sublists of l with same members
    -- eraseDups <+ l and dedup <+ l
    -- We need eraseDups <+ dedup
    -- This requires showing that eraseDups is a sublist of dedup
    -- which would require showing they have the same elements in the same relative order
    sorry
  · sorry


theorem correctness_goal_1_0
    (s : List Char)
    (h_precond : precondition s)
    (uniq : List Char)
    (huniq : uniq = s.eraseDups)
    (pairSum : ℕ)
    (hpairSum : pairSum = List.foldl (fun acc c => acc + List.count c s / 2 * 2) 0 uniq)
    (h_pairSum_eq : pairSum = (List.map (fun c => List.count c s / 2 * 2) uniq).sum)
    : s.eraseDups = s.dedup := by
    sorry

theorem correctness_goal_1
    (s : List Char)
    (h_precond : precondition s)
    (uniq : List Char)
    (huniq : uniq = s.eraseDups)
    (pairSum : ℕ)
    (hpairSum : pairSum = List.foldl (fun acc c => acc + List.count c s / 2 * 2) 0 uniq)
    (h_pairSum_eq : pairSum = (List.map (fun c => List.count c s / 2 * 2) uniq).sum)
    : (List.map (fun c => List.count c s) uniq).sum = s.length := by
    have h_eq : s.eraseDups = s.dedup := by expose_names; exact (correctness_goal_1_0 s h_precond uniq huniq pairSum hpairSum h_pairSum_eq)
    subst huniq
    rw [h_eq]
    exact List.sum_map_count_dedup_eq_length s

theorem correctness_goal_2
    (s : List Char)
    (uniq : List Char)
    (pairSum : ℕ)
    (h_pairSum_eq : pairSum = (List.map (fun c => List.count c s / 2 * 2) uniq).sum)
    (h_sum_count : (List.map (fun c => List.count c s) uniq).sum = s.length)
    : pairSum ≤ s.length := by
    rw [h_pairSum_eq, ← h_sum_count]
    apply List.sum_le_sum
    intro c _
    exact Nat.div_mul_le_self (List.count c s) 2

theorem correctness_goal_3_0
    (s : List Char)
    (uniq : List Char)
    (pairSum : ℕ)
    (h_pairSum_eq : pairSum = (List.map (fun c => List.count c s / 2 * 2) uniq).sum)
    (left : List Char)
    (h_left_len : left.length = (List.map (fun c => List.count c s / 2) uniq).sum)
    : pairSum = 2 * left.length := by
    rw [h_pairSum_eq, h_left_len]
    rw [List.sum_map_mul_right]
    ring

theorem count_flatMap_replicate_nodup (s : List Char) (uniq : List Char) (hnodup : uniq.Nodup) (c : Char) :
    List.count c (List.flatMap (fun d => List.replicate (List.count d s / 2) d) uniq) = if c ∈ uniq then List.count c s / 2 else 0 := by
  induction uniq with
  | nil => simp
  | cons hd tl ih =>
    have hnodup_tl : tl.Nodup := List.Nodup.of_cons hnodup
    have hd_not_mem : hd ∉ tl := List.Nodup.not_mem hnodup
    simp only [List.flatMap_cons, List.count_append, List.mem_cons]
    rw [ih hnodup_tl]
    simp only [List.count_replicate]
    by_cases hdc : hd = c
    · subst hdc
      simp [hd_not_mem]
    · have hbeq : (hd == c) = false := by
        simp [beq_iff_eq, hdc]
      have hne : ¬(c = hd) := fun h => hdc h.symm
      simp [hbeq, hne]


theorem correctness_goal_3_1
    (s : List Char)
    (uniq : List Char)
    (huniq : uniq = s.eraseDups)
    (pairSum : ℕ)
    (hpairSum : pairSum = List.foldl (fun acc c => acc + List.count c s / 2 * 2) 0 uniq)
    (h_pairSum_eq : pairSum = (List.map (fun c => List.count c s / 2 * 2) uniq).sum)
    (h_sum_count : (List.map (fun c => List.count c s) uniq).sum = s.length)
    (left : List Char)
    (hleft_def : left = List.flatMap (fun c => List.replicate (List.count c s / 2) c) uniq)
    (h_left_len : left.length = (List.map (fun c => List.count c s / 2) uniq).sum)
    (h_pairSum_twice : pairSum = 2 * left.length)
    : ∀ (c : Char), List.count c left = if c ∈ uniq then List.count c s / 2 else 0 := by
    intro c
    subst hleft_def
    have hnodup : uniq.Nodup := by
      subst huniq
      rw [eraseDups_eq_dedup_char]
      exact List.nodup_dedup s
    exact count_flatMap_replicate_nodup s uniq hnodup c

theorem correctness_goal_3_2
    (s : List Char)
    (uniq : List Char)
    (pairSum : ℕ)
    (h_pairSum_eq : pairSum = (List.map (fun c => List.count c s / 2 * 2) uniq).sum)
    (h_sum_count : (List.map (fun c => List.count c s) uniq).sum = s.length)
    : pairSum < s.length → ∃ c₀ ∈ uniq, List.count c₀ s % 2 = 1 := by
    intro h_lt
    rw [h_pairSum_eq] at h_lt
    rw [← h_sum_count] at h_lt
    have ⟨c₀, hc₀_mem, hc₀_lt⟩ := List.exists_lt_of_sum_lt (fun c => List.count c s / 2 * 2) (fun c => List.count c s) h_lt
    exact ⟨c₀, hc₀_mem, by omega⟩

theorem correctness_goal_3_3
    (s : List Char)
    (uniq : List Char)
    (huniq : uniq = s.eraseDups)
    (pairSum : ℕ)
    (hpairSum : pairSum = List.foldl (fun acc c => acc + List.count c s / 2 * 2) 0 uniq)
    (h_pairSum_eq : pairSum = (List.map (fun c => List.count c s / 2 * 2) uniq).sum)
    (h_sum_count : (List.map (fun c => List.count c s) uniq).sum = s.length)
    (h_pairSum_le : pairSum ≤ s.length)
    (left : List Char)
    (hleft_def : left = List.flatMap (fun c => List.replicate (List.count c s / 2) c) uniq)
    (h_pairSum_twice : pairSum = 2 * left.length)
    (h_left_count : ∀ (c : Char), List.count c left = if c ∈ uniq then List.count c s / 2 else 0)
    (h_left_uses : ∀ (c : Char), 2 * List.count c left ≤ List.count c s)
    (h_odd_left_uses : ∀ c₀ ∈ uniq, List.count c₀ s % 2 = 1 → 2 * List.count c₀ left + 1 ≤ List.count c₀ s)
    (h_palindrome_rev_left : isPalindrome (left.reverse ++ left))
    (hlt : pairSum < s.length)
    (c₀ : Char)
    (hc₀_mem : c₀ ∈ uniq)
    (hc₀_odd : List.count c₀ s % 2 = 1)
    (h_palindrome_mid : isPalindrome (left.reverse ++ [c₀] ++ left))
    : usesLetters s (left.reverse ++ [c₀] ++ left) := by
  simp only [isPalindrome, usesLetters, buildablePalindrome, precondition, postcondition]
  intros; expose_names; try simp_all; try grind

theorem correctness_goal_3
    (s : List Char)
    (uniq : List Char)
    (huniq : uniq = s.eraseDups)
    (pairSum : ℕ)
    (hpairSum : pairSum = List.foldl (fun acc c => acc + List.count c s / 2 * 2) 0 uniq)
    (h_pairSum_eq : pairSum = (List.map (fun c => List.count c s / 2 * 2) uniq).sum)
    (h_sum_count : (List.map (fun c => List.count c s) uniq).sum = s.length)
    (h_pairSum_le : pairSum ≤ s.length)
    : ∃ t, buildablePalindrome s t ∧ t.length = if pairSum < s.length then pairSum + 1 else pairSum := by
    set left := uniq.flatMap (fun c => List.replicate (s.count c / 2) c) with hleft_def
    have h_left_len : left.length = (List.map (fun c => List.count c s / 2) uniq).sum := by
      simp [hleft_def, List.length_flatMap, List.length_replicate]
    have h_pairSum_twice : pairSum = 2 * left.length := by
      expose_names; exact (correctness_goal_3_0 s uniq pairSum h_pairSum_eq left h_left_len)
    have h_left_count : ∀ c, left.count c = if c ∈ uniq then s.count c / 2 else 0 := by
      expose_names; exact (correctness_goal_3_1 s uniq huniq pairSum hpairSum h_pairSum_eq h_sum_count left hleft_def h_left_len h_pairSum_twice)
    have h_exists_odd : pairSum < s.length → ∃ c₀ ∈ uniq, s.count c₀ % 2 = 1 := by
      expose_names; exact (correctness_goal_3_2 s uniq pairSum h_pairSum_eq h_sum_count)
    have h_left_uses : ∀ c, 2 * left.count c ≤ s.count c := by
      expose_names; intros; expose_names; try simp_all; try grind
    have h_odd_left_uses : ∀ c₀, c₀ ∈ uniq → s.count c₀ % 2 = 1 → 2 * left.count c₀ + 1 ≤ s.count c₀ := by
      expose_names; intros; expose_names; try simp_all; try grind
    have h_palindrome_rev_left : isPalindrome (left.reverse ++ left) := by
      unfold isPalindrome; simp [List.reverse_append, List.reverse_reverse]
    by_cases hlt : pairSum < s.length
    · obtain ⟨c₀, hc₀_mem, hc₀_odd⟩ := h_exists_odd hlt
      have h_palindrome_mid : isPalindrome (left.reverse ++ [c₀] ++ left) := by
        unfold isPalindrome; simp [List.reverse_append, List.reverse_reverse]
      have h_uses_mid : usesLetters s (left.reverse ++ [c₀] ++ left) := by
        expose_names; exact (correctness_goal_3_3 s uniq huniq pairSum hpairSum h_pairSum_eq h_sum_count h_pairSum_le left hleft_def h_pairSum_twice h_left_count h_left_uses h_odd_left_uses h_palindrome_rev_left hlt c₀ hc₀_mem hc₀_odd h_palindrome_mid)
      have h_len_mid : (left.reverse ++ [c₀] ++ left).length = pairSum + 1 := by
        simp [List.length_append, List.length_reverse]; omega
      have h_if_true : (if pairSum < s.length then pairSum + 1 else pairSum) = pairSum + 1 := by
        simp [hlt]
      rw [h_if_true]
      exact ⟨left.reverse ++ [c₀] ++ left, ⟨h_palindrome_mid, h_uses_mid⟩, h_len_mid⟩
    · have h_uses_no_mid : usesLetters s (left.reverse ++ left) := by
        expose_names; simp only [isPalindrome, usesLetters, buildablePalindrome, precondition, postcondition]
        intros; expose_names; try ( simp at * ); try grind
      have h_len_no_mid : (left.reverse ++ left).length = pairSum := by
        simp [List.length_append, List.length_reverse]; omega
      have h_if_false : (if pairSum < s.length then pairSum + 1 else pairSum) = pairSum := by
        simp [hlt]
      rw [h_if_false]
      exact ⟨left.reverse ++ left, ⟨h_palindrome_rev_left, h_uses_no_mid⟩, h_len_no_mid⟩

theorem correctness_goal_4_0
    (s : List Char)
    (h_precond : precondition s)
    (uniq : List Char)
    (huniq : uniq = s.eraseDups)
    (pairSum : ℕ)
    (hpairSum : pairSum = List.foldl (fun acc c => acc + List.count c s / 2 * 2) 0 uniq)
    (h_pairSum_eq : pairSum = (List.map (fun c => List.count c s / 2 * 2) uniq).sum)
    (h_sum_count : (List.map (fun c => List.count c s) uniq).sum = s.length)
    (h_pairSum_le : pairSum ≤ s.length)
    (h_exists : ∃ t, buildablePalindrome s t ∧ t.length = if pairSum < s.length then pairSum + 1 else pairSum)
    : ∀ (t : List Char), buildablePalindrome s t → t.length ≤ pairSum + 1 := by
    sorry

theorem correctness_goal_4_1
    (s : List Char)
    (h_precond : precondition s)
    (uniq : List Char)
    (huniq : uniq = s.eraseDups)
    (pairSum : ℕ)
    (hpairSum : pairSum = List.foldl (fun acc c => acc + List.count c s / 2 * 2) 0 uniq)
    (h_pairSum_eq : pairSum = (List.map (fun c => List.count c s / 2 * 2) uniq).sum)
    (h_sum_count : (List.map (fun c => List.count c s) uniq).sum = s.length)
    (h_pairSum_le : pairSum ≤ s.length)
    (h_exists : ∃ t, buildablePalindrome s t ∧ t.length = if pairSum < s.length then pairSum + 1 else pairSum)
    (h_bound1 : ∀ (t : List Char), buildablePalindrome s t → t.length ≤ pairSum + 1)
    : ∀ (t : List Char), buildablePalindrome s t → t.length ≤ s.length := by
    sorry


theorem correctness_goal_4
    (s : List Char)
    (h_precond : precondition s)
    (uniq : List Char)
    (huniq : uniq = s.eraseDups)
    (pairSum : ℕ)
    (hpairSum : pairSum = List.foldl (fun acc c => acc + List.count c s / 2 * 2) 0 uniq)
    (h_pairSum_eq : pairSum = (List.map (fun c => List.count c s / 2 * 2) uniq).sum)
    (h_sum_count : (List.map (fun c => List.count c s) uniq).sum = s.length)
    (h_pairSum_le : pairSum ≤ s.length)
    (h_exists : ∃ t, buildablePalindrome s t ∧ t.length = if pairSum < s.length then pairSum + 1 else pairSum)
    : ∀ (t : List Char), buildablePalindrome s t → t.length ≤ if pairSum < s.length then pairSum + 1 else pairSum := by
    -- Key lemma 1: any buildable palindrome has length ≤ pairSum + 1
    have h_bound1 : ∀ (t : List Char), buildablePalindrome s t → t.length ≤ pairSum + 1 := by expose_names; exact (correctness_goal_4_0 s h_precond uniq huniq pairSum hpairSum h_pairSum_eq h_sum_count h_pairSum_le h_exists)
    -- Key lemma 2: any buildable palindrome has length ≤ s.length
    have h_bound2 : ∀ (t : List Char), buildablePalindrome s t → t.length ≤ s.length := by expose_names; exact (correctness_goal_4_1 s h_precond uniq huniq pairSum hpairSum h_pairSum_eq h_sum_count h_pairSum_le h_exists h_bound1)
    intro t ht
    split_ifs with hlt
    · exact h_bound1 t ht
    · have hge := Nat.le_antisymm h_pairSum_le (Nat.not_lt.mp hlt)
      linarith [h_bound2 t ht]


theorem correctness_goal
    (s : List Char)
    (h_precond : precondition s)
    : postcondition s (implementation s) := by
    unfold postcondition implementation
    simp only []
    -- Key definitions
    set uniq := s.eraseDups with huniq
    set pairSum := uniq.foldl (fun acc c => acc + (s.count c) / 2 * 2) 0 with hpairSum
    -- We need two parts: existence and upper bound
    have h_pairSum_eq : pairSum = (uniq.map (fun c => (s.count c) / 2 * 2)).sum := by expose_names; exact (correctness_goal_0 s uniq pairSum hpairSum)
    have h_sum_count : (uniq.map (fun c => s.count c)).sum = s.length := by expose_names; exact (correctness_goal_1 s h_precond uniq huniq pairSum hpairSum h_pairSum_eq)
    have h_pairSum_le : pairSum ≤ s.length := by expose_names; exact (correctness_goal_2 s uniq pairSum h_pairSum_eq h_sum_count)
    have h_exists : ∃ (t : List Char), buildablePalindrome s t ∧ t.length = (if pairSum < s.length then pairSum + 1 else pairSum) := by expose_names; exact (correctness_goal_3 s uniq huniq pairSum hpairSum h_pairSum_eq h_sum_count h_pairSum_le)
    have h_upper : ∀ (t : List Char), buildablePalindrome s t → t.length ≤ (if pairSum < s.length then pairSum + 1 else pairSum) := by expose_names; exact (correctness_goal_4 s h_precond uniq huniq pairSum hpairSum h_pairSum_eq h_sum_count h_pairSum_le h_exists)
    exact ⟨h_exists, h_upper⟩
end Proof
