import Lean

import Mathlib.Tactic

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

section Proof

theorem eraseDups_eq_dedup_char (l : List Char) : l.eraseDups = l.dedup := by
  apply List.Sublist.antisymm
  ·
    
    
    
    
    
    sorry
  · sorry

theorem correctness_goal_1_0 (s : List Char) (h_precond : precondition s) (uniq : List Char) (huniq : uniq = s.eraseDups) (pairSum : ℕ) (hpairSum : pairSum = List.foldl (fun acc c => acc + List.count c s / 2 * 2) 0 uniq) (h_pairSum_eq : pairSum = (List.map (fun c => List.count c s / 2 * 2) uniq).sum) : s.eraseDups = s.dedup := by
    sorry

theorem correctness_goal_4_0 (s : List Char) (h_precond : precondition s) (uniq : List Char) (huniq : uniq = s.eraseDups) (pairSum : ℕ) (hpairSum : pairSum = List.foldl (fun acc c => acc + List.count c s / 2 * 2) 0 uniq) (h_pairSum_eq : pairSum = (List.map (fun c => List.count c s / 2 * 2) uniq).sum) (h_sum_count : (List.map (fun c => List.count c s) uniq).sum = s.length) (h_pairSum_le : pairSum ≤ s.length) (h_exists : ∃ t, buildablePalindrome s t ∧ t.length = if pairSum < s.length then pairSum + 1 else pairSum) : ∀ (t : List Char), buildablePalindrome s t → t.length ≤ pairSum + 1 := by
    sorry

theorem correctness_goal_4_1 (s : List Char) (h_precond : precondition s) (uniq : List Char) (huniq : uniq = s.eraseDups) (pairSum : ℕ) (hpairSum : pairSum = List.foldl (fun acc c => acc + List.count c s / 2 * 2) 0 uniq) (h_pairSum_eq : pairSum = (List.map (fun c => List.count c s / 2 * 2) uniq).sum) (h_sum_count : (List.map (fun c => List.count c s) uniq).sum = s.length) (h_pairSum_le : pairSum ≤ s.length) (h_exists : ∃ t, buildablePalindrome s t ∧ t.length = if pairSum < s.length then pairSum + 1 else pairSum) (h_bound1 : ∀ (t : List Char), buildablePalindrome s t → t.length ≤ pairSum + 1) : ∀ (t : List Char), buildablePalindrome s t → t.length ≤ s.length := by
    sorry
end Proof
