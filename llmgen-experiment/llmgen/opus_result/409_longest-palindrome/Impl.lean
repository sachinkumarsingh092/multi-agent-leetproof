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
  let arr : Array Char := s.toArray
  let n := arr.size
  let mut pairSum : Nat := 0
  let mut hasOdd : Bool := false
  let mut i : Nat := 0
  while i < n
    -- i_bound: i ranges from 0 to n
    invariant "i_bound" i ≤ n
    -- pairSum_def: pairSum tracks the sum of (count(c)/2)*2 for each distinct character
    -- in the prefix s[0..i). dedup gives unique chars; s.count c is the full-string count.
    -- Init: i=0, take 0 = [], dedup [] = [], sum = 0 = pairSum. ✓
    -- Pres (firstOcc=true): new char added to dedup, pairSum increases by (cnt/2)*2. ✓
    -- Pres (firstOcc=false): char already in prefix, dedup unchanged, pairSum unchanged. ✓
    -- Suff: at i=n, pairSum = sum over all distinct chars of (count/2)*2. ✓
    invariant "pairSum_def" pairSum = List.sum (List.map (fun c => (s.count c / 2) * 2) ((s.take i).dedup))
    -- hasOdd_def: hasOdd is true iff some character in s[0..i) has odd total count in s.
    -- Init: i=0, take 0 = [], no such x exists, hasOdd=false. ✓
    -- Pres (firstOcc=true, cnt odd): hasOdd set to true, new x witnesses existential. ✓
    -- Pres (firstOcc=false): char already in take i, take (i+1) has same members, unchanged. ✓
    -- Suff: at i=n, tells us if any char has odd count. ✓
    invariant "hasOdd_def" (hasOdd = true) ↔ (∃ x ∈ List.take i s, s.count x % 2 = 1)
    decreasing n - i
  do
    let c := arr[i]!
    -- Check if this is the first occurrence of c (no earlier index has same char)
    let mut firstOcc := true
    let mut j : Nat := 0
    while j < i
      -- j_bound: j ranges from 0 to i
      invariant "j_bound" j ≤ i
      -- firstOcc_true: if firstOcc is still true, no index before j matches c
      -- Init: vacuously true (no k < 0). ✓
      -- Pres: if arr[j]! ≠ c, extends to k < j+1; if arr[j]! = c, firstOcc set false. ✓
      invariant "firstOcc_true" firstOcc = true → ∀ k, k < j → arr[k]! ≠ c
      -- firstOcc_false: if firstOcc is false, there exists a witness before index i
      -- Init: firstOcc=true, implication vacuously true. ✓
      -- Pres: when arr[j]! = c, j < i provides the witness. ✓
      -- Suff: at exit with firstOcc=false, we know c appears in s.take i. ✓
      invariant "firstOcc_false" firstOcc = false → ∃ k, k < i ∧ arr[k]! = c
      done_with j = i ∨ firstOcc = false
      decreasing i - j
    do
      if arr[j]! = c then
        firstOcc := false
        break
      j := j + 1
    if firstOcc then
      -- Count occurrences of c in the whole array
      let mut cnt : Nat := 0
      let mut k : Nat := 0
      while k < n
        -- k_bound: k ranges from 0 to n
        invariant "k_bound" k ≤ n
        -- cnt_def: cnt equals the count of c in the first k elements of s
        -- Init: k=0, (s.take 0).count c = 0 = cnt. ✓
        -- Pres: if s[k]=c, cnt+1 = (s.take (k+1)).count c; otherwise unchanged. ✓
        -- Suff: at k=n, cnt = s.count c. ✓
        invariant "cnt_def" cnt = (s.take k).count c
        decreasing n - k
      do
        if arr[k]! = c then
          cnt := cnt + 1
        k := k + 1
      -- Add pairs
      pairSum := pairSum + (cnt / 2) * 2
      -- Check if odd
      if cnt % 2 = 1 then
        hasOdd := true
    i := i + 1
  let mut res : Nat := pairSum
  if hasOdd then
    res := res + 1
  return res
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
    (hasOdd : Bool)
    (i : ℕ)
    (invariant_hasOdd_def : hasOdd = true ↔ ∃ x ∈ List.take i s, List.count x s % OfNat.ofNat 2 = OfNat.ofNat 1)
    (firstOcc : Bool)
    (j : ℕ)
    (invariant_j_bound : j ≤ i)
    (if_pos_1 : j < i)
    (invariant_i_bound : i ≤ s.length)
    (if_pos : i < s.length)
    (invariant_firstOcc_true : firstOcc = true → ∀ k < j, ¬s[k]?.getD 'A' = s[i]?.getD 'A')
    (invariant_firstOcc_false : firstOcc = false → ∃ k < i, s[k]?.getD 'A' = s[i]?.getD 'A')
    (if_pos_2 : s[j]?.getD 'A' = s[i]?.getD 'A')
    : ∃ k < i, s[k]?.getD 'A' = s[i]?.getD 'A' := by
    intros; expose_names; try simp_all; try grind

theorem goal_1
    (s : List Char)
    (hasOdd : Bool)
    (i : ℕ)
    (invariant_hasOdd_def : hasOdd = true ↔ ∃ x ∈ List.take i s, List.count x s % OfNat.ofNat 2 = OfNat.ofNat 1)
    (firstOcc : Bool)
    (j : ℕ)
    (invariant_j_bound : j ≤ i)
    (if_pos_1 : j < i)
    (invariant_i_bound : i ≤ s.length)
    (if_pos : i < s.length)
    (invariant_firstOcc_true : firstOcc = true → ∀ k < j, ¬s[k]?.getD 'A' = s[i]?.getD 'A')
    (if_neg : ¬s[j]?.getD 'A' = s[i]?.getD 'A')
    : firstOcc = true → ∀ k < j + OfNat.ofNat 1, ¬s[k]?.getD 'A' = s[i]?.getD 'A' := by
    intros; expose_names; try simp_all; try grind

theorem goal_2
    (s : List Char)
    (i : ℕ)
    (k : ℕ)
    (if_pos : i < s.length)
    (if_pos_2 : k < s.length)
    (if_pos_3 : s[k]?.getD 'A' = s[i]?.getD 'A')
    : List.count (s[i]?.getD 'A') (List.take k s) + OfNat.ofNat 1 = List.count (s[i]?.getD 'A') (List.take (k + OfNat.ofNat 1) s) := by
    have hk : s[k]?.getD 'A' = s[k] := by simp [List.getD_getElem?, if_pos_2]
    have hi : s[i]?.getD 'A' = s[i] := by simp [List.getD_getElem?, if_pos]
    have heq : s[k] = s[i] := by rw [← hk, ← hi]; exact if_pos_3
    rw [hi]
    rw [List.take_succ_eq_append_getElem if_pos_2]
    rw [List.count_append]
    rw [heq]
    rw [List.count_singleton_self]

theorem goal_3
    (s : List Char)
    (i : ℕ)
    (k : ℕ)
    (if_pos_2 : k < s.length)
    (if_neg : ¬s[k]?.getD 'A' = s[i]?.getD 'A')
    : List.count (s[i]?.getD 'A') (List.take k s) = List.count (s[i]?.getD 'A') (List.take (k + OfNat.ofNat 1) s) := by
    rw [List.take_succ_eq_append_getElem if_pos_2]
    rw [List.count_append, List.count_singleton]
    have hne : ¬(s[k] = s[i]?.getD 'A') := by
      rw [List.getD_getElem? (d := 'A')] at if_neg
      simp [dif_pos if_pos_2] at if_neg
      exact if_neg
    simp [beq_iff_eq, hne]

theorem goal_4_0
    (s : List Char)
    (i : ℕ)
    (if_pos : i < s.length)
    (hc_not_mem : s[i] ∉ List.take i s)
    : (List.take i s ++ [s[i]]).dedup = (List.take i s).dedup ++ [s[i]] := by
    have hdisj : List.Disjoint (List.take i s) [s[i]] := by
      intro a ha hb
      simp at hb
      subst hb
      exact hc_not_mem ha
    rw [List.Disjoint.dedup_append hdisj]
    simp [List.dedup_cons_of_not_mem]

theorem goal_4
    (s : List Char)
    (hasOdd : Bool)
    (i : ℕ)
    (invariant_hasOdd_def : hasOdd = true ↔ ∃ x ∈ List.take i s, List.count x s % OfNat.ofNat 2 = OfNat.ofNat 1)
    (j_1 : ℕ)
    (k_1 : ℕ)
    (invariant_i_bound : i ≤ s.length)
    (if_pos : i < s.length)
    (invariant_firstOcc_true : ∀ k < j_1, ¬s[k]?.getD 'A' = s[i]?.getD 'A')
    (done_2 : j_1 = i)
    (invariant_k_bound : k_1 ≤ s.length)
    (done_3 : s.length ≤ k_1)
    (if_pos_2 : List.count (s[i]?.getD 'A') (List.take k_1 s) % OfNat.ofNat 2 = OfNat.ofNat 1)
    : (List.map (fun c => List.count c s / OfNat.ofNat 2 * OfNat.ofNat 2) (List.take i s).dedup).sum + List.count (s[i]?.getD 'A') (List.take k_1 s) / OfNat.ofNat 2 * OfNat.ofNat 2 = (List.map (fun c => List.count c s / OfNat.ofNat 2 * OfNat.ofNat 2) (List.take (i + OfNat.ofNat 1) s).dedup).sum := by
    have hk_eq : k_1 = s.length := Nat.le_antisymm invariant_k_bound done_3
    have htake_k : List.take k_1 s = s := by
      rw [hk_eq]; exact List.take_length
    have hc_eq : s[i]?.getD 'A' = s[i] := by
      simp [List.getElem?_eq_getElem (h := if_pos)]
    have hc_not_mem : s[i] ∉ List.take i s := by
      expose_names; intros; expose_names; try simp_all; try grind
    have htake_succ : List.take (i + 1) s = List.take i s ++ [s[i]] := by
      exact List.take_succ_eq_append_getElem if_pos
    have hdedup_eq : (List.take i s ++ [s[i]]).dedup = (List.take i s).dedup ++ [s[i]] := by
      expose_names; exact (goal_4_0 s i if_pos hc_not_mem)
    rw [htake_k, htake_succ, hdedup_eq, List.map_append, List.sum_append]
    simp [hc_eq]

theorem goal_5
    (s : List Char)
    (i : ℕ)
    (j_1 : ℕ)
    (k_1 : ℕ)
    (if_pos : i < s.length)
    (done_2 : j_1 = i)
    (invariant_k_bound : k_1 ≤ s.length)
    (done_3 : s.length ≤ k_1)
    (if_pos_2 : List.count (s[i]?.getD 'A') (List.take k_1 s) % OfNat.ofNat 2 = OfNat.ofNat 1)
    : ∃ x ∈ List.take (i + OfNat.ofNat 1) s, List.count x s % OfNat.ofNat 2 = OfNat.ofNat 1 := by
    have htake_k : List.take k_1 s = s := List.take_of_length_le (by omega)
    rw [htake_k] at if_pos_2
    have hgetD : s[i]?.getD 'A' = s[i] := by
      simp [List.getD_getElem?, if_pos]
    refine ⟨s[i]?.getD 'A', ?_, if_pos_2⟩
    rw [hgetD]
    have : i + 1 ≤ s.length := by omega
    rw [List.mem_take_iff_getElem]
    refine ⟨i, ?_, rfl⟩
    simp [Nat.min_eq_left this]

theorem goal_6
    (s : List Char)
    (i : ℕ)
    (j_1 : ℕ)
    (k_1 : ℕ)
    (if_pos : i < s.length)
    (invariant_firstOcc_true : ∀ k < j_1, ¬s[k]?.getD 'A' = s[i]?.getD 'A')
    (done_2 : j_1 = i)
    (invariant_k_bound : k_1 ≤ s.length)
    (done_3 : s.length ≤ k_1)
    : (List.map (fun c => List.count c s / OfNat.ofNat 2 * OfNat.ofNat 2) (List.take i s).dedup).sum + List.count (s[i]?.getD 'A') (List.take k_1 s) / OfNat.ofNat 2 * OfNat.ofNat 2 = (List.map (fun c => List.count c s / OfNat.ofNat 2 * OfNat.ofNat 2) (List.take (i + OfNat.ofNat 1) s).dedup).sum := by
    have hk1 : k_1 = s.length := Nat.le_antisymm invariant_k_bound done_3
    have htake_k1 : List.take k_1 s = s := by rw [hk1]; exact List.take_length
    have hsi_getD : s[i]?.getD 'A' = s[i]'if_pos := by
      rw [List.getElem?_eq_getElem if_pos]
      simp
    have hc_not_mem : s[i]'if_pos ∉ List.take i s := by
      intro hmem
      rw [List.mem_take_iff_getElem] at hmem
      obtain ⟨j, hj_lt, hj_eq⟩ := hmem
      have hji : j < i := by omega
      have := invariant_firstOcc_true j (done_2 ▸ hji)
      rw [hsi_getD] at this
      have hj_lt_len : j < s.length := by omega
      simp [List.getElem?_eq_getElem hj_lt_len] at this
      exact this hj_eq
    have hdedup : (List.take i s ++ [s[i]'if_pos]).dedup = (List.take i s).dedup ++ [s[i]'if_pos] := goal_4_0 s i if_pos hc_not_mem
    have htake_succ : List.take (i + 1) s = List.take i s ++ [s[i]'if_pos] := by
      rw [List.take_succ]
      simp [List.getElem?_eq_getElem if_pos]
    rw [htake_succ, hdedup, List.map_append, List.sum_append]
    simp [htake_k1, hsi_getD]

theorem goal_7
    (s : List Char)
    (require_1 : True)
    (hasOdd : Bool)
    (i : ℕ)
    (invariant_hasOdd_def : hasOdd = true ↔ ∃ x ∈ List.take i s, List.count x s % OfNat.ofNat 2 = OfNat.ofNat 1)
    (i_1 : Bool)
    (j_1 : ℕ)
    (invariant_j_bound : j_1 ≤ i)
    (done_2 : j_1 = i ∨ i_1 = false)
    (invariant_i_bound : i ≤ s.length)
    (if_pos : i < s.length)
    (if_neg : i_1 = false)
    (invariant_firstOcc_false : i_1 = false → ∃ k < i, s[k]?.getD 'A' = s[i]?.getD 'A')
    (invariant_firstOcc_true : i_1 = true → ∀ k < j_1, ¬s[k]?.getD 'A' = s[i]?.getD 'A')
    : (List.map (fun c => List.count c s / OfNat.ofNat 2 * OfNat.ofNat 2) (List.take i s).dedup).sum = (List.map (fun c => List.count c s / OfNat.ofNat 2 * OfNat.ofNat 2) (List.take (i + OfNat.ofNat 1) s).dedup).sum := by
    sorry



theorem goal_7
    (s : List Char)
    (require_1 : True)
    (hasOdd : Bool)
    (i : ℕ)
    (invariant_hasOdd_def : hasOdd = true ↔ ∃ x ∈ List.take i s, List.count x s % OfNat.ofNat 2 = OfNat.ofNat 1)
    (i_1 : Bool)
    (j_1 : ℕ)
    (invariant_j_bound : j_1 ≤ i)
    (done_2 : j_1 = i ∨ i_1 = false)
    (invariant_i_bound : i ≤ s.length)
    (if_pos : i < s.length)
    (if_neg : i_1 = false)
    (invariant_firstOcc_false : i_1 = false → ∃ k < i, s[k]?.getD 'A' = s[i]?.getD 'A')
    (invariant_firstOcc_true : i_1 = true → ∀ k < j_1, ¬s[k]?.getD 'A' = s[i]?.getD 'A')
    : (List.map (fun c => List.count c s / OfNat.ofNat 2 * OfNat.ofNat 2) (List.take i s).dedup).sum = (List.map (fun c => List.count c s / OfNat.ofNat 2 * OfNat.ofNat 2) (List.take (i + OfNat.ofNat 1) s).dedup).sum := by
    sorry

theorem goal_8
    (s : List Char)
    (require_1 : True)
    (hasOdd : Bool)
    (i : ℕ)
    (invariant_hasOdd_def : hasOdd = true ↔ ∃ x ∈ List.take i s, List.count x s % OfNat.ofNat 2 = OfNat.ofNat 1)
    (i_1 : Bool)
    (j_1 : ℕ)
    (invariant_j_bound : j_1 ≤ i)
    (done_2 : j_1 = i ∨ i_1 = false)
    (invariant_i_bound : i ≤ s.length)
    (if_pos : i < s.length)
    (if_neg : i_1 = false)
    (invariant_firstOcc_false : i_1 = false → ∃ k < i, s[k]?.getD 'A' = s[i]?.getD 'A')
    (invariant_firstOcc_true : i_1 = true → ∀ k < j_1, ¬s[k]?.getD 'A' = s[i]?.getD 'A')
    : hasOdd = true ↔ ∃ x ∈ List.take (i + OfNat.ofNat 1) s, List.count x s % OfNat.ofNat 2 = OfNat.ofNat 1 := by
    sorry

theorem goal_9
    (s : List Char)
    (require_1 : True)
    (i_2 : ℕ)
    (invariant_i_bound : i_2 ≤ s.length)
    (done_1 : s.length ≤ i_2)
    (invariant_hasOdd_def : ∃ x ∈ List.take i_2 s, List.count x s % OfNat.ofNat 2 = OfNat.ofNat 1)
    : postcondition s ((List.map (fun c => List.count c s / OfNat.ofNat 2 * OfNat.ofNat 2) (List.take i_2 s).dedup).sum + OfNat.ofNat 1) := by
    sorry

theorem goal_10
    (s : List Char)
    (require_1 : True)
    (i_1 : Bool)
    (i_2 : ℕ)
    (invariant_hasOdd_def : i_1 = true ↔ ∃ x ∈ List.take i_2 s, List.count x s % OfNat.ofNat 2 = OfNat.ofNat 1)
    (if_neg : i_1 = false)
    (invariant_i_bound : i_2 ≤ s.length)
    (done_1 : s.length ≤ i_2)
    : postcondition s (List.map (fun c => List.count c s / OfNat.ofNat 2 * OfNat.ofNat 2) (List.take i_2 s).dedup).sum := by
    sorry



prove_correct LongestPalindrome by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at *); try (conv => congr <;> simp) ; try expose_names)
  exact (goal_0 s hasOdd i invariant_hasOdd_def firstOcc j invariant_j_bound if_pos_1 invariant_i_bound if_pos invariant_firstOcc_true invariant_firstOcc_false if_pos_2)
  exact (goal_1 s hasOdd i invariant_hasOdd_def firstOcc j invariant_j_bound if_pos_1 invariant_i_bound if_pos invariant_firstOcc_true if_neg)
  exact (goal_2 s i k if_pos if_pos_2 if_pos_3)
  exact (goal_3 s i k if_pos_2 if_neg)
  exact (goal_4 s hasOdd i invariant_hasOdd_def j_1 k_1 invariant_i_bound if_pos invariant_firstOcc_true done_2 invariant_k_bound done_3 if_pos_2)
  exact (goal_5 s i j_1 k_1 if_pos done_2 invariant_k_bound done_3 if_pos_2)
  exact (goal_6 s i j_1 k_1 if_pos invariant_firstOcc_true done_2 invariant_k_bound done_3)
  exact (goal_7 s require_1 hasOdd i invariant_hasOdd_def i_1 j_1 invariant_j_bound done_2 invariant_i_bound if_pos if_neg invariant_firstOcc_false invariant_firstOcc_true)
  exact (goal_8 s require_1 hasOdd i invariant_hasOdd_def i_1 j_1 invariant_j_bound done_2 invariant_i_bound if_pos if_neg invariant_firstOcc_false invariant_firstOcc_true)
  exact (goal_9 s require_1 i_2 invariant_i_bound done_1 invariant_hasOdd_def)
  exact (goal_10 s require_1 i_1 i_2 invariant_hasOdd_def if_neg invariant_i_bound done_1)
end Proof
