import Mathlib

-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false

/- Problem Description
    917. Reverse Only Letters: Reverse only the English letters in a character sequence, keeping non-letters fixed.
    **Important: complexity should be O(n) time and O(n) space**
    Natural language breakdown:
    1. Input is a finite sequence of characters.
    2. A character is considered an English letter exactly when it is an ASCII uppercase letter ('A'..'Z') or an ASCII lowercase letter ('a'..'z').
    3. Every non-letter character must stay at the same index in the output.
    4. The set of indices that contain letters must be the same in input and output.
    5. Reading only the letters from left to right in the output yields the reverse of the letters read from left to right in the input.
    6. The output has the same length as the input.
-/

section Specs
-- Helper predicate: ASCII uppercase letter ('A'..'Z').
def isAsciiUpper (c : Char) : Bool :=
  ('A'.toNat ≤ c.toNat) && (c.toNat ≤ 'Z'.toNat)

-- Helper predicate: ASCII lowercase letter ('a'..'z').
def isAsciiLower (c : Char) : Bool :=
  ('a'.toNat ≤ c.toNat) && (c.toNat ≤ 'z'.toNat)

-- Helper predicate: English letter (ASCII) is upper or lower.
def isLetter (c : Char) : Bool :=
  isAsciiUpper c || isAsciiLower c

-- Helper: extract the subsequence of letters.
def letters (s : List Char) : List Char :=
  s.filter (fun c => isLetter c)

-- No special input restrictions.
def precondition (s : List Char) : Prop :=
  True

-- Postcondition: length preserved; non-letters fixed; letter mask preserved; letters reversed.
def postcondition (s : List Char) (result : List Char) : Prop :=
  result.length = s.length ∧
  (∀ (i : Nat), i < s.length → (isLetter s[i]! = false) → result[i]! = s[i]!) ∧
  (∀ (i : Nat), i < s.length → isLetter result[i]! = isLetter s[i]!) ∧
  letters result = (letters s).reverse
end Specs

section TestCases
-- Test case 1: example 1
-- Input: "ab-cd"  Output: "dc-ba"
def test1_s : List Char := ['a','b','-','c','d']
def test1_Expected : List Char := ['d','c','-','b','a']

-- Test case 2: example 2
-- Input: "a-bC-dEf-ghIj"  Output: "j-Ih-gfE-dCba"
def test2_s : List Char := ['a','-','b','C','-','d','E','f','-','g','h','I','j']
def test2_Expected : List Char := ['j','-','I','h','-','g','f','E','-','d','C','b','a']

-- Test case 3: example 3
-- Input: "Test1ng-Leet=code-Q!"  Output: "Qedo1ct-eeLg=ntse-T!"
def test3_s : List Char :=
  ['T','e','s','t','1','n','g','-','L','e','e','t','=','c','o','d','e','-','Q','!']
def test3_Expected : List Char :=
  ['Q','e','d','o','1','c','t','-','e','e','L','g','=','n','t','s','e','-','T','!']

-- Test case 4: empty input

def test4_s : List Char := []
def test4_Expected : List Char := []

-- Test case 5: only letters (all reversed)

def test5_s : List Char := ['A','b','C','d']
def test5_Expected : List Char := ['d','C','b','A']

-- Test case 6: only non-letters (unchanged)

def test6_s : List Char := ['-','1','_','!']
def test6_Expected : List Char := ['-','1','_','!']

-- Test case 7: single character that is a letter

def test7_s : List Char := ['z']
def test7_Expected : List Char := ['z']

-- Test case 8: single character that is not a letter

def test8_s : List Char := ['?']
def test8_Expected : List Char := ['?']

-- Test case 9: letters separated by digits and punctuation
-- Input letters: a b c d e; reversed: e d c b a
-- Non-letters stay in place.

def test9_s : List Char := ['a','1','b','2','-','c','3','d','4','e']
def test9_Expected : List Char := ['e','1','d','2','-','c','3','b','4','a']

-- Recommend to validate: empty input, inputs with only non-letters, inputs mixing letters/non-letters
end TestCases

section Proof

/-
PROVIDED SOLUTION
The key insight: we have `invariant_inner_letters_search` saying `filter f (take i res_1.toList) = (filter f (drop j_1 s)).reverse`. We need to show the same with `drop (j_1 - 1) s` instead of `drop j_1 s`. Since `j_1 ≠ 0` and `j_1 ≤ s.length`, we have `drop (j_1 - 1) s = s[j_1-1] :: drop j_1 s`. The hypothesis `if_neg_2` says `s[j_1-1]` is NOT a letter (both upper and lower conditions fail). So `filter f (drop (j_1 - 1) s) = filter f (drop j_1 s)`. Use `List.drop_eq_getElem_cons` or decompose the drop manually, then show the filter is unchanged because the head element is not a letter. Then apply the invariant.
-/
theorem goal_5 (s : List Char) (require_1 : True) (i : ℕ) (j : ℕ) (res : Array Char) (invariant_outer_letters_account : List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.take i res.toList) = (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.drop j s)).reverse) (invariant_outer_lettercount_account : (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.take i s)).length = (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.drop j s)).length) (j_1 : ℕ) (res_1 : Array Char) (if_neg_1 : ¬j_1 = OfNat.ofNat 0) (invariant_outer_res_size : res.size = s.length) (invariant_outer_n_eq_len : True) (invariant_outer_i_le : i ≤ s.length) (invariant_outer_j_le : j ≤ s.length) (invariant_outer_fixed_nonletters : ∀ k < i, (OfNat.ofNat 65 ≤ (s[k]?.getD 'A').toNat → OfNat.ofNat 90 < (s[k]?.getD 'A').toNat) → (OfNat.ofNat 97 ≤ (s[k]?.getD 'A').toNat → OfNat.ofNat 122 < (s[k]?.getD 'A').toNat) → res[k]! = s[k]?.getD 'A') (invariant_outer_mask_prefix : ∀ k < i, (decide (OfNat.ofNat 65 ≤ res[k]!.toNat) && decide (res[k]!.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ res[k]!.toNat) && decide (res[k]!.toNat ≤ OfNat.ofNat 122)) = (decide (OfNat.ofNat 65 ≤ (s[k]?.getD 'A').toNat) && decide ((s[k]?.getD 'A').toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ (s[k]?.getD 'A').toNat) && decide ((s[k]?.getD 'A').toNat ≤ OfNat.ofNat 122))) (if_pos : i < s.length) (if_neg : (OfNat.ofNat 65 ≤ (s[i]?.getD 'A').toNat → OfNat.ofNat 90 < (s[i]?.getD 'A').toNat) → OfNat.ofNat 97 ≤ (s[i]?.getD 'A').toNat ∧ (s[i]?.getD 'A').toNat ≤ OfNat.ofNat 122) (invariant_inner_res_size : res_1.size = s.length) (invariant_inner_i_lt : i < s.length) (invariant_inner_j_le : j_1 ≤ s.length) (invariant_inner_ci_letter : OfNat.ofNat 65 ≤ (s[i]?.getD 'A').toNat ∧ (s[i]?.getD 'A').toNat ≤ OfNat.ofNat 90 ∨ OfNat.ofNat 97 ≤ (s[i]?.getD 'A').toNat ∧ (s[i]?.getD 'A').toNat ≤ OfNat.ofNat 122) (invariant_inner_fixed_nonletters_prefix : ∀ k < i, (OfNat.ofNat 65 ≤ (s[k]?.getD 'A').toNat → OfNat.ofNat 90 < (s[k]?.getD 'A').toNat) → (OfNat.ofNat 97 ≤ (s[k]?.getD 'A').toNat → OfNat.ofNat 122 < (s[k]?.getD 'A').toNat) → res_1[k]! = s[k]?.getD 'A') (invariant_inner_mask_prefix : ∀ k < i, (decide (OfNat.ofNat 65 ≤ res_1[k]!.toNat) && decide (res_1[k]!.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ res_1[k]!.toNat) && decide (res_1[k]!.toNat ≤ OfNat.ofNat 122)) = (decide (OfNat.ofNat 65 ≤ (s[k]?.getD 'A').toNat) && decide ((s[k]?.getD 'A').toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ (s[k]?.getD 'A').toNat) && decide ((s[k]?.getD 'A').toNat ≤ OfNat.ofNat 122))) (if_neg_2 : (OfNat.ofNat 65 ≤ (s[j_1 - OfNat.ofNat 1]?.getD 'A').toNat → OfNat.ofNat 90 < (s[j_1 - OfNat.ofNat 1]?.getD 'A').toNat) ∧ (OfNat.ofNat 97 ≤ (s[j_1 - OfNat.ofNat 1]?.getD 'A').toNat → OfNat.ofNat 122 < (s[j_1 - OfNat.ofNat 1]?.getD 'A').toNat)) (invariant_inner_letters_search : List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.take i res_1.toList) = (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.drop j_1 s)).reverse) (invariant_inner_count_search : (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.take i s)).length = (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.drop j_1 s)).length) (invariant_inner_done_found : True) : List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.take i res_1.toList) = (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.drop (j_1 - OfNat.ofNat 1) s)).reverse := by
  classical
  let p : Char → Bool := fun c =>
    decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) ||
      decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)
  have hjpos : 0 < j_1 := Nat.pos_of_ne_zero if_neg_1
  have hjm1_lt : j_1 - 1 < s.length := by
    omega
  have hdrop : List.drop (j_1 - 1) s = s[j_1 - 1] :: List.drop j_1 s := by
    simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hjpos)] using
      (List.drop_eq_getElem_cons (l := s) (i := j_1 - 1) hjm1_lt)
  have hget :
      s[j_1 - 1] = s[j_1 - 1]?.getD 'A' := by
    simp [List.getElem?_eq_getElem hjm1_lt]
  have hnot_upper :
      ¬ (OfNat.ofNat 65 ≤ (s[j_1 - 1]).toNat ∧ (s[j_1 - 1]).toNat ≤ OfNat.ofNat 90) := by
    intro h
    have h1 : OfNat.ofNat 65 ≤ (s[j_1 - 1]?.getD 'A').toNat := by
      simpa [hget] using h.1
    have h2 : OfNat.ofNat 90 < (s[j_1 - 1]?.getD 'A').toNat := if_neg_2.1 h1
    exact (Nat.not_lt_of_le h.2) (by simpa [hget] using h2)
  have hnot_lower :
      ¬ (OfNat.ofNat 97 ≤ (s[j_1 - 1]).toNat ∧ (s[j_1 - 1]).toNat ≤ OfNat.ofNat 122) := by
    intro h
    have h1 : OfNat.ofNat 97 ≤ (s[j_1 - 1]?.getD 'A').toNat := by
      simpa [hget] using h.1
    have h2 : OfNat.ofNat 122 < (s[j_1 - 1]?.getD 'A').toNat := if_neg_2.2 h1
    exact (Nat.not_lt_of_le h.2) (by simpa [hget] using h2)
  have hp_head_false : p (s[j_1 - 1]) = false := by
    by_cases h65 : OfNat.ofNat 65 ≤ (s[j_1 - 1]).toNat
    · have h90 : ¬ (s[j_1 - 1]).toNat ≤ OfNat.ofNat 90 := by
        intro h90
        exact hnot_upper ⟨h65, h90⟩
      by_cases h97 : OfNat.ofNat 97 ≤ (s[j_1 - 1]).toNat
      · have h122 : ¬ (s[j_1 - 1]).toNat ≤ OfNat.ofNat 122 := by
          intro h122
          exact hnot_lower ⟨h97, h122⟩
        simp [p, h65, h90, h97, h122]
      · simp [p, h65, h97, h90]
    · by_cases h97 : OfNat.ofNat 97 ≤ (s[j_1 - 1]).toNat
      · have h122 : ¬ (s[j_1 - 1]).toNat ≤ OfNat.ofNat 122 := by
          intro h122
          exact hnot_lower ⟨h97, h122⟩
        simp [p, h65, h97, h122]
      · simp [p, h65, h97]
  have hfilter_drop :
      List.filter p (List.drop (j_1 - 1) s) = List.filter p (List.drop j_1 s) := by
    rw [hdrop]
    simp [p, hp_head_false]
  calc
    List.filter p (List.take i res_1.toList) = (List.filter p (List.drop j_1 s)).reverse := by
      simpa [p] using invariant_inner_letters_search
    _ = (List.filter p (List.drop (j_1 - 1) s)).reverse := by
      simp [hfilter_drop]

/-
PROVIDED SOLUTION
Same as goal_5: we have `invariant_inner_letters_search` saying `filter f (take i res_1.toList) = (filter f (drop j_1 s)).reverse`. We need to show the same with `drop (j_1 - 1) s` instead of `drop j_1 s`. Since `j_1 ≠ 0` and `j_1 ≤ s.length`, we have `drop (j_1 - 1) s = s[j_1-1] :: drop j_1 s`. The hypothesis `if_neg_2` says `s[j_1-1]` is NOT a letter. So `filter f (drop (j_1 - 1) s) = filter f (drop j_1 s)`. Rewrite with the invariant.
-/
theorem goal_5' (s : List Char) (require_1 : True) (i : ℕ) (j : ℕ) (res : Array Char) (invariant_outer_letters_account : List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.take i res.toList) = (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.drop j s)).reverse) (invariant_outer_lettercount_account : (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.take i s)).length = (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.drop j s)).length) (j_1 : ℕ) (res_1 : Array Char) (if_neg_1 : ¬j_1 = OfNat.ofNat 0) (invariant_outer_res_size : res.size = s.length) (invariant_outer_n_eq_len : True) (invariant_outer_i_le : i ≤ s.length) (invariant_outer_j_le : j ≤ s.length) (invariant_outer_fixed_nonletters : ∀ k < i, (OfNat.ofNat 65 ≤ (s[k]?.getD 'A').toNat → OfNat.ofNat 90 < (s[k]?.getD 'A').toNat) → (OfNat.ofNat 97 ≤ (s[k]?.getD 'A').toNat → OfNat.ofNat 122 < (s[k]?.getD 'A').toNat) → res[k]! = s[k]?.getD 'A') (invariant_outer_mask_prefix : ∀ k < i, (decide (OfNat.ofNat 65 ≤ res[k]!.toNat) && decide (res[k]!.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ res[k]!.toNat) && decide (res[k]!.toNat ≤ OfNat.ofNat 122)) = (decide (OfNat.ofNat 65 ≤ (s[k]?.getD 'A').toNat) && decide ((s[k]?.getD 'A').toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ (s[k]?.getD 'A').toNat) && decide ((s[k]?.getD 'A').toNat ≤ OfNat.ofNat 122))) (if_pos : i < s.length) (if_neg : (OfNat.ofNat 65 ≤ (s[i]?.getD 'A').toNat → OfNat.ofNat 90 < (s[i]?.getD 'A').toNat) → OfNat.ofNat 97 ≤ (s[i]?.getD 'A').toNat ∧ (s[i]?.getD 'A').toNat ≤ OfNat.ofNat 122) (invariant_inner_res_size : res_1.size = s.length) (invariant_inner_i_lt : i < s.length) (invariant_inner_j_le : j_1 ≤ s.length) (invariant_inner_ci_letter : OfNat.ofNat 65 ≤ (s[i]?.getD 'A').toNat ∧ (s[i]?.getD 'A').toNat ≤ OfNat.ofNat 90 ∨ OfNat.ofNat 97 ≤ (s[i]?.getD 'A').toNat ∧ (s[i]?.getD 'A').toNat ≤ OfNat.ofNat 122) (invariant_inner_fixed_nonletters_prefix : ∀ k < i, (OfNat.ofNat 65 ≤ (s[k]?.getD 'A').toNat → OfNat.ofNat 90 < (s[k]?.getD 'A').toNat) → (OfNat.ofNat 97 ≤ (s[k]?.getD 'A').toNat → OfNat.ofNat 122 < (s[k]?.getD 'A').toNat) → res_1[k]! = s[k]?.getD 'A') (invariant_inner_mask_prefix : ∀ k < i, (decide (OfNat.ofNat 65 ≤ res_1[k]!.toNat) && decide (res_1[k]!.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ res_1[k]!.toNat) && decide (res_1[k]!.toNat ≤ OfNat.ofNat 122)) = (decide (OfNat.ofNat 65 ≤ (s[k]?.getD 'A').toNat) && decide ((s[k]?.getD 'A').toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ (s[k]?.getD 'A').toNat) && decide ((s[k]?.getD 'A').toNat ≤ OfNat.ofNat 122))) (if_neg_2 : (OfNat.ofNat 65 ≤ (s[j_1 - OfNat.ofNat 1]?.getD 'A').toNat → OfNat.ofNat 90 < (s[j_1 - OfNat.ofNat 1]?.getD 'A').toNat) ∧ (OfNat.ofNat 97 ≤ (s[j_1 - OfNat.ofNat 1]?.getD 'A').toNat → OfNat.ofNat 122 < (s[j_1 - OfNat.ofNat 1]?.getD 'A').toNat)) (invariant_inner_letters_search : List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.take i res_1.toList) = (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.drop j_1 s)).reverse) (invariant_inner_count_search : (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.take i s)).length = (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.drop j_1 s)).length) (invariant_inner_done_found : True) : List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.take i res_1.toList) = (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.drop (j_1 - OfNat.ofNat 1) s)).reverse := by
  exact goal_5 s require_1 i j res invariant_outer_letters_account invariant_outer_lettercount_account
    j_1 res_1 if_neg_1 invariant_outer_res_size invariant_outer_n_eq_len invariant_outer_i_le
    invariant_outer_j_le invariant_outer_fixed_nonletters invariant_outer_mask_prefix if_pos if_neg
    invariant_inner_res_size invariant_inner_i_lt invariant_inner_j_le invariant_inner_ci_letter
    invariant_inner_fixed_nonletters_prefix invariant_inner_mask_prefix if_neg_2
    invariant_inner_letters_search invariant_inner_count_search invariant_inner_done_found

/-
PROVIDED SOLUTION
Same structure as goal_5: we have `invariant_inner_count_search` saying the lengths of filter on `take i s` and `drop j_1 s` are equal. We need to show the same with `drop (j_1 - 1) s`. Since `j_1 ≠ 0` and `j_1 ≤ s.length`, `drop (j_1 - 1) s = s[j_1-1] :: drop j_1 s`. Since `s[j_1-1]` is NOT a letter (`if_neg_2`), filtering doesn't include it, so `filter f (drop (j_1-1) s) = filter f (drop j_1 s)`. The lengths are the same.
-/
theorem goal_6 (s : List Char) (require_1 : True) (i : ℕ) (j : ℕ) (res : Array Char) (invariant_outer_letters_account : List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.take i res.toList) = (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.drop j s)).reverse) (invariant_outer_lettercount_account : (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.take i s)).length = (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.drop j s)).length) (j_1 : ℕ) (res_1 : Array Char) (if_neg_1 : ¬j_1 = OfNat.ofNat 0) (invariant_outer_res_size : res.size = s.length) (invariant_outer_n_eq_len : True) (invariant_outer_i_le : i ≤ s.length) (invariant_outer_j_le : j ≤ s.length) (invariant_outer_fixed_nonletters : ∀ k < i, (OfNat.ofNat 65 ≤ (s[k]?.getD 'A').toNat → OfNat.ofNat 90 < (s[k]?.getD 'A').toNat) → (OfNat.ofNat 97 ≤ (s[k]?.getD 'A').toNat → OfNat.ofNat 122 < (s[k]?.getD 'A').toNat) → res[k]! = s[k]?.getD 'A') (invariant_outer_mask_prefix : ∀ k < i, (decide (OfNat.ofNat 65 ≤ res[k]!.toNat) && decide (res[k]!.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ res[k]!.toNat) && decide (res[k]!.toNat ≤ OfNat.ofNat 122)) = (decide (OfNat.ofNat 65 ≤ (s[k]?.getD 'A').toNat) && decide ((s[k]?.getD 'A').toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ (s[k]?.getD 'A').toNat) && decide ((s[k]?.getD 'A').toNat ≤ OfNat.ofNat 122))) (if_pos : i < s.length) (if_neg : (OfNat.ofNat 65 ≤ (s[i]?.getD 'A').toNat → OfNat.ofNat 90 < (s[i]?.getD 'A').toNat) → OfNat.ofNat 97 ≤ (s[i]?.getD 'A').toNat ∧ (s[i]?.getD 'A').toNat ≤ OfNat.ofNat 122) (invariant_inner_res_size : res_1.size = s.length) (invariant_inner_i_lt : i < s.length) (invariant_inner_j_le : j_1 ≤ s.length) (invariant_inner_ci_letter : OfNat.ofNat 65 ≤ (s[i]?.getD 'A').toNat ∧ (s[i]?.getD 'A').toNat ≤ OfNat.ofNat 90 ∨ OfNat.ofNat 97 ≤ (s[i]?.getD 'A').toNat ∧ (s[i]?.getD 'A').toNat ≤ OfNat.ofNat 122) (invariant_inner_fixed_nonletters_prefix : ∀ k < i, (OfNat.ofNat 65 ≤ (s[k]?.getD 'A').toNat → OfNat.ofNat 90 < (s[k]?.getD 'A').toNat) → (OfNat.ofNat 97 ≤ (s[k]?.getD 'A').toNat → OfNat.ofNat 122 < (s[k]?.getD 'A').toNat) → res_1[k]! = s[k]?.getD 'A') (invariant_inner_mask_prefix : ∀ k < i, (decide (OfNat.ofNat 65 ≤ res_1[k]!.toNat) && decide (res_1[k]!.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ res_1[k]!.toNat) && decide (res_1[k]!.toNat ≤ OfNat.ofNat 122)) = (decide (OfNat.ofNat 65 ≤ (s[k]?.getD 'A').toNat) && decide ((s[k]?.getD 'A').toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ (s[k]?.getD 'A').toNat) && decide ((s[k]?.getD 'A').toNat ≤ OfNat.ofNat 122))) (if_neg_2 : (OfNat.ofNat 65 ≤ (s[j_1 - OfNat.ofNat 1]?.getD 'A').toNat → OfNat.ofNat 90 < (s[j_1 - OfNat.ofNat 1]?.getD 'A').toNat) ∧ (OfNat.ofNat 97 ≤ (s[j_1 - OfNat.ofNat 1]?.getD 'A').toNat → OfNat.ofNat 122 < (s[j_1 - OfNat.ofNat 1]?.getD 'A').toNat)) (invariant_inner_letters_search : List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.take i res_1.toList) = (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.drop j_1 s)).reverse) (invariant_inner_count_search : (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.take i s)).length = (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.drop j_1 s)).length) (invariant_inner_done_found : True) : (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.take i s)).length = (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.drop (j_1 - OfNat.ofNat 1) s)).length := by
  classical
  let p : Char → Bool := fun c =>
    decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) ||
      decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)
  have hjpos : 0 < j_1 := Nat.pos_of_ne_zero if_neg_1
  have hjm1_lt : j_1 - 1 < s.length := by
    omega
  have hdrop : List.drop (j_1 - 1) s = s[j_1 - 1] :: List.drop j_1 s := by
    simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hjpos)] using
      (List.drop_eq_getElem_cons (l := s) (i := j_1 - 1) hjm1_lt)
  have hget :
      s[j_1 - 1] = s[j_1 - 1]?.getD 'A' := by
    simp [List.getElem?_eq_getElem hjm1_lt]
  have hnot_upper :
      ¬ (OfNat.ofNat 65 ≤ (s[j_1 - 1]).toNat ∧ (s[j_1 - 1]).toNat ≤ OfNat.ofNat 90) := by
    intro h
    have h1 : OfNat.ofNat 65 ≤ (s[j_1 - 1]?.getD 'A').toNat := by
      simpa [hget] using h.1
    have h2 : OfNat.ofNat 90 < (s[j_1 - 1]?.getD 'A').toNat := if_neg_2.1 h1
    exact (Nat.not_lt_of_le h.2) (by simpa [hget] using h2)
  have hnot_lower :
      ¬ (OfNat.ofNat 97 ≤ (s[j_1 - 1]).toNat ∧ (s[j_1 - 1]).toNat ≤ OfNat.ofNat 122) := by
    intro h
    have h1 : OfNat.ofNat 97 ≤ (s[j_1 - 1]?.getD 'A').toNat := by
      simpa [hget] using h.1
    have h2 : OfNat.ofNat 122 < (s[j_1 - 1]?.getD 'A').toNat := if_neg_2.2 h1
    exact (Nat.not_lt_of_le h.2) (by simpa [hget] using h2)
  have hp_head_false : p (s[j_1 - 1]) = false := by
    by_cases h65 : OfNat.ofNat 65 ≤ (s[j_1 - 1]).toNat
    · have h90 : ¬ (s[j_1 - 1]).toNat ≤ OfNat.ofNat 90 := by
        intro h90
        exact hnot_upper ⟨h65, h90⟩
      by_cases h97 : OfNat.ofNat 97 ≤ (s[j_1 - 1]).toNat
      · have h122 : ¬ (s[j_1 - 1]).toNat ≤ OfNat.ofNat 122 := by
          intro h122
          exact hnot_lower ⟨h97, h122⟩
        simp [p, h65, h90, h97, h122]
      · simp [p, h65, h97, h90]
    · by_cases h97 : OfNat.ofNat 97 ≤ (s[j_1 - 1]).toNat
      · have h122 : ¬ (s[j_1 - 1]).toNat ≤ OfNat.ofNat 122 := by
          intro h122
          exact hnot_lower ⟨h97, h122⟩
        simp [p, h65, h97, h122]
      · simp [p, h65, h97]
  have hfilter_drop :
      List.filter p (List.drop (j_1 - 1) s) = List.filter p (List.drop j_1 s) := by
    rw [hdrop]
    simp [p, hp_head_false]
  calc
    (List.filter p (List.take i s)).length = (List.filter p (List.drop j_1 s)).length := by
      simpa [p] using invariant_inner_count_search
    _ = (List.filter p (List.drop (j_1 - 1) s)).length := by
      simp [hfilter_drop]

/-
PROVIDED SOLUTION
We need to prove `postcondition s res_1.toList`, which unfolds to 4 conjuncts:
1. `res_1.toList.length = s.length`: follows from `invariant_outer_res_size` since `res_1.size = s.length` and `Array.toList` preserves length.
2. Non-letters fixed: `invariant_outer_fixed_nonletters` gives this. Need to relate `s[k]?.getD 'A'` to `s[k]!` and `res_1[k]!` - for `k < s.length`, `s[k]?.getD 'A' = s[k]!` (since getD with default on a valid index equals the element). The condition on non-letters (`isLetter s[i]! = false`) matches the negation of the letter condition.
3. Letter mask preserved: `invariant_outer_mask_prefix` gives that `isLetter (res_1[k]!) = isLetter (s[k]!)` for all `k < s.length`. Need to unfold `isLetter` to match the `decide` expressions.
4. `letters result = (letters s).reverse`: From `invariant_outer_letters_account` with `i = s.length` and the letter count accounting. We have `List.take s.length res_1.toList = res_1.toList` (since res_1.size = s.length). Then the `invariant_outer_lettercount_account` tells us `i_2` accounts for the remaining letters in s. Since `(filter f s).length = (filter f (drop i_2 s)).length`, and this combined with `invariant_outer_letters_account` gives us the full reversal.
-/
theorem goal_7 (s : List Char) (require_1 : True) (i_2 : ℕ) (res_1 : Array Char) (invariant_outer_n_eq_len : True) (invariant_outer_i_le : True) (invariant_outer_j_le : i_2 ≤ s.length) (invariant_outer_lettercount_account : (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) s).length = (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.drop i_2 s)).length) (invariant_outer_res_size : res_1.size = s.length) (invariant_outer_fixed_nonletters : ∀ k < s.length, (OfNat.ofNat 65 ≤ (s[k]?.getD 'A').toNat → OfNat.ofNat 90 < (s[k]?.getD 'A').toNat) → (OfNat.ofNat 97 ≤ (s[k]?.getD 'A').toNat → OfNat.ofNat 122 < (s[k]?.getD 'A').toNat) → res_1[k]! = s[k]?.getD 'A') (invariant_outer_mask_prefix : ∀ k < s.length, (decide (OfNat.ofNat 65 ≤ res_1[k]!.toNat) && decide (res_1[k]!.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ res_1[k]!.toNat) && decide (res_1[k]!.toNat ≤ OfNat.ofNat 122)) = (decide (OfNat.ofNat 65 ≤ (s[k]?.getD 'A').toNat) && decide ((s[k]?.getD 'A').toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ (s[k]?.getD 'A').toNat) && decide ((s[k]?.getD 'A').toNat ≤ OfNat.ofNat 122))) (invariant_outer_letters_account : List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.take s.length res_1.toList) = (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.drop i_2 s)).reverse) : postcondition s res_1.toList := by
    refine' ⟨ _, _, _, _ ⟩;
    · grind;
    · intro k hk h;
      convert invariant_outer_fixed_nonletters k hk _ _ <;> simp_all +decide [ isLetter ];
      · cases res_1 ; aesop;
      · unfold isAsciiUpper at h; aesop;
      · unfold isAsciiLower at h; aesop;
    · unfold isLetter; aesop;
    · convert invariant_outer_letters_account using 1;
      · rw [ List.take_of_length_le ] <;> aesop;
      · unfold letters;
        congr! 1;
        have h_filter_eq : List.length (List.filter (fun c => isLetter c) s) = List.length (List.filter (fun c => isLetter c) (List.drop i_2 s)) := by
          convert invariant_outer_lettercount_account using 1;
        have h_filter_eq : List.filter (fun c => isLetter c) s = List.filter (fun c => isLetter c) (List.take i_2 s) ++ List.filter (fun c => isLetter c) (List.drop i_2 s) := by
          rw [ ← List.filter_append, List.take_append_drop ];
        simp_all +decide [ isLetter ];
        rw [ List.filter_eq_nil_iff.mpr ] <;> aesop

end Proof
