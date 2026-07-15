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

section Impl
method ReverseOnlyLetters (s : List Char)
  return (result : List Char)
  require precondition s
  ensures postcondition s result
  do
  -- O(n) time / O(n) space strategy:
  -- 1) Convert to Array for O(1) indexing.
  -- 2) Two pointers i (from left) and j (from right) walk inward.
  -- 3) Non-letters are copied in place; letters are swapped (reversed) by taking
  --    the next letter from the right side.
  let a : Array Char := s.toArray
  let n : Nat := a.size
  let mut res : Array Char := Array.replicate n ('\x00')

  let mut i : Nat := 0
  let mut j : Nat := n

  while i < n
    -- Structural facts
    invariant "outer_res_size" res.size = n
    invariant "outer_n_eq_len" n = s.length
    invariant "outer_i_le" i ≤ n
    invariant "outer_j_le" j ≤ n
    -- Functional correctness on the processed prefix [0,i)
    invariant "outer_fixed_nonletters" ∀ k, k < i → (isLetter (a[k]!) = false) → res[k]! = a[k]!
    invariant "outer_mask_prefix" ∀ k, k < i → isLetter (res[k]!) = isLetter (a[k]!)
    -- Letter accounting: the letters written so far are the reverse of the letters in the consumed suffix.
    invariant "outer_letters_account" letters (res.toList.take i) = (letters (a.toList.drop j)).reverse
    invariant "outer_lettercount_account" (letters (a.toList.take i)).length = (letters (a.toList.drop j)).length
    done_with i = n
    decreasing n - i
  do
    let ci := a[i]!
    if isLetter ci = false then
      -- keep non-letter fixed
      res := res.set! i ci
      i := i + 1
    else
      -- move j left until it points to a letter (or reaches 0)
      let mut done := false
      while done = false
        -- Basic bounds/structure
        invariant "inner_res_size" res.size = n
        invariant "inner_i_lt" i < n
        invariant "inner_j_le" j ≤ n
        invariant "inner_ci_letter" isLetter ci = true
        -- Preserve already-fixed prefix facts inside the search loop (so they transfer to the post-state res)
        invariant "inner_fixed_nonletters_prefix" ∀ k, k < i → (isLetter (a[k]!) = false) → res[k]! = a[k]!
        invariant "inner_mask_prefix" ∀ k, k < i → isLetter (res[k]!) = isLetter (a[k]!)
        -- While searching (done=false), we have not written res[i] yet; the accounting is still for length i.
        invariant "inner_letters_search" done = false → letters (res.toList.take i) = (letters (a.toList.drop j)).reverse
        invariant "inner_count_search" done = false → (letters (a.toList.take i)).length = (letters (a.toList.drop j)).length
        -- When done=true (i.e. at loop exit), we have written res[i] from a[j] and advanced the accounting to i+1.
        invariant "inner_done_found" done = true → (j < n ∧ isLetter (a[j]!) = true ∧ res[i]! = a[j]! ∧
          letters (res.toList.take (i + 1)) = (letters (a.toList.drop j)).reverse ∧
          (letters (a.toList.take (i + 1))).length = (letters (a.toList.drop j)).length)
        done_with done = true
        decreasing j
      do
        if j = 0 then
          done := true
        else
          let j1 := j - 1
          let cj1 := a[j1]!
          if isLetter cj1 then
            -- use this rightmost remaining letter
            res := res.set! i cj1
            j := j1
            done := true
          else
            -- skip non-letter on the right
            j := j1
      i := i + 1

  return res.toList
end Impl

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

section Assertions
-- Test case 1

#assert_same_evaluation #[((ReverseOnlyLetters test1_s).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((ReverseOnlyLetters test2_s).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((ReverseOnlyLetters test3_s).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((ReverseOnlyLetters test4_s).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((ReverseOnlyLetters test5_s).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((ReverseOnlyLetters test6_s).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((ReverseOnlyLetters test7_s).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((ReverseOnlyLetters test8_s).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((ReverseOnlyLetters test9_s).run), DivM.res test9_Expected ]
end Assertions

section Pbt
velvet_plausible_test ReverseOnlyLetters (config := { maxMs := some 20000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000

theorem goal_0
    (s : List Char)
    (i : ℕ)
    (j : ℕ)
    (res : Array Char)
    (invariant_outer_letters_account : List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.take i res.toList) = (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.drop j s)).reverse)
    (invariant_outer_res_size : res.size = s.length)
    (if_pos : i < s.length)
    (if_pos_1 : (OfNat.ofNat 65 ≤ (s[i]?.getD 'A').toNat → OfNat.ofNat 90 < (s[i]?.getD 'A').toNat) ∧ (OfNat.ofNat 97 ≤ (s[i]?.getD 'A').toNat → OfNat.ofNat 122 < (s[i]?.getD 'A').toNat))
    : List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.take (i + OfNat.ofNat 1) (res.toList.set i (s[i]?.getD 'A'))) = (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.drop j s)).reverse := by
  classical

  -- Abbreviate the letter-test predicate used in the invariant/goal.
  let p : Char → Bool := fun c =>
    decide (65 ≤ c.toNat) && decide (c.toNat ≤ 90) ||
    decide (97 ≤ c.toNat) && decide (c.toNat ≤ 122)

  -- The new character written at position i.
  set a : Char := s[i]?.getD 'A' with ha

  have hiSize : i < res.size := by
    simpa [invariant_outer_res_size] using if_pos

  have hiRes : i < res.toList.length := by
    simpa [Array.length_toList] using hiSize

  have hiSet : i < (res.toList.set i a).length := by
    simpa [List.length_set] using hiRes

  -- From `if_pos_1`, show that `a` is not an ASCII letter (so `p a = false`).
  have hp_false : p a = false := by
    have hUpperImp : (65 ≤ a.toNat → 90 < a.toNat) := by
      simpa [a] using if_pos_1.1
    have hLowerImp : (97 ≤ a.toNat → 122 < a.toNat) := by
      simpa [a] using if_pos_1.2

    have hUpper : ¬ (65 ≤ a.toNat ∧ a.toNat ≤ 90) := by
      intro h
      have hlt : 90 < a.toNat := hUpperImp h.1
      exact (Nat.not_lt_of_le h.2) hlt

    have hLower : ¬ (97 ≤ a.toNat ∧ a.toNat ≤ 122) := by
      intro h
      have hlt : 122 < a.toNat := hLowerImp h.1
      exact (Nat.not_lt_of_le h.2) hlt

    have hUpperB : (decide (65 ≤ a.toNat) && decide (a.toNat ≤ 90)) = false := by
      by_cases hb : (decide (65 ≤ a.toNat) && decide (a.toNat ≤ 90)) = true
      · have h' : decide (65 ≤ a.toNat) = true ∧ decide (a.toNat ≤ 90) = true :=
          (Bool.and_eq_true_iff).1 hb
        have h1 : 65 ≤ a.toNat := by simpa using h'.1
        have h2 : a.toNat ≤ 90 := by simpa using h'.2
        exact (hUpper ⟨h1, h2⟩).elim
      · cases hbool : (decide (65 ≤ a.toNat) && decide (a.toNat ≤ 90))
        · simpa [hbool]
        · exfalso
          exact hb hbool

    have hLowerB : (decide (97 ≤ a.toNat) && decide (a.toNat ≤ 122)) = false := by
      by_cases hb : (decide (97 ≤ a.toNat) && decide (a.toNat ≤ 122)) = true
      · have h' : decide (97 ≤ a.toNat) = true ∧ decide (a.toNat ≤ 122) = true :=
          (Bool.and_eq_true_iff).1 hb
        have h1 : 97 ≤ a.toNat := by simpa using h'.1
        have h2 : a.toNat ≤ 122 := by simpa using h'.2
        exact (hLower ⟨h1, h2⟩).elim
      · cases hbool : (decide (97 ≤ a.toNat) && decide (a.toNat ≤ 122))
        · simpa [hbool]
        · exfalso
          exact hb hbool

    simp [p, hUpperB, hLowerB]

  have htake : List.take (i + 1) (res.toList.set i a) = List.take i res.toList ++ [a] := by
    have h := (List.take_succ_eq_append_getElem (i := i) (l := res.toList.set i a) hiSet)

    have htakei : (res.toList.set i a).take i = res.toList.take i := by
      simpa using
        (List.take_set_of_le (l := res.toList) (i := i) (j := i) (a := a) (le_rfl))

    have hget : (res.toList.set i a)[i] = a := by
      -- specialize `getElem_set` to the updated index
      simpa using
        (List.getElem_set (l := res.toList) (i := i) (j := i) (a := a) (h := hiSet))

    simpa [htakei, hget] using h

  -- Updating a non-letter at position i does not change the filtered letters in the prefix.
  have hfilter : List.filter p (List.take (i + 1) (res.toList.set i a)) =
      List.filter p (List.take i res.toList) := by
    simp [htake, List.filter_append, List.filter_singleton, hp_false]

  -- Conclude using the existing accounting invariant.
  simpa [p, a] using (hfilter.trans (by simpa [p] using invariant_outer_letters_account))

theorem goal_1
    (s : List Char)
    (i : ℕ)
    (j : ℕ)
    (invariant_outer_lettercount_account : (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.take i s)).length = (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.drop j s)).length)
    (if_pos : i < s.length)
    (if_pos_1 : (OfNat.ofNat 65 ≤ (s[i]?.getD 'A').toNat → OfNat.ofNat 90 < (s[i]?.getD 'A').toNat) ∧ (OfNat.ofNat 97 ≤ (s[i]?.getD 'A').toNat → OfNat.ofNat 122 < (s[i]?.getD 'A').toNat))
    : (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.take (i + OfNat.ofNat 1) s)).length = (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.drop j s)).length := by
  classical
  let p : Char → Bool := fun c =>
    decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) ||
      decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)

  have inv' : (List.filter p (List.take i s)).length = (List.filter p (List.drop j s)).length := by
    simpa [p] using invariant_outer_lettercount_account

  have hi : i < s.length := if_pos

  have hci1 : OfNat.ofNat 65 ≤ (s[i]'hi).toNat → OfNat.ofNat 90 < (s[i]'hi).toNat := by
    simpa [List.getElem?_eq_getElem, hi] using if_pos_1.1
  have hci2 : OfNat.ofNat 97 ≤ (s[i]'hi).toNat → OfNat.ofNat 122 < (s[i]'hi).toNat := by
    simpa [List.getElem?_eq_getElem, hi] using if_pos_1.2

  set t : Nat := (s[i]'hi).toNat

  have hand1 : (decide (OfNat.ofNat 65 ≤ t) && decide (t ≤ OfNat.ofNat 90)) = false := by
    by_cases h65 : OfNat.ofNat 65 ≤ t
    · have hgt : OfNat.ofNat 90 < t := by
        have : OfNat.ofNat 90 < (s[i]'hi).toNat := hci1 h65
        simpa [t] using this
      have hnotle : ¬ t ≤ OfNat.ofNat 90 := Nat.not_le_of_gt hgt
      have hdec65 : decide (OfNat.ofNat 65 ≤ t) = true := decide_eq_true h65
      have hdecle : decide (t ≤ OfNat.ofNat 90) = false := (decide_eq_false_iff_not).2 hnotle
      simp [hdec65, hdecle]
    · have hdec65 : decide (OfNat.ofNat 65 ≤ t) = false := (decide_eq_false_iff_not).2 h65
      simp [hdec65]

  have hand2 : (decide (OfNat.ofNat 97 ≤ t) && decide (t ≤ OfNat.ofNat 122)) = false := by
    by_cases h97 : OfNat.ofNat 97 ≤ t
    · have hgt : OfNat.ofNat 122 < t := by
        have : OfNat.ofNat 122 < (s[i]'hi).toNat := hci2 h97
        simpa [t] using this
      have hnotle : ¬ t ≤ OfNat.ofNat 122 := Nat.not_le_of_gt hgt
      have hdec97 : decide (OfNat.ofNat 97 ≤ t) = true := decide_eq_true h97
      have hdecle : decide (t ≤ OfNat.ofNat 122) = false := (decide_eq_false_iff_not).2 hnotle
      simp [hdec97, hdecle]
    · have hdec97 : decide (OfNat.ofNat 97 ≤ t) = false := (decide_eq_false_iff_not).2 h97
      simp [hdec97]

  have hp : p (s[i]'hi) = false := by
    dsimp [p]
    simpa [t, hand1, hand2]

  have hsingle : List.filter p [s[i]'hi] = [] := by
    simpa [List.filter_singleton, hp]

  have main : (List.filter p (List.take (i + 1) s)).length = (List.filter p (List.drop j s)).length := by
    calc
      (List.filter p (List.take (i + 1) s)).length =
          (List.filter p (List.take i s ++ [s[i]'hi])).length := by
            -- rewrite take (i+1)
            simpa using
              congrArg (fun l => (List.filter p l).length)
                (List.take_succ_eq_append_getElem (l := s) (i := i) hi)
      _ = (List.filter p (List.take i s) ++ List.filter p [s[i]'hi]).length := by
            simpa using
              congrArg List.length
                (List.filter_append (p := p) (List.take i s) [s[i]'hi])
      _ = (List.filter p (List.take i s)).length := by
            simp [hsingle]
      _ = (List.filter p (List.drop j s)).length := inv'

  -- return to the original predicate
  simpa [p] using main

theorem goal_2
    (s : List Char)
    (i : ℕ)
    (res_1 : Array Char)
    (invariant_inner_i_lt : i < s.length)
    (invariant_inner_ci_letter : OfNat.ofNat 65 ≤ (s[i]?.getD 'A').toNat ∧ (s[i]?.getD 'A').toNat ≤ OfNat.ofNat 90 ∨ OfNat.ofNat 97 ≤ (s[i]?.getD 'A').toNat ∧ (s[i]?.getD 'A').toNat ≤ OfNat.ofNat 122)
    (invariant_inner_count_search : (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.take i s)).length = (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) s).length)
    : OfNat.ofNat 0 < s.length ∧ (OfNat.ofNat 65 ≤ (s[OfNat.ofNat 0]?.getD 'A').toNat ∧ (s[OfNat.ofNat 0]?.getD 'A').toNat ≤ OfNat.ofNat 90 ∨ OfNat.ofNat 97 ≤ (s[OfNat.ofNat 0]?.getD 'A').toNat ∧ (s[OfNat.ofNat 0]?.getD 'A').toNat ≤ OfNat.ofNat 122) ∧ res_1[i]! = s[OfNat.ofNat 0]?.getD 'A' ∧ List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.take (i + OfNat.ofNat 1) res_1.toList) = (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) s).reverse ∧ (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.take (i + OfNat.ofNat 1) s)).length = (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) s).length := by
  classical
  -- Derive a contradiction from `invariant_inner_ci_letter` and `invariant_inner_count_search`.
  let p : Char → Bool := fun c =>
    decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) ||
      decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)

  have hi : i < s.length := invariant_inner_i_lt

  have hci : (OfNat.ofNat 65 ≤ (s[i]).toNat ∧ (s[i]).toNat ≤ OfNat.ofNat 90) ∨
      (OfNat.ofNat 97 ≤ (s[i]).toNat ∧ (s[i]).toNat ≤ OfNat.ofNat 122) := by
    simpa [List.getElem?_eq_getElem hi] using invariant_inner_ci_letter

  have hp : p (s[i]) = true := by
    rcases hci with hU | hL
    · rcases hU with ⟨h65, h90⟩
      simp [p, h65, h90]
    · rcases hL with ⟨h97, h122⟩
      simp [p, h97, h122]

  have htake : List.take i.succ s = List.take i s ++ [s[i]] := by
    simpa [Nat.succ_eq_add_one] using
      (List.take_succ_eq_append_getElem (l := s) (i := i) hi)

  have hfilter : List.filter p (List.take i.succ s) =
      List.filter p (List.take i s) ++ [s[i]] := by
    rw [htake]
    calc
      List.filter p (List.take i s ++ [s[i]])
          = List.filter p (List.take i s) ++ List.filter p [s[i]] := by
              exact List.filter_append (p := p) (List.take i s) [s[i]]
      _ = List.filter p (List.take i s) ++ [s[i]] := by
              simp [List.filter_singleton, hp]

  have hlen_succ : (List.filter p (List.take i.succ s)).length =
      (List.filter p (List.take i s)).length + 1 := by
    rw [hfilter]
    simp

  have hEq : (List.filter p (List.take i s)).length = (List.filter p s).length := by
    simpa [p] using invariant_inner_count_search

  have hsub : List.Sublist (List.filter p (List.take i.succ s)) (List.filter p s) := by
    exact List.Sublist.filter p (List.take_sublist i.succ s)

  have hle : (List.filter p (List.take i.succ s)).length ≤ (List.filter p s).length := by
    exact List.Sublist.length_le hsub

  have hcontra : False := by
    have hs : Nat.succ (List.filter p s).length ≤ (List.filter p s).length := by
      have : (List.filter p s).length + 1 ≤ (List.filter p s).length := by
        calc
          (List.filter p s).length + 1
              = (List.filter p (List.take i s)).length + 1 := by simpa [hEq]
          _ = (List.filter p (List.take i.succ s)).length := by
                simpa [Nat.succ_eq_add_one] using (Eq.symm hlen_succ)
          _ ≤ (List.filter p s).length := hle
      simpa [Nat.succ_eq_add_one] using this
    exact Nat.not_succ_le_self _ hs

  exact False.elim hcontra

theorem goal_3
    (s : List Char)
    (i : ℕ)
    (invariant_inner_i_lt : i < s.length)
    (invariant_inner_ci_letter : OfNat.ofNat 65 ≤ (s[i]?.getD 'A').toNat ∧ (s[i]?.getD 'A').toNat ≤ OfNat.ofNat 90 ∨ OfNat.ofNat 97 ≤ (s[i]?.getD 'A').toNat ∧ (s[i]?.getD 'A').toNat ≤ OfNat.ofNat 122)
    (invariant_inner_count_search : (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.take i s)).length = (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) s).length)
    : False := by
    classical

    -- the boolean predicate used by all `List.filter` occurrences
    let p : Char → Bool := fun c =>
      decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) ||
        decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)

    have hi : i < s.length := invariant_inner_i_lt

    have hci_letter :
        (OfNat.ofNat 65 ≤ (s[i]'hi).toNat ∧ (s[i]'hi).toNat ≤ OfNat.ofNat 90) ∨
          (OfNat.ofNat 97 ≤ (s[i]'hi).toNat ∧ (s[i]'hi).toNat ≤ OfNat.ofNat 122) := by
      simpa [List.getD_getElem?, hi] using invariant_inner_ci_letter

    have hpci : p (s[i]'hi) = true := by
      cases hci_letter with
      | inl h =>
        have h1 : OfNat.ofNat 65 ≤ (s[i]'hi).toNat := h.1
        have h2 : (s[i]'hi).toNat ≤ OfNat.ofNat 90 := h.2
        simp [p, h1, h2]
      | inr h =>
        have h1 : OfNat.ofNat 97 ≤ (s[i]'hi).toNat := h.1
        have h2 : (s[i]'hi).toNat ≤ OfNat.ofNat 122 := h.2
        simp [p, h1, h2]

    have htake : s.take (i + 1) = s.take i ++ [s[i]'hi] := by
      simpa using (List.take_succ_eq_append_getElem (l := s) (i := i) hi)

    have hsingle : (List.filter p [s[i]'hi]).length = 1 := by
      -- filtering a singleton keeps it because `p` is true on that element
      simp [List.filter, hpci]

    have hlen_succ :
        (List.filter p (s.take (i + 1))).length = (List.filter p (s.take i)).length + 1 := by
      -- expand `take (i+1)` and distribute `filter` over append
      rw [htake]
      rw [List.filter_append]
      -- now just compute lengths
      simp [List.length_append, hsingle, Nat.add_assoc]

    have hle : (List.filter p (s.take (i + 1))).length ≤ (List.filter p s).length := by
      have hsub : List.Sublist (List.filter p (s.take (i + 1))) (List.filter p s) := by
        exact (List.Sublist.filter p (List.take_sublist (i + 1) s))
      exact List.Sublist.length_le hsub

    have hEq : (List.filter p (s.take i)).length = (List.filter p s).length := by
      simpa [p] using invariant_inner_count_search

    have hle' : (List.filter p (s.take i)).length + 1 ≤ (List.filter p s).length := by
      simpa [hlen_succ] using hle

    have hcontr : (List.filter p s).length + 1 ≤ (List.filter p s).length := by
      simpa [hEq] using hle'

    have hs : Nat.succ (List.filter p s).length ≤ (List.filter p s).length := by
      simpa [Nat.succ_eq_add_one] using hcontr

    exact Nat.not_succ_le_self _ hs

theorem goal_4
    (s : List Char)
    (i : ℕ)
    (j : ℕ)
    (j_1 : ℕ)
    (res_1 : Array Char)
    (if_neg_1 : ¬j_1 = OfNat.ofNat 0)
    (invariant_inner_res_size : res_1.size = s.length)
    (invariant_inner_i_lt : i < s.length)
    (invariant_inner_j_le : j_1 ≤ s.length)
    (invariant_inner_ci_letter : OfNat.ofNat 65 ≤ (s[i]?.getD 'A').toNat ∧ (s[i]?.getD 'A').toNat ≤ OfNat.ofNat 90 ∨ OfNat.ofNat 97 ≤ (s[i]?.getD 'A').toNat ∧ (s[i]?.getD 'A').toNat ≤ OfNat.ofNat 122)
    (if_pos_2 : OfNat.ofNat 65 ≤ (s[j_1 - OfNat.ofNat 1]?.getD 'A').toNat ∧ (s[j_1 - OfNat.ofNat 1]?.getD 'A').toNat ≤ OfNat.ofNat 90 ∨ OfNat.ofNat 97 ≤ (s[j_1 - OfNat.ofNat 1]?.getD 'A').toNat ∧ (s[j_1 - OfNat.ofNat 1]?.getD 'A').toNat ≤ OfNat.ofNat 122)
    (invariant_inner_letters_search : List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.take i res_1.toList) = (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.drop j_1 s)).reverse)
    (invariant_inner_count_search : (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.take i s)).length = (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.drop j_1 s)).length)
    : j_1 - OfNat.ofNat 1 < s.length ∧ (OfNat.ofNat 65 ≤ (s[j_1 - OfNat.ofNat 1]?.getD 'A').toNat ∧ (s[j_1 - OfNat.ofNat 1]?.getD 'A').toNat ≤ OfNat.ofNat 90 ∨ OfNat.ofNat 97 ≤ (s[j_1 - OfNat.ofNat 1]?.getD 'A').toNat ∧ (s[j_1 - OfNat.ofNat 1]?.getD 'A').toNat ≤ OfNat.ofNat 122) ∧ (res_1.setIfInBounds i (s[j_1 - OfNat.ofNat 1]?.getD 'A'))[i]! = s[j_1 - OfNat.ofNat 1]?.getD 'A' ∧ List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.take (i + OfNat.ofNat 1) (res_1.toList.set i (s[j_1 - OfNat.ofNat 1]?.getD 'A'))) = (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.drop (j_1 - OfNat.ofNat 1) s)).reverse ∧ (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.take (i + OfNat.ofNat 1) s)).length = (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.drop (j_1 - OfNat.ofNat 1) s)).length := by
  classical
  let p : Char → Bool := fun c =>
    decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) ||
      decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)
  let cj : Char := s[j_1 - 1]?.getD 'A'

  have hjm1_lt_len : j_1 - 1 < s.length :=
    lt_of_lt_of_le (Nat.sub_one_lt if_neg_1) invariant_inner_j_le

  have hi_lt_size : i < res_1.size := by
    simpa [invariant_inner_res_size] using invariant_inner_i_lt
  have hi_lt_list : i < res_1.toList.length := by
    simpa [Array.length_toList] using hi_lt_size

  have hp_cj : p cj = true := by
    rcases if_pos_2 with hU | hL
    · have h1 : (OfNat.ofNat 65 : Nat) ≤ cj.toNat := by simpa [cj] using hU.1
      have h2 : cj.toNat ≤ (OfNat.ofNat 90 : Nat) := by simpa [cj] using hU.2
      simp [p, h1, h2]
    · have h1 : (OfNat.ofNat 97 : Nat) ≤ cj.toNat := by simpa [cj] using hL.1
      have h2 : cj.toNat ≤ (OfNat.ofNat 122 : Nat) := by simpa [cj] using hL.2
      simp [p, h1, h2]

  have hset_get : (res_1.setIfInBounds i cj)[i]! = cj := by
    simp [Array.setIfInBounds, hi_lt_size]

  have ht_take_set : List.take (i + 1) (res_1.toList.set i cj) = List.take i res_1.toList ++ [cj] := by
    have h0 : (res_1.toList.set i cj).take (i + 1) = (res_1.toList.take i) ++ [cj] := by
      calc
        (res_1.toList.set i cj).take (i + 1)
            = (res_1.toList.take (i + 1)).set i cj := by
                simpa using (List.take_set (l := res_1.toList) (i := i + 1) (j := i) (a := cj))
        _ = ((res_1.toList.take i ++ [res_1.toList[i]]).set i cj) := by
                simp [List.take_succ_eq_append_getElem hi_lt_list]
        _ = res_1.toList.take i ++ [cj] := by
                have hslen : (res_1.toList.take i).length = i :=
                  List.length_take_of_le (Nat.le_of_lt hi_lt_list)
                calc
                  (res_1.toList.take i ++ [res_1.toList[i]]).set i cj
                      = res_1.toList.take i ++ ([res_1.toList[i]].set (i - (res_1.toList.take i).length) cj) := by
                          simpa using
                            (List.set_append_right (s := res_1.toList.take i) (t := [res_1.toList[i]]) (i := i) (x := cj)
                              (by simpa [hslen]))
                  _ = res_1.toList.take i ++ [cj] := by
                          simp [hslen]
    simpa [List.take] using h0

  have hfilter_take :
      List.filter p (List.take (i + 1) (res_1.toList.set i cj)) =
        List.filter p (List.take i res_1.toList) ++ [cj] := by
    have hf :
        List.filter p (List.take i res_1.toList ++ [cj]) =
          List.filter p (List.take i res_1.toList) ++ List.filter p [cj] := by
      exact List.filter_append (p := p) (List.take i res_1.toList) [cj]
    have hsingle : List.filter p [cj] = [cj] := by
      simp [List.filter, hp_cj]
    simpa [ht_take_set, hf, hsingle]

  have hdrop_cons : List.drop (j_1 - 1) s = s[j_1 - 1] :: List.drop j_1 s := by
    have h1le : 1 ≤ j_1 := Nat.succ_le_of_lt (Nat.pos_of_ne_zero if_neg_1)
    simpa [Nat.sub_add_cancel h1le] using (List.drop_eq_getElem_cons (l := s) (i := j_1 - 1) hjm1_lt_len)

  have hget_cj : s[j_1 - 1] = cj := by
    simp [cj, List.get?, hjm1_lt_len]

  have hdrop_cons' : List.drop (j_1 - 1) s = cj :: List.drop j_1 s := by
    simpa [hget_cj] using hdrop_cons

  have hfilter_drop_rev :
      (List.filter p (List.drop (j_1 - 1) s)).reverse =
        (List.filter p (List.drop j_1 s)).reverse ++ [cj] := by
    simp [hdrop_cons', List.filter_cons, hp_cj, List.reverse_cons]

  have hinv : List.filter p (List.take i res_1.toList) = (List.filter p (List.drop j_1 s)).reverse := by
    simpa [p] using invariant_inner_letters_search

  have hletters :
      List.filter p (List.take (i + 1) (res_1.toList.set i cj)) =
        (List.filter p (List.drop (j_1 - 1) s)).reverse := by
    calc
      List.filter p (List.take (i + 1) (res_1.toList.set i cj))
          = List.filter p (List.take i res_1.toList) ++ [cj] := hfilter_take
      _ = (List.filter p (List.drop j_1 s)).reverse ++ [cj] := by simpa [hinv]
      _ = (List.filter p (List.drop (j_1 - 1) s)).reverse := by
            simpa using (Eq.symm hfilter_drop_rev)

  have hp_si : p (s[i]?.getD 'A') = true := by
    rcases invariant_inner_ci_letter with hU | hL
    · have h1 : (OfNat.ofNat 65 : Nat) ≤ (s[i]?.getD 'A').toNat := hU.1
      have h2 : (s[i]?.getD 'A').toNat ≤ (OfNat.ofNat 90 : Nat) := hU.2
      simp [p, h1, h2]
    · have h1 : (OfNat.ofNat 97 : Nat) ≤ (s[i]?.getD 'A').toNat := hL.1
      have h2 : (s[i]?.getD 'A').toNat ≤ (OfNat.ofNat 122 : Nat) := hL.2
      simp [p, h1, h2]

  have hget_si : s[i] = s[i]?.getD 'A' := by
    simp [List.get?, invariant_inner_i_lt]
  have hp_si' : p (s[i]) = true := by
    simpa [hget_si] using hp_si

  have hlen_take :
      (List.filter p (List.take (i + 1) s)).length = (List.filter p (List.take i s)).length + 1 := by
    have ht : List.take (i + 1) s = List.take i s ++ [s[i]] := by
      simpa using (List.take_succ_eq_append_getElem (l := s) (i := i) invariant_inner_i_lt)
    rw [ht]
    have hf :
        List.filter p (List.take i s ++ [s[i]]) =
          List.filter p (List.take i s) ++ List.filter p [s[i]] := by
      exact List.filter_append (p := p) (List.take i s) [s[i]]
    rw [hf]
    simp [List.filter, hp_si', List.length_append]

  have hlen_drop :
      (List.filter p (List.drop (j_1 - 1) s)).length = (List.filter p (List.drop j_1 s)).length + 1 := by
    rw [hdrop_cons']
    simp [List.filter_cons, hp_cj]

  have hcount0 : (List.filter p (List.take i s)).length = (List.filter p (List.drop j_1 s)).length := by
    simpa [p] using invariant_inner_count_search

  have hcount :
      (List.filter p (List.take (i + 1) s)).length = (List.filter p (List.drop (j_1 - 1) s)).length := by
    have hplus : (List.filter p (List.take i s)).length + 1 = (List.filter p (List.drop j_1 s)).length + 1 :=
      congrArg (fun n => n + 1) hcount0
    calc
      (List.filter p (List.take (i + 1) s)).length
          = (List.filter p (List.take i s)).length + 1 := hlen_take
      _ = (List.filter p (List.drop j_1 s)).length + 1 := hplus
      _ = (List.filter p (List.drop (j_1 - 1) s)).length := by
            simpa using (Eq.symm hlen_drop)

  refine And.intro hjm1_lt_len ?_
  refine And.intro if_pos_2 ?_
  refine And.intro ?_ ?_
  · simpa [cj] using hset_get
  refine And.intro ?_ ?_
  · simpa [p, cj] using hletters
  · simpa [p] using hcount

theorem goal_5
    (s : List Char)
    (require_1 : True)
    (i : ℕ)
    (j : ℕ)
    (res : Array Char)
    (invariant_outer_letters_account : List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.take i res.toList) = (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.drop j s)).reverse)
    (invariant_outer_lettercount_account : (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.take i s)).length = (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.drop j s)).length)
    (j_1 : ℕ)
    (res_1 : Array Char)
    (if_neg_1 : ¬j_1 = OfNat.ofNat 0)
    (invariant_outer_res_size : res.size = s.length)
    (invariant_outer_n_eq_len : True)
    (invariant_outer_i_le : i ≤ s.length)
    (invariant_outer_j_le : j ≤ s.length)
    (invariant_outer_fixed_nonletters : ∀ k < i, (OfNat.ofNat 65 ≤ (s[k]?.getD 'A').toNat → OfNat.ofNat 90 < (s[k]?.getD 'A').toNat) → (OfNat.ofNat 97 ≤ (s[k]?.getD 'A').toNat → OfNat.ofNat 122 < (s[k]?.getD 'A').toNat) → res[k]! = s[k]?.getD 'A')
    (invariant_outer_mask_prefix : ∀ k < i, (decide (OfNat.ofNat 65 ≤ res[k]!.toNat) && decide (res[k]!.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ res[k]!.toNat) && decide (res[k]!.toNat ≤ OfNat.ofNat 122)) = (decide (OfNat.ofNat 65 ≤ (s[k]?.getD 'A').toNat) && decide ((s[k]?.getD 'A').toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ (s[k]?.getD 'A').toNat) && decide ((s[k]?.getD 'A').toNat ≤ OfNat.ofNat 122)))
    (if_pos : i < s.length)
    (if_neg : (OfNat.ofNat 65 ≤ (s[i]?.getD 'A').toNat → OfNat.ofNat 90 < (s[i]?.getD 'A').toNat) → OfNat.ofNat 97 ≤ (s[i]?.getD 'A').toNat ∧ (s[i]?.getD 'A').toNat ≤ OfNat.ofNat 122)
    (invariant_inner_res_size : res_1.size = s.length)
    (invariant_inner_i_lt : i < s.length)
    (invariant_inner_j_le : j_1 ≤ s.length)
    (invariant_inner_ci_letter : OfNat.ofNat 65 ≤ (s[i]?.getD 'A').toNat ∧ (s[i]?.getD 'A').toNat ≤ OfNat.ofNat 90 ∨ OfNat.ofNat 97 ≤ (s[i]?.getD 'A').toNat ∧ (s[i]?.getD 'A').toNat ≤ OfNat.ofNat 122)
    (invariant_inner_fixed_nonletters_prefix : ∀ k < i, (OfNat.ofNat 65 ≤ (s[k]?.getD 'A').toNat → OfNat.ofNat 90 < (s[k]?.getD 'A').toNat) → (OfNat.ofNat 97 ≤ (s[k]?.getD 'A').toNat → OfNat.ofNat 122 < (s[k]?.getD 'A').toNat) → res_1[k]! = s[k]?.getD 'A')
    (invariant_inner_mask_prefix : ∀ k < i, (decide (OfNat.ofNat 65 ≤ res_1[k]!.toNat) && decide (res_1[k]!.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ res_1[k]!.toNat) && decide (res_1[k]!.toNat ≤ OfNat.ofNat 122)) = (decide (OfNat.ofNat 65 ≤ (s[k]?.getD 'A').toNat) && decide ((s[k]?.getD 'A').toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ (s[k]?.getD 'A').toNat) && decide ((s[k]?.getD 'A').toNat ≤ OfNat.ofNat 122)))
    (if_neg_2 : (OfNat.ofNat 65 ≤ (s[j_1 - OfNat.ofNat 1]?.getD 'A').toNat → OfNat.ofNat 90 < (s[j_1 - OfNat.ofNat 1]?.getD 'A').toNat) ∧ (OfNat.ofNat 97 ≤ (s[j_1 - OfNat.ofNat 1]?.getD 'A').toNat → OfNat.ofNat 122 < (s[j_1 - OfNat.ofNat 1]?.getD 'A').toNat))
    (invariant_inner_letters_search : List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.take i res_1.toList) = (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.drop j_1 s)).reverse)
    (invariant_inner_count_search : (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.take i s)).length = (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.drop j_1 s)).length)
    (invariant_inner_done_found : True)
    : List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.take i res_1.toList) = (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.drop (j_1 - OfNat.ofNat 1) s)).reverse := by
    sorry



theorem goal_5
    (s : List Char)
    (require_1 : True)
    (i : ℕ)
    (j : ℕ)
    (res : Array Char)
    (invariant_outer_letters_account : List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.take i res.toList) = (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.drop j s)).reverse)
    (invariant_outer_lettercount_account : (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.take i s)).length = (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.drop j s)).length)
    (j_1 : ℕ)
    (res_1 : Array Char)
    (if_neg_1 : ¬j_1 = OfNat.ofNat 0)
    (invariant_outer_res_size : res.size = s.length)
    (invariant_outer_n_eq_len : True)
    (invariant_outer_i_le : i ≤ s.length)
    (invariant_outer_j_le : j ≤ s.length)
    (invariant_outer_fixed_nonletters : ∀ k < i, (OfNat.ofNat 65 ≤ (s[k]?.getD 'A').toNat → OfNat.ofNat 90 < (s[k]?.getD 'A').toNat) → (OfNat.ofNat 97 ≤ (s[k]?.getD 'A').toNat → OfNat.ofNat 122 < (s[k]?.getD 'A').toNat) → res[k]! = s[k]?.getD 'A')
    (invariant_outer_mask_prefix : ∀ k < i, (decide (OfNat.ofNat 65 ≤ res[k]!.toNat) && decide (res[k]!.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ res[k]!.toNat) && decide (res[k]!.toNat ≤ OfNat.ofNat 122)) = (decide (OfNat.ofNat 65 ≤ (s[k]?.getD 'A').toNat) && decide ((s[k]?.getD 'A').toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ (s[k]?.getD 'A').toNat) && decide ((s[k]?.getD 'A').toNat ≤ OfNat.ofNat 122)))
    (if_pos : i < s.length)
    (if_neg : (OfNat.ofNat 65 ≤ (s[i]?.getD 'A').toNat → OfNat.ofNat 90 < (s[i]?.getD 'A').toNat) → OfNat.ofNat 97 ≤ (s[i]?.getD 'A').toNat ∧ (s[i]?.getD 'A').toNat ≤ OfNat.ofNat 122)
    (invariant_inner_res_size : res_1.size = s.length)
    (invariant_inner_i_lt : i < s.length)
    (invariant_inner_j_le : j_1 ≤ s.length)
    (invariant_inner_ci_letter : OfNat.ofNat 65 ≤ (s[i]?.getD 'A').toNat ∧ (s[i]?.getD 'A').toNat ≤ OfNat.ofNat 90 ∨ OfNat.ofNat 97 ≤ (s[i]?.getD 'A').toNat ∧ (s[i]?.getD 'A').toNat ≤ OfNat.ofNat 122)
    (invariant_inner_fixed_nonletters_prefix : ∀ k < i, (OfNat.ofNat 65 ≤ (s[k]?.getD 'A').toNat → OfNat.ofNat 90 < (s[k]?.getD 'A').toNat) → (OfNat.ofNat 97 ≤ (s[k]?.getD 'A').toNat → OfNat.ofNat 122 < (s[k]?.getD 'A').toNat) → res_1[k]! = s[k]?.getD 'A')
    (invariant_inner_mask_prefix : ∀ k < i, (decide (OfNat.ofNat 65 ≤ res_1[k]!.toNat) && decide (res_1[k]!.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ res_1[k]!.toNat) && decide (res_1[k]!.toNat ≤ OfNat.ofNat 122)) = (decide (OfNat.ofNat 65 ≤ (s[k]?.getD 'A').toNat) && decide ((s[k]?.getD 'A').toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ (s[k]?.getD 'A').toNat) && decide ((s[k]?.getD 'A').toNat ≤ OfNat.ofNat 122)))
    (if_neg_2 : (OfNat.ofNat 65 ≤ (s[j_1 - OfNat.ofNat 1]?.getD 'A').toNat → OfNat.ofNat 90 < (s[j_1 - OfNat.ofNat 1]?.getD 'A').toNat) ∧ (OfNat.ofNat 97 ≤ (s[j_1 - OfNat.ofNat 1]?.getD 'A').toNat → OfNat.ofNat 122 < (s[j_1 - OfNat.ofNat 1]?.getD 'A').toNat))
    (invariant_inner_letters_search : List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.take i res_1.toList) = (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.drop j_1 s)).reverse)
    (invariant_inner_count_search : (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.take i s)).length = (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.drop j_1 s)).length)
    (invariant_inner_done_found : True)
    : List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.take i res_1.toList) = (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.drop (j_1 - OfNat.ofNat 1) s)).reverse := by
    sorry

theorem goal_6
    (s : List Char)
    (require_1 : True)
    (i : ℕ)
    (j : ℕ)
    (res : Array Char)
    (invariant_outer_letters_account : List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.take i res.toList) = (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.drop j s)).reverse)
    (invariant_outer_lettercount_account : (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.take i s)).length = (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.drop j s)).length)
    (j_1 : ℕ)
    (res_1 : Array Char)
    (if_neg_1 : ¬j_1 = OfNat.ofNat 0)
    (invariant_outer_res_size : res.size = s.length)
    (invariant_outer_n_eq_len : True)
    (invariant_outer_i_le : i ≤ s.length)
    (invariant_outer_j_le : j ≤ s.length)
    (invariant_outer_fixed_nonletters : ∀ k < i, (OfNat.ofNat 65 ≤ (s[k]?.getD 'A').toNat → OfNat.ofNat 90 < (s[k]?.getD 'A').toNat) → (OfNat.ofNat 97 ≤ (s[k]?.getD 'A').toNat → OfNat.ofNat 122 < (s[k]?.getD 'A').toNat) → res[k]! = s[k]?.getD 'A')
    (invariant_outer_mask_prefix : ∀ k < i, (decide (OfNat.ofNat 65 ≤ res[k]!.toNat) && decide (res[k]!.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ res[k]!.toNat) && decide (res[k]!.toNat ≤ OfNat.ofNat 122)) = (decide (OfNat.ofNat 65 ≤ (s[k]?.getD 'A').toNat) && decide ((s[k]?.getD 'A').toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ (s[k]?.getD 'A').toNat) && decide ((s[k]?.getD 'A').toNat ≤ OfNat.ofNat 122)))
    (if_pos : i < s.length)
    (if_neg : (OfNat.ofNat 65 ≤ (s[i]?.getD 'A').toNat → OfNat.ofNat 90 < (s[i]?.getD 'A').toNat) → OfNat.ofNat 97 ≤ (s[i]?.getD 'A').toNat ∧ (s[i]?.getD 'A').toNat ≤ OfNat.ofNat 122)
    (invariant_inner_res_size : res_1.size = s.length)
    (invariant_inner_i_lt : i < s.length)
    (invariant_inner_j_le : j_1 ≤ s.length)
    (invariant_inner_ci_letter : OfNat.ofNat 65 ≤ (s[i]?.getD 'A').toNat ∧ (s[i]?.getD 'A').toNat ≤ OfNat.ofNat 90 ∨ OfNat.ofNat 97 ≤ (s[i]?.getD 'A').toNat ∧ (s[i]?.getD 'A').toNat ≤ OfNat.ofNat 122)
    (invariant_inner_fixed_nonletters_prefix : ∀ k < i, (OfNat.ofNat 65 ≤ (s[k]?.getD 'A').toNat → OfNat.ofNat 90 < (s[k]?.getD 'A').toNat) → (OfNat.ofNat 97 ≤ (s[k]?.getD 'A').toNat → OfNat.ofNat 122 < (s[k]?.getD 'A').toNat) → res_1[k]! = s[k]?.getD 'A')
    (invariant_inner_mask_prefix : ∀ k < i, (decide (OfNat.ofNat 65 ≤ res_1[k]!.toNat) && decide (res_1[k]!.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ res_1[k]!.toNat) && decide (res_1[k]!.toNat ≤ OfNat.ofNat 122)) = (decide (OfNat.ofNat 65 ≤ (s[k]?.getD 'A').toNat) && decide ((s[k]?.getD 'A').toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ (s[k]?.getD 'A').toNat) && decide ((s[k]?.getD 'A').toNat ≤ OfNat.ofNat 122)))
    (if_neg_2 : (OfNat.ofNat 65 ≤ (s[j_1 - OfNat.ofNat 1]?.getD 'A').toNat → OfNat.ofNat 90 < (s[j_1 - OfNat.ofNat 1]?.getD 'A').toNat) ∧ (OfNat.ofNat 97 ≤ (s[j_1 - OfNat.ofNat 1]?.getD 'A').toNat → OfNat.ofNat 122 < (s[j_1 - OfNat.ofNat 1]?.getD 'A').toNat))
    (invariant_inner_letters_search : List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.take i res_1.toList) = (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.drop j_1 s)).reverse)
    (invariant_inner_count_search : (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.take i s)).length = (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.drop j_1 s)).length)
    (invariant_inner_done_found : True)
    : (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.take i s)).length = (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.drop (j_1 - OfNat.ofNat 1) s)).length := by
    sorry

theorem goal_7
    (s : List Char)
    (require_1 : True)
    (i_2 : ℕ)
    (res_1 : Array Char)
    (invariant_outer_n_eq_len : True)
    (invariant_outer_i_le : True)
    (invariant_outer_j_le : i_2 ≤ s.length)
    (invariant_outer_lettercount_account : (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) s).length = (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.drop i_2 s)).length)
    (invariant_outer_res_size : res_1.size = s.length)
    (invariant_outer_fixed_nonletters : ∀ k < s.length, (OfNat.ofNat 65 ≤ (s[k]?.getD 'A').toNat → OfNat.ofNat 90 < (s[k]?.getD 'A').toNat) → (OfNat.ofNat 97 ≤ (s[k]?.getD 'A').toNat → OfNat.ofNat 122 < (s[k]?.getD 'A').toNat) → res_1[k]! = s[k]?.getD 'A')
    (invariant_outer_mask_prefix : ∀ k < s.length, (decide (OfNat.ofNat 65 ≤ res_1[k]!.toNat) && decide (res_1[k]!.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ res_1[k]!.toNat) && decide (res_1[k]!.toNat ≤ OfNat.ofNat 122)) = (decide (OfNat.ofNat 65 ≤ (s[k]?.getD 'A').toNat) && decide ((s[k]?.getD 'A').toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ (s[k]?.getD 'A').toNat) && decide ((s[k]?.getD 'A').toNat ≤ OfNat.ofNat 122)))
    (invariant_outer_letters_account : List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.take s.length res_1.toList) = (List.filter (fun c => decide (OfNat.ofNat 65 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 90) || decide (OfNat.ofNat 97 ≤ c.toNat) && decide (c.toNat ≤ OfNat.ofNat 122)) (List.drop i_2 s)).reverse)
    : postcondition s res_1.toList := by
    sorry



prove_correct ReverseOnlyLetters by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at * <;> expose_names); try (conv => congr <;> simp) ; try rfl; try expose_names)
  exact (goal_0 s i j res invariant_outer_letters_account invariant_outer_res_size if_pos if_pos_1)
  exact (goal_1 s i j invariant_outer_lettercount_account if_pos if_pos_1)
  exact (goal_2 s i res_1 invariant_inner_i_lt invariant_inner_ci_letter invariant_inner_count_search)
  exact (goal_3 s i invariant_inner_i_lt invariant_inner_ci_letter invariant_inner_count_search)
  exact (goal_4 s i j j_1 res_1 if_neg_1 invariant_inner_res_size invariant_inner_i_lt invariant_inner_j_le invariant_inner_ci_letter if_pos_2 invariant_inner_letters_search invariant_inner_count_search)
  exact (goal_5 s require_1 i j res invariant_outer_letters_account invariant_outer_lettercount_account j_1 res_1 if_neg_1 invariant_outer_res_size invariant_outer_n_eq_len invariant_outer_i_le invariant_outer_j_le invariant_outer_fixed_nonletters invariant_outer_mask_prefix if_pos if_neg invariant_inner_res_size invariant_inner_i_lt invariant_inner_j_le invariant_inner_ci_letter invariant_inner_fixed_nonletters_prefix invariant_inner_mask_prefix if_neg_2 invariant_inner_letters_search invariant_inner_count_search invariant_inner_done_found)
  exact (goal_6 s require_1 i j res invariant_outer_letters_account invariant_outer_lettercount_account j_1 res_1 if_neg_1 invariant_outer_res_size invariant_outer_n_eq_len invariant_outer_i_le invariant_outer_j_le invariant_outer_fixed_nonletters invariant_outer_mask_prefix if_pos if_neg invariant_inner_res_size invariant_inner_i_lt invariant_inner_j_le invariant_inner_ci_letter invariant_inner_fixed_nonletters_prefix invariant_inner_mask_prefix if_neg_2 invariant_inner_letters_search invariant_inner_count_search invariant_inner_done_found)
  exact (goal_7 s require_1 i_2 res_1 invariant_outer_n_eq_len invariant_outer_i_le invariant_outer_j_le invariant_outer_lettercount_account invariant_outer_res_size invariant_outer_fixed_nonletters invariant_outer_mask_prefix invariant_outer_letters_account)
end Proof
