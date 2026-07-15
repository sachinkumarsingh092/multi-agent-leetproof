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
    387. First Unique Character in a String: return the index of the first non-repeating character.
    **Important: complexity should be O(n) time and O(1) space**
    Natural language breakdown:
    1. The input is a finite sequence of characters s indexed from 0.
    2. A character at index i is non-repeating (unique) if it occurs in s exactly once.
    3. If there exists at least one index i whose character is unique, the function returns the smallest such index.
    4. If no unique character exists, the function returns -1.
    5. All characters are ASCII, meaning each character code is < 128.
-/

section Specs
-- Count how many times a character occurs in the array.
-- Uses Array.countP (no List conversions).
def charCount (s : Array Char) (c : Char) : Nat :=
  s.countP (fun x => x = c)

-- A simple ASCII predicate (as required by constraints).
def isASCII (c : Char) : Prop := c.toNat < 128

-- Input constraint: all characters are ASCII.
def precondition (s : Array Char) : Prop :=
  ∀ (i : Nat), i < s.size → isASCII (s[i]!)

def postcondition (s : Array Char) (result : Int) : Prop :=
  -- If there is a unique character, result is the smallest index with count = 1.
  ((∃ (i : Nat), i < s.size ∧ charCount s (s[i]!) = 1) →
      0 ≤ result ∧
      (result.toNat < s.size) ∧
      charCount s (s[result.toNat]!) = 1 ∧
      (∀ (j : Nat), j < result.toNat → charCount s (s[j]!) ≠ 1))
  ∧
  -- If there is no unique character, result is -1.
  ((¬ (∃ (i : Nat), i < s.size ∧ charCount s (s[i]!) = 1)) →
      result = (-1) ∧
      (∀ (i : Nat), i < s.size → charCount s (s[i]!) ≠ 1))
end Specs

section Impl
method FirstUniqueCharIndex (s : Array Char)
  return (result : Int)
  require precondition s
  ensures postcondition s result
  do
  -- Build frequency array of size 128 (all ASCII chars)
  let mut freq : Array Nat := Array.replicate 128 0
  -- First pass: count occurrences of each character
  let mut i : Nat := 0
  while i < s.size
    -- Invariant: freq array maintains size 128
    -- Init: Array.replicate 128 0 has size 128. Pres: set! preserves size. Suff: needed for indexing.
    invariant "freq_size" freq.size = 128
    -- Invariant: loop counter in bounds
    -- Init: i=0. Pres: i increments up to s.size. Suff: needed for termination and extraction.
    invariant "i_bounds" i ≤ s.size
    -- Invariant: freq[code] counts occurrences of that code in s[0..i]
    -- Init: freq all zeros, extract s 0 0 is empty so countP is 0. Pres: adding 1 when char matches.
    -- Suff: after loop (i = s.size), freq holds full counts.
    invariant "freq_counts" ∀ (code : Nat), code < 128 →
      freq[code]! = (Array.extract s 0 i).countP (fun x => x.toNat = code)
    -- Decreasing: distance to array size
    decreasing s.size - i
  do
    let c := s[i]!
    let code := c.toNat
    if code < 128 then
      freq := freq.set! code (freq[code]! + 1)
    i := i + 1
  -- Second pass: find first character with count = 1
  let mut j : Nat := 0
  let mut ans : Int := -1
  let mut found : Bool := false
  while j < s.size ∧ !found
    -- Invariant: freq array still has size 128
    invariant "freq_size2" freq.size = 128
    -- Invariant: j is in bounds
    -- Init: j=0. Pres: j increments or stays (when found). Suff: needed for postcondition indexing.
    invariant "j_bounds" j ≤ s.size
    -- Invariant: freq still holds full character counts (freq not modified in this loop)
    -- Init: established by first loop (extract s 0 s.size = s). Pres: freq unchanged. Suff: links freq lookups to charCount.
    invariant "freq_is_charcount" ∀ (code : Nat), code < 128 →
      freq[code]! = s.countP (fun x => x.toNat = code)
    -- Invariant: if not found, ans is still -1
    -- Init: ans=-1, found=false. Pres: ans only changes when found becomes true.
    invariant "found_false_ans" (found = false → ans = -1)
    -- Invariant: if not found, all indices before j have non-unique characters
    -- Init: vacuously true (j=0). Pres: we only advance j when current char isn't unique.
    -- Suff: at exit with found=false, all indices checked → no unique char exists.
    invariant "found_false_prev" (found = false → ∀ (k : Nat), k < j → charCount s (s[k]!) ≠ 1)
    -- Invariant: if found, ans = j and s[j] is unique
    -- Init: found=false so vacuously true. Pres: set when freq[code]=1.
    -- Suff: at exit with found=true, ans is the correct index.
    invariant "found_true_ans" (found = true → ans = (j : Int) ∧ j < s.size ∧ charCount s (s[j]!) = 1)
    -- Invariant: if found, all prior indices have non-unique characters
    -- Init: vacuously true. Pres: carried from found_false_prev at moment of finding.
    -- Suff: ensures ans is the *first* unique character index.
    invariant "found_true_prev" (found = true → ∀ (k : Nat), k < j → charCount s (s[k]!) ≠ 1)
    -- Decreasing: encode lexicographic (found-flag, s.size-j) as single Nat.
    -- When found becomes true: value drops from (s.size-j+1 > 0) to 0.
    -- When found stays false and j increments: s.size-j+1 decreases by 1.
    decreasing if !found then s.size - j + 1 else 0
  do
    let c := s[j]!
    let code := c.toNat
    if code < 128 then
      if freq[code]! = 1 then
        ans := (j : Int)
        found := true
    if !found then
      j := j + 1
  return ans
end Impl

section TestCases
-- Test case 1: Example 1
-- Input: "leetcode" -> output 0
-- ('l' occurs once and is the first such character)
def test1_s : Array Char := #['l','e','e','t','c','o','d','e']
def test1_Expected : Int := 0

-- Test case 2: Example 2
-- Input: "loveleetcode" -> output 2
-- (first unique is 'v' at index 2)
def test2_s : Array Char := #['l','o','v','e','l','e','e','t','c','o','d','e']
def test2_Expected : Int := 2

-- Test case 3: Example 3
-- Input: "aabb" -> output -1
-- (no unique character)
def test3_s : Array Char := #['a','a','b','b']
def test3_Expected : Int := (-1)

-- Test case 4: Empty input (degenerate)
-- No characters => no unique => -1
def test4_s : Array Char := #[]
def test4_Expected : Int := (-1)

-- Test case 5: Singleton input (boundary)
-- Only character is unique => index 0
def test5_s : Array Char := #['z']
def test5_Expected : Int := 0

-- Test case 6: Unique appears after repeats
-- "aabc" => 'b' at index 2 is the first unique
def test6_s : Array Char := #['a','a','b','c']
def test6_Expected : Int := 2

-- Test case 7: All same characters
-- "aaaa" => -1
def test7_s : Array Char := #['a','a','a','a']
def test7_Expected : Int := (-1)

-- Test case 8: Includes ASCII control char and repeats
-- [NUL, 'a', 'a'] => NUL is unique at index 0
-- NUL is ASCII (code 0)
def test8_s : Array Char := #[('\u0000'), 'a', 'a']
def test8_Expected : Int := 0

-- Test case 9: Multiple uniques; must pick the smallest index
-- "abac" => 'b' at 1 and 'c' at 3 are unique, so answer is 1
def test9_s : Array Char := #['a','b','a','c']
def test9_Expected : Int := 1
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((FirstUniqueCharIndex test1_s).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((FirstUniqueCharIndex test2_s).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((FirstUniqueCharIndex test3_s).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((FirstUniqueCharIndex test4_s).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((FirstUniqueCharIndex test5_s).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((FirstUniqueCharIndex test6_s).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((FirstUniqueCharIndex test7_s).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((FirstUniqueCharIndex test8_s).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((FirstUniqueCharIndex test9_s).run), DivM.res test9_Expected ]
end Assertions

section Pbt
velvet_plausible_test FirstUniqueCharIndex (config := { maxMs := some 20000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000

theorem goal_0
    (s : Array Char)
    (freq : Array ℕ)
    (i : ℕ)
    (invariant_freq_size : freq.size = OfNat.ofNat 128)
    (invariant_freq_counts : ∀ code < OfNat.ofNat 128, freq[code]! = Array.countP (fun x => decide (x.toNat = code)) (s.extract (OfNat.ofNat 0) i))
    (if_pos : i < s.size)
    (if_pos_1 : s[i]!.toNat < OfNat.ofNat 128)
    : ∀ code < OfNat.ofNat 128, (freq.setIfInBounds s[i]!.toNat (freq[s[i]!.toNat]! + OfNat.ofNat 1))[code]! = Array.countP (fun x => decide (x.toNat = code)) (s.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) := by
    intro code hcode
    -- Step 1: Rewrite extract (i+1) as extract i pushed with s[i]
    have h_extract : s.extract 0 (i + 1) = (s.extract 0 i).push s[i]! := by
      rw [Array.extract_succ_right (by omega) if_pos]
      congr 1
      simp [Array.getElem!_eq_getD, Array.getD_getElem?, if_pos]
    -- Step 2: countP over push = countP + if match then 1 else 0
    have h_countP : Array.countP (fun x => decide (x.toNat = code)) (s.extract 0 (i + 1)) = Array.countP (fun x => decide (x.toNat = code)) (s.extract 0 i) + if decide (s[i]!.toNat = code) then 1 else 0 := by
      rw [h_extract, Array.push_eq_append_singleton, Array.countP_append, Array.countP_singleton]
    -- Step 3: The LHS getElem! of setIfInBounds
    have hcode' : code < freq.size := by omega
    have hsi_lt : s[i]!.toNat < freq.size := by omega
    have h_lhs : (freq.setIfInBounds s[i]!.toNat (freq[s[i]!.toNat]! + 1))[code]! = if s[i]!.toNat = code then freq[s[i]!.toNat]! + 1 else freq[code]! := by
      simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
      split_ifs with h1 h2
      · simp
      · exfalso; exact h2 (by simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?] at hsi_lt; exact hsi_lt)
      · rfl
    -- Now combine
    rw [h_lhs, h_countP, invariant_freq_counts code hcode]
    split <;> simp_all

theorem goal_1
    (s : Array Char)
    (i_1 : Array ℕ)
    (j : ℕ)
    (invariant_freq_is_charcount : ∀ code < OfNat.ofNat 128, i_1[code]! = Array.countP (fun x => decide (x.toNat = code)) s)
    (a : j < s.size)
    (if_pos : s[j]!.toNat < OfNat.ofNat 128)
    (if_pos_1 : i_1[s[j]!.toNat]! = OfNat.ofNat 1)
    : j < s.size ∧ Array.countP (fun x => decide (x = s[j]!)) s = OfNat.ofNat 1 := by
    constructor
    · exact a
    · have h1 := invariant_freq_is_charcount (s[j]!.toNat) if_pos
      rw [if_pos_1] at h1
      have h2 : Array.countP (fun x => decide (x = s[j]!)) s = Array.countP (fun x => decide (x.toNat = s[j]!.toNat)) s := by
        apply Array.countP_congr
        intro x _
        constructor
        · intro hx
          have := decide_eq_true_eq.mp hx
          exact decide_eq_true_eq.mpr (congrArg Char.toNat this)
        · intro hx
          have hxeq := decide_eq_true_eq.mp hx
          apply decide_eq_true_eq.mpr
          have h3 : Char.ofNat x.toNat = Char.ofNat (s[j]!).toNat := by rw [hxeq]
          rw [Char.ofNat_toNat, Char.ofNat_toNat] at h3
          exact h3
      rw [h2]
      omega

theorem goal_2
    (s : Array Char)
    (i_1 : Array ℕ)
    (found : Bool)
    (j : ℕ)
    (invariant_freq_is_charcount : ∀ code < OfNat.ofNat 128, i_1[code]! = Array.countP (fun x => decide (x.toNat = code)) s)
    (invariant_found_false_prev : found = false → ∀ k < j, ¬Array.countP (fun x => decide (x = s[k]!)) s = OfNat.ofNat 1)
    (a : j < s.size)
    (if_pos : s[j]!.toNat < OfNat.ofNat 128)
    (if_neg : ¬i_1[s[j]!.toNat]! = OfNat.ofNat 1)
    : found = false → ∀ k < j + OfNat.ofNat 1, ¬Array.countP (fun x => decide (x = s[k]!)) s = OfNat.ofNat 1 := by
    intro hf k hk
    rw [Nat.lt_succ_iff_lt_or_eq] at hk
    cases hk with
    | inl hlt => exact invariant_found_false_prev hf k hlt
    | inr heq =>
      rw [heq]
      have h_freq := invariant_freq_is_charcount (s[j]!.toNat) if_pos
      have h_ne : ¬Array.countP (fun x => decide (x.toNat = s[j]!.toNat)) s = OfNat.ofNat 1 := by
        rw [← h_freq]; exact if_neg
      have h_congr : Array.countP (fun x => decide (x = s[j]!)) s = Array.countP (fun x => decide (x.toNat = s[j]!.toNat)) s := by
        apply Array.countP_congr
        intro x _
        simp only [decide_eq_true_iff]
        constructor
        · intro h; rw [h]
        · intro h
          have := Char.ofNat_toNat x
          have := Char.ofNat_toNat (s[j]!)
          rw [h] at *
          simp_all
      rw [h_congr]
      exact h_ne

theorem goal_3
    (s : Array Char)
    (i_1 : Array ℕ)
    (i_2 : ℕ)
    (invariant_i_bounds : i_2 ≤ s.size)
    (invariant_freq_counts : ∀ code < OfNat.ofNat 128, i_1[code]! = Array.countP (fun x => decide (x.toNat = code)) (s.extract (OfNat.ofNat 0) i_2))
    (done_1 : s.size ≤ i_2)
    : ∀ code < OfNat.ofNat 128, i_1[code]! = Array.countP (fun x => decide (x.toNat = code)) s := by
    have h_eq : i_2 = s.size := Nat.le_antisymm invariant_i_bounds done_1
    subst h_eq
    simp [Array.extract_size] at invariant_freq_counts
    exact invariant_freq_counts

theorem goal_4
    (s : Array Char)
    (i_2 : ℕ)
    (i_4 : ℤ)
    (i_5 : Bool)
    (j_1 : ℕ)
    (invariant_i_bounds : i_2 ≤ s.size)
    (invariant_found_false_ans : i_5 = false → i_4 = -OfNat.ofNat 1)
    (invariant_j_bounds : j_1 ≤ s.size)
    (invariant_found_false_prev : i_5 = false → ∀ k < j_1, ¬Array.countP (fun x => decide (x = s[k]!)) s = OfNat.ofNat 1)
    (invariant_found_true_prev : i_5 = true → ∀ k < j_1, ¬Array.countP (fun x => decide (x = s[k]!)) s = OfNat.ofNat 1)
    (invariant_found_true_ans : i_5 = true → i_4 = j_1.cast ∧ j_1 < s.size ∧ Array.countP (fun x => decide (x = s[j_1]!)) s = OfNat.ofNat 1)
    (done_1 : s.size ≤ i_2)
    (done_2 : j_1 < s.size → i_5 = true)
    : postcondition s i_4 := by
    unfold postcondition charCount
    have h_not_lt : ¬(j_1 < s.size) → j_1 = s.size := by omega
    constructor
    · -- Part 1: existence of unique char → result is smallest index
      intro ⟨i, hi_lt, hi_count⟩
      cases h_found : i_5 with
      | false =>
        exfalso
        have h_j_eq : j_1 = s.size := h_not_lt (fun h => by simp [done_2 h] at h_found)
        have h_prev := invariant_found_false_prev h_found
        exact h_prev i (h_j_eq ▸ hi_lt) hi_count
      | true =>
        obtain ⟨h_ans, h_j_lt, h_j_count⟩ := invariant_found_true_ans h_found
        have h_prev := invariant_found_true_prev h_found
        rw [h_ans]
        refine ⟨Int.ofNat_nonneg j_1, ?_, ?_, ?_⟩
        · simp [Int.toNat_natCast]; exact h_j_lt
        · simp [Int.toNat_natCast]; exact h_j_count
        · intro j hj
          simp [Int.toNat_natCast] at hj
          exact h_prev j hj
    · -- Part 2: no unique char → result = -1
      intro h_no_unique
      cases h_found : i_5 with
      | false =>
        exact ⟨invariant_found_false_ans h_found, fun i hi habs => h_no_unique ⟨i, hi, habs⟩⟩
      | true =>
        exfalso
        obtain ⟨h_ans, h_j_lt, h_j_count⟩ := invariant_found_true_ans h_found
        exact h_no_unique ⟨j_1, h_j_lt, h_j_count⟩


prove_correct FirstUniqueCharIndex by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at *); try (conv => congr <;> simp) ; try expose_names)
  exact (goal_0 s freq i invariant_freq_size invariant_freq_counts if_pos if_pos_1)
  exact (goal_1 s i_1 j invariant_freq_is_charcount a if_pos if_pos_1)
  exact (goal_2 s i_1 found j invariant_freq_is_charcount invariant_found_false_prev a if_pos if_neg)
  exact (goal_3 s i_1 i_2 invariant_i_bounds invariant_freq_counts done_1)
  exact (goal_4 s i_2 i_4 i_5 j_1 invariant_i_bounds invariant_found_false_ans invariant_j_bounds invariant_found_false_prev invariant_found_true_prev invariant_found_true_ans done_1 done_2)
end Proof
