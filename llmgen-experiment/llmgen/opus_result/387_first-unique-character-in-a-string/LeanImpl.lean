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
    387. First Unique Character in a String: return the index of the first non-repeating character.
    **Important: complexity should be O(n) time and O(1) space**
    Natural language breakdown:
    1. The input is a finite sequence of characters s indexed from 0.
    2. A character at index i is non-repeating (unique) if it occurs in s exactly once.
    3. If there exists at least one index i whose character is unique, the function returns the smallest such index.
    4. If no unique character exists, the function returns -1.
    5. All characters are ASCII, meaning each character code is < 128.
-/

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
def implementation (s : Array Char) : Int :=
  -- Build frequency table: Array of 128 Nats, one per ASCII code
  let counts := s.foldl (fun (acc : Array Nat) (c : Char) =>
    let idx := c.toNat
    if idx < acc.size then
      acc.set! idx (acc[idx]! + 1)
    else
      acc
  ) (mkArray 128 0)
  -- Find the first character with count = 1
  let result := s.foldl (fun (acc : Int × Nat) (c : Char) =>
    let (bestIdx, curIdx) := acc
    let code := c.toNat
    if bestIdx = -1 then
      if code < counts.size then
        if counts[code]! = 1 then ((curIdx : Int), curIdx + 1) else (-1, curIdx + 1)
      else
        (-1, curIdx + 1)
    else
      (bestIdx, curIdx + 1)
  ) ((-1 : Int), (0 : Nat))
  result.1
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
method implementationPbt (s : Array Char)
  return (result : Int)
  require precondition s
  ensures postcondition s result
  do
  return (implementation s)

velvet_plausible_test implementationPbt (config := { maxMs := some 20000 })
end Pbt

section Proof
theorem correctness_goal_0
    (s : Array Char)
    (counts : Array ℕ)
    (hcounts_def : counts =
  Array.foldl
    (fun acc c =>
      let idx := c.toNat;
      if idx < acc.size then acc.set! idx (acc[idx]! + 1) else acc)
    (mkArray 128 0) s)
    (result : ℤ × ℕ)
    (hresult_def : result =
  Array.foldl
    (fun acc c =>
      let bestIdx := acc.1;
      let curIdx := acc.2;
      let code := c.toNat;
      if bestIdx = -1 then
        if code < counts.size then if counts[code]! = 1 then (↑curIdx, curIdx + 1) else (-1, curIdx + 1)
        else (-1, curIdx + 1)
      else (bestIdx, curIdx + 1))
    (-1, 0) s)
    : counts.size = 128 := by
    subst hcounts_def
    let f := (fun (acc : Array Nat) (c : Char) =>
      let idx := c.toNat;
      if idx < acc.size then acc.set! idx (acc[idx]! + 1) else acc)
    show (Array.foldl f (mkArray 128 0) s).size = 128
    apply Array.foldl_induction (motive := fun _ (acc : Array Nat) => acc.size = 128)
    · native_decide
    · intro i acc hacc
      simp only [f]
      split
      · rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
        exact hacc
      · exact hacc

theorem size_mkArray_128 : (mkArray 128 (0:ℕ)).size = 128 := by native_decide

theorem mkArray_getElem!_zero (n : ℕ) (i : ℕ) (h : i < n) : (mkArray n (0:ℕ))[i]! = 0 := by
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
  have hsz : (mkArray n (0:ℕ)).size = n := by
    unfold mkArray
    simp [List.length_replicate]
  have hi : i < (mkArray n (0:ℕ)).size := by omega
  rw [show (mkArray n (0:ℕ))[i]? = some ((mkArray n (0:ℕ))[i]'hi) from Array.getElem?_eq_getElem hi]
  simp only [Option.getD_some]
  exact Array.getElem_mkArray hi

theorem countP_extract_zero_zero (s : Array Char) (p : Char → Bool) :
    Array.countP p (s.extract 0 0) = 0 := by
  simp [Array.countP_eq_zero]

theorem countP_extract_succ (s : Array Char) (p : Char → Bool) (k : ℕ) (hk : k < s.size) :
    Array.countP p (s.extract 0 (k + 1)) = Array.countP p (s.extract 0 k) + if p s[k] then 1 else 0 := by
  have h0 : min 0 k = 0 := Nat.min_eq_left (Nat.zero_le k)
  have h1 : (s.extract 0 k).push s[k] = s.extract 0 (k + 1) := by
    have h := @Array.push_extract_getElem _ s 0 k hk
    rw [h0] at h
    exact h
  rw [← h1, Array.countP_push]


theorem correctness_goal_1_0
    (s : Array Char)
    (h_precond : precondition s)
    (result : ℤ × ℕ)
    (c : Char)
    (hc : c.toNat < 128)
    (hresult_def : result =
  Array.foldl
    (fun acc c =>
      let bestIdx := acc.1;
      let curIdx := acc.2;
      let code := c.toNat;
      if bestIdx = -1 then
        if
            code <
              (Array.foldl
                  (fun acc c =>
                    let idx := c.toNat;
                    if idx < acc.size then acc.set! idx (acc[idx]! + 1) else acc)
                  (mkArray 128 0) s).size then
          if
              (Array.foldl
                    (fun acc c =>
                      let idx := c.toNat;
                      if idx < acc.size then acc.set! idx (acc[idx]! + 1) else acc)
                    (mkArray 128 0) s)[code]! =
                1 then
            (↑curIdx, curIdx + 1)
          else (-1, curIdx + 1)
        else (-1, curIdx + 1)
      else (bestIdx, curIdx + 1))
    (-1, 0) s)
    (h_counts_size : (Array.foldl
      (fun acc c =>
        let idx := c.toNat;
        if idx < acc.size then acc.set! idx (acc[idx]! + 1) else acc)
      (mkArray 128 0) s).size =
  128)
    (f : Array ℕ → Char → Array ℕ)
    (hf_def : f = fun acc ch =>
  let idx := ch.toNat;
  if idx < acc.size then acc.set! idx (acc[idx]! + 1) else acc)
    : ∀ (ch : Char), ch.toNat < 128 → (Array.foldl f (mkArray 128 0) s)[ch.toNat]! = Array.countP (fun x => decide (x = ch)) s := by
    sorry


theorem correctness_goal_1
    (s : Array Char)
    (h_precond : precondition s)
    (counts : Array ℕ)
    (hcounts_def : counts =
  Array.foldl
    (fun acc c =>
      let idx := c.toNat;
      if idx < acc.size then acc.set! idx (acc[idx]! + 1) else acc)
    (mkArray 128 0) s)
    (result : ℤ × ℕ)
    (hresult_def : result =
  Array.foldl
    (fun acc c =>
      let bestIdx := acc.1;
      let curIdx := acc.2;
      let code := c.toNat;
      if bestIdx = -1 then
        if code < counts.size then if counts[code]! = 1 then (↑curIdx, curIdx + 1) else (-1, curIdx + 1)
        else (-1, curIdx + 1)
      else (bestIdx, curIdx + 1))
    (-1, 0) s)
    (h_counts_size : counts.size = 128)
    : ∀ (c : Char), c.toNat < 128 → counts[c.toNat]! = charCount s c := by
    intro c hc
    subst hcounts_def
    set f := (fun (acc : Array ℕ) (ch : Char) =>
      let idx := ch.toNat;
      if idx < acc.size then acc.set! idx (acc[idx]! + 1) else acc) with hf_def
    have hmain : ∀ (ch : Char), ch.toNat < 128 →
        (Array.foldl f (mkArray 128 0) s)[ch.toNat]! = s.countP (fun x => x = ch) := by
      expose_names; exact (correctness_goal_1_0 s h_precond result c hc hresult_def h_counts_size f hf_def)
    have hresult := hmain c hc
    simp only [charCount]
    exact hresult

theorem correctness_goal_2_0
    (s : Array Char)
    (h_precond : precondition s)
    (counts : Array ℕ)
    (result : ℤ × ℕ)
    (h_counts_size : counts.size = 128)
    (h_counts_correct : ∀ (c : Char), c.toNat < 128 → counts[c.toNat]! = charCount s c)
    (f : ℤ × ℕ → Char → ℤ × ℕ)
    (hf_def : f = fun acc c =>
  let bestIdx := acc.1;
  let curIdx := acc.2;
  let code := c.toNat;
  if bestIdx = -1 then
    if code < counts.size then if counts[code]! = 1 then (↑curIdx, curIdx + 1) else (-1, curIdx + 1)
    else (-1, curIdx + 1)
  else (bestIdx, curIdx + 1))
    (hresult_eq : result = Array.foldl f (-1, 0) s)
    : (fun k acc =>
    acc.2 = k ∧
      ((acc.1 = -1 ∧ ∀ j < k, j < s.size → charCount s s[j]! ≠ 1) ∨
        0 ≤ acc.1 ∧
          acc.1.toNat < k ∧
            acc.1.toNat < s.size ∧ charCount s s[acc.1.toNat]! = 1 ∧ ∀ j < acc.1.toNat, charCount s s[j]! ≠ 1))
  s.size (Array.foldl f (-1, 0) s) := by
  let motive := fun (k : Nat) (acc : ℤ × ℕ) =>
    acc.2 = k ∧
      ((acc.1 = -1 ∧ ∀ j < k, j < s.size → charCount s s[j]! ≠ 1) ∨
        0 ≤ acc.1 ∧
          acc.1.toNat < k ∧
            acc.1.toNat < s.size ∧ charCount s s[acc.1.toNat]! = 1 ∧ ∀ j < acc.1.toNat, charCount s s[j]! ≠ 1)
  apply Array.foldl_induction (motive := motive)
  · exact ⟨rfl, Or.inl ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩⟩
  · intro ⟨i, hi⟩ b hb
    simp only [motive] at hb ⊢
    subst hf_def
    obtain ⟨hb2, hb_disj⟩ := hb
    have h_ascii : s[i]!.toNat < 128 := by
      have := h_precond i hi; unfold isASCII at this; exact this
    have h_getElem_eq : s[i]'hi = s[i]! := by rw [getElem!_pos s i hi]
    simp only []
    split
    · rename_i h_eq  -- b.1 = -1
      have h_code_lt : (s[i]'hi).toNat < counts.size := by rw [h_getElem_eq]; omega
      split
      · rename_i h_lt  -- code < counts.size
        have h_count_eq : counts[(s[i]'hi).toNat]! = charCount s s[i]! := by
          rw [h_getElem_eq]; exact h_counts_correct s[i]! h_ascii
        split
        · rename_i h_one  -- counts[code]! = 1
          -- result is (↑b.2, b.2 + 1)
          refine ⟨by omega, Or.inr ?_⟩
          have hb2_eq : (↑b.2 : ℤ).toNat = b.2 := Int.toNat_natCast b.2
          refine ⟨Int.natCast_nonneg b.2, ?_, ?_, ?_, ?_⟩
          · rw [hb2_eq]; omega
          · rw [hb2_eq]; omega
          · rw [hb2_eq, hb2]
            rw [← h_count_eq]; exact h_one
          · intro j hj
            rw [hb2_eq] at hj
            cases hb_disj with
            | inl h_neg => exact h_neg.2 j (by omega) (by omega)
            | inr h_pos => omega
        · rename_i h_not_one  -- counts[code]! ≠ 1
          -- result is (-1, b.2 + 1)
          refine ⟨by omega, Or.inl ⟨by trivial, ?_⟩⟩
          intro j hj hj_size
          by_cases hjk : j < i
          · cases hb_disj with
            | inl h_neg => exact h_neg.2 j hjk hj_size
            | inr h_pos => omega
          · have hji : j = i := by omega
            subst hji; rw [← h_count_eq]; exact h_not_one
      · rename_i h_not_lt  -- code ≥ counts.size
        exfalso; exact h_not_lt h_code_lt
    · rename_i h_ne  -- b.1 ≠ -1
      refine ⟨by omega, Or.inr ?_⟩
      cases hb_disj with
      | inl h_neg => exact absurd h_neg.1 h_ne
      | inr h_pos =>
        exact ⟨h_pos.1, by omega, h_pos.2.2.1, h_pos.2.2.2.1, h_pos.2.2.2.2⟩

theorem correctness_goal_2
    (s : Array Char)
    (h_precond : precondition s)
    (counts : Array ℕ)
    (result : ℤ × ℕ)
    (hresult_def : result =
  Array.foldl
    (fun acc c =>
      let bestIdx := acc.1;
      let curIdx := acc.2;
      let code := c.toNat;
      if bestIdx = -1 then
        if code < counts.size then if counts[code]! = 1 then (↑curIdx, curIdx + 1) else (-1, curIdx + 1)
        else (-1, curIdx + 1)
      else (bestIdx, curIdx + 1))
    (-1, 0) s)
    (h_counts_size : counts.size = 128)
    (h_counts_correct : ∀ (c : Char), c.toNat < 128 → counts[c.toNat]! = charCount s c)
    : (∃ i < s.size, charCount s s[i]! = 1) →
  0 ≤ result.1 ∧
    result.1.toNat < s.size ∧ charCount s s[result.1.toNat]! = 1 ∧ ∀ j < result.1.toNat, charCount s s[j]! ≠ 1 := by
    -- Define the fold function
    set f := (fun (acc : ℤ × ℕ) (c : Char) =>
      let bestIdx := acc.1;
      let curIdx := acc.2;
      let code := c.toNat;
      if bestIdx = -1 then
        if code < counts.size then if counts[code]! = 1 then (↑curIdx, curIdx + 1) else (-1, curIdx + 1)
        else (-1, curIdx + 1)
      else (bestIdx, curIdx + 1)) with hf_def
    -- Define the motive (loop invariant)
    have hresult_eq : result = Array.foldl f (-1, 0) s := by rw [hresult_def]
    -- The key invariant: after processing k elements, the accumulator satisfies the invariant
    have h_invariant : (fun (k : ℕ) (acc : ℤ × ℕ) =>
      acc.2 = k ∧
      ((acc.1 = -1 ∧ ∀ j, j < k → j < s.size → charCount s s[j]! ≠ 1) ∨
       (0 ≤ acc.1 ∧ acc.1.toNat < k ∧ acc.1.toNat < s.size ∧ charCount s s[acc.1.toNat]! = 1 ∧ ∀ j, j < acc.1.toNat → charCount s s[j]! ≠ 1)))
      s.size (s.foldl f (-1, 0)) := by expose_names; exact (correctness_goal_2_0 s h_precond counts result h_counts_size h_counts_correct f hf_def hresult_eq)
    -- Now use the invariant to prove the goal
    intro ⟨i, hi_lt, hi_unique⟩
    obtain ⟨h_snd, h_cases⟩ := h_invariant
    rw [hresult_eq]
    cases h_cases with
    | inl h_neg =>
      -- If result.1 = -1 after full fold, then all chars are non-unique, contradiction
      exfalso
      exact h_neg.2 i hi_lt hi_lt hi_unique
    | inr h_found =>
      exact ⟨h_found.1, h_found.2.2.1, h_found.2.2.2.1, fun j hj => h_found.2.2.2.2 j hj⟩

theorem correctness_goal_3
    (s : Array Char)
    (h_precond : precondition s)
    (counts : Array ℕ)
    (result : ℤ × ℕ)
    (hresult_def : result =
  Array.foldl
    (fun acc c =>
      let bestIdx := acc.1;
      let curIdx := acc.2;
      let code := c.toNat;
      if bestIdx = -1 then
        if code < counts.size then if counts[code]! = 1 then (↑curIdx, curIdx + 1) else (-1, curIdx + 1)
        else (-1, curIdx + 1)
      else (bestIdx, curIdx + 1))
    (-1, 0) s)
    (h_counts_size : counts.size = 128)
    (h_counts_correct : ∀ (c : Char), c.toNat < 128 → counts[c.toNat]! = charCount s c)
    : (¬∃ i < s.size, charCount s s[i]! = 1) → result.1 = -1 ∧ ∀ i < s.size, charCount s s[i]! ≠ 1 := by
    intro hno
    let f := fun (acc : ℤ × ℕ) (c : Char) =>
      let bestIdx := acc.1
      let curIdx := acc.2
      let code := c.toNat
      if bestIdx = -1 then
        if code < counts.size then if counts[code]! = 1 then (↑curIdx, curIdx + 1) else (-1, curIdx + 1)
        else (-1, curIdx + 1)
      else (bestIdx, curIdx + 1)
    have hf_def : f = fun acc c =>
      let bestIdx := acc.1;
      let curIdx := acc.2;
      let code := c.toNat;
      if bestIdx = -1 then
        if code < counts.size then if counts[code]! = 1 then (↑curIdx, curIdx + 1) else (-1, curIdx + 1)
        else (-1, curIdx + 1)
      else (bestIdx, curIdx + 1) := rfl
    have hresult_eq : result = Array.foldl f (-1, 0) s := hresult_def
    have inv := correctness_goal_2_0 s h_precond counts result h_counts_size h_counts_correct f hf_def hresult_eq
    simp only at inv
    rw [← hresult_eq] at inv
    obtain ⟨_, h_cases⟩ := inv
    cases h_cases with
    | inl h_neg =>
      exact ⟨h_neg.1, fun i hi => h_neg.2 i hi hi⟩
    | inr h_pos =>
      exfalso
      apply hno
      exact ⟨result.1.toNat, h_pos.2.2.1, h_pos.2.2.2.1⟩


theorem correctness_goal
    (s : Array Char)
    (h_precond : precondition s)
    : postcondition s (implementation s) := by
    unfold postcondition implementation
    -- Define the counts array
    set counts := s.foldl (fun (acc : Array Nat) (c : Char) =>
      let idx := c.toNat
      if idx < acc.size then
        acc.set! idx (acc[idx]! + 1)
      else
        acc
    ) (mkArray 128 0) with hcounts_def
    -- Define the result
    set result := s.foldl (fun (acc : Int × Nat) (c : Char) =>
      let bestIdx := acc.1
      let curIdx := acc.2
      let code := c.toNat
      if bestIdx = -1 then
        if code < counts.size then
          if counts[code]! = 1 then ((curIdx : Int), curIdx + 1) else (-1, curIdx + 1)
        else
          (-1, curIdx + 1)
      else
        (bestIdx, curIdx + 1)
    ) ((-1 : Int), (0 : Nat)) with hresult_def
    -- Key lemma 1: counts array has size 128
    have h_counts_size : counts.size = 128 := by expose_names; exact (correctness_goal_0 s counts hcounts_def result hresult_def)
    -- Key lemma 2: counts correctly tracks character frequencies
    have h_counts_correct : ∀ (c : Char), c.toNat < 128 → counts[c.toNat]! = charCount s c := by expose_names; exact (correctness_goal_1 s h_precond counts hcounts_def result hresult_def h_counts_size)
    -- Key lemma 3: the scan result satisfies the postcondition
    have h_scan_pos : (∃ i, i < s.size ∧ charCount s (s[i]!) = 1) →
      0 ≤ result.1 ∧ result.1.toNat < s.size ∧ charCount s (s[result.1.toNat]!) = 1 ∧
      (∀ j, j < result.1.toNat → charCount s (s[j]!) ≠ 1) := by expose_names; exact (correctness_goal_2 s h_precond counts result hresult_def h_counts_size h_counts_correct)
    have h_scan_neg : (¬∃ i, i < s.size ∧ charCount s (s[i]!) = 1) →
      result.1 = -1 ∧ (∀ i, i < s.size → charCount s (s[i]!) ≠ 1) := by expose_names; exact (correctness_goal_3 s h_precond counts result hresult_def h_counts_size h_counts_correct)
    exact ⟨h_scan_pos, h_scan_neg⟩
end Proof
