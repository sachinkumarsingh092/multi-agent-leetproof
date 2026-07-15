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
    383. Ransom Note: decide whether one note can be constructed from the letters of a magazine.
    **Important: complexity should be O(m + n) time and O(1) space**
    Natural language breakdown:
    1. Inputs are two sequences of characters: ransomNote and magazine.
    2. A character from magazine can be used at most once when constructing the ransomNote.
    3. Construction is possible exactly when every character occurs in magazine at least as many times as it occurs in ransomNote.
    4. The function returns true iff construction is possible; otherwise it returns false.
    5. The empty ransom note is always constructible from any magazine.
    6. Characters (Char) may be arbitrary Unicode characters, not limited to lowercase English letters.
-/

-- Helper: multiset-style availability condition via per-character counts.
-- Mathlib provides `List.count` for decidable equality types.
def canConstructProp (ransomNote : List Char) (magazine : List Char) : Prop :=
  ∀ c : Char, ransomNote.count c ≤ magazine.count c

def precondition (ransomNote : List Char) (magazine : List Char) : Prop :=
  True

def postcondition (ransomNote : List Char) (magazine : List Char) (result : Bool) : Prop :=
  (result = true ↔ canConstructProp ransomNote magazine)
end Specs

section Impl
def implementation (ransomNote : List Char) (magazine : List Char) : Bool :=
  -- Build frequency map from magazine
  let magCounts := magazine.foldl (fun (m : Std.HashMap Char Nat) c =>
    m.insert c (m.getD c 0 + 1)) Std.HashMap.empty
  -- Decrement counts for each ransom note character; if any goes below zero, fail
  let result := ransomNote.foldl (fun (state : Bool × Std.HashMap Char Nat) c =>
    if state.1 then
      let count := state.2.getD c 0
      if count == 0 then (false, state.2)
      else (true, state.2.insert c (count - 1))
    else state) (true, magCounts)
  result.1
end Impl

section TestCases
-- Test case 1: Example 1: ransomNote = "a", magazine = "b" => false
def test1_ransomNote : List Char := ['a']
def test1_magazine : List Char := ['b']
def test1_Expected : Bool := false

-- Test case 2: Example 2: ransomNote = "aa", magazine = "ab" => false
def test2_ransomNote : List Char := ['a', 'a']
def test2_magazine : List Char := ['a', 'b']
def test2_Expected : Bool := false

-- Test case 3: Example 3: ransomNote = "aa", magazine = "aab" => true
def test3_ransomNote : List Char := ['a', 'a']
def test3_magazine : List Char := ['a', 'a', 'b']
def test3_Expected : Bool := true

-- Test case 4: Edge: empty ransom note, empty magazine => true
def test4_ransomNote : List Char := []
def test4_magazine : List Char := []
def test4_Expected : Bool := true

-- Test case 5: Edge: empty ransom note, nonempty magazine => true
def test5_ransomNote : List Char := []
def test5_magazine : List Char := ['x', 'y']
def test5_Expected : Bool := true

-- Test case 6: Edge: nonempty ransom note, empty magazine => false
def test6_ransomNote : List Char := ['z']
def test6_magazine : List Char := []
def test6_Expected : Bool := false

-- Test case 7: Exact match with repeats => true
def test7_ransomNote : List Char := ['a', 'b', 'c', 'a']
def test7_magazine : List Char := ['a', 'b', 'c', 'a']
def test7_Expected : Bool := true

-- Test case 8: Insufficient multiplicity for one letter => false
def test8_ransomNote : List Char := ['a', 'b', 'b']
def test8_magazine : List Char := ['b', 'a']
def test8_Expected : Bool := false

-- Test case 9: Magazine has extra letters and permuted order => true
def test9_ransomNote : List Char := ['c', 'a', 't']
def test9_magazine : List Char := ['t', 'a', 'c', 'h', 'e', 'r']
def test9_Expected : Bool := true
end TestCases

section Assertions
-- Test case 1
#assert_same_evaluation #[(implementation test1_ransomNote test1_magazine), test1_Expected]

-- Test case 2
#assert_same_evaluation #[(implementation test2_ransomNote test2_magazine), test2_Expected]

-- Test case 3
#assert_same_evaluation #[(implementation test3_ransomNote test3_magazine), test3_Expected]

-- Test case 4
#assert_same_evaluation #[(implementation test4_ransomNote test4_magazine), test4_Expected]

-- Test case 5
#assert_same_evaluation #[(implementation test5_ransomNote test5_magazine), test5_Expected]

-- Test case 6
#assert_same_evaluation #[(implementation test6_ransomNote test6_magazine), test6_Expected]

-- Test case 7
#assert_same_evaluation #[(implementation test7_ransomNote test7_magazine), test7_Expected]

-- Test case 8
#assert_same_evaluation #[(implementation test8_ransomNote test8_magazine), test8_Expected]

-- Test case 9
#assert_same_evaluation #[(implementation test9_ransomNote test9_magazine), test9_Expected]
end Assertions

section Pbt
method implementationPbt (ransomNote : List Char) (magazine : List Char)
  return (result : Bool)
  require precondition ransomNote magazine
  ensures postcondition ransomNote magazine result
  do
  return (implementation ransomNote magazine)

velvet_plausible_test implementationPbt (config := { maxMs := some 20000 })
end Pbt

section Proof
theorem correctness_goal_0_0 : ∀ (l : List Char) (m : Std.HashMap Char ℕ) (c : Char),
  (List.foldl (fun m c => m.insert c (m.getD c 0 + 1)) m l).getD c 0 = m.getD c 0 + List.count c l := by
    intro l
    induction l with
    | nil => intro m c; simp [List.count]
    | cons hd tl ih =>
      intro m c
      simp only [List.foldl_cons]
      rw [ih]
      simp only [List.count_cons]
      by_cases h : hd = c
      · subst h
        simp [Std.HashMap.getD_insert]
        omega
      · have hne : (hd == c) = false := by simp [beq_iff_eq, h]
        simp [hne]
        rw [Std.HashMap.getD_insert]
        simp [beq_iff_eq, h]

theorem correctness_goal_0
    (magazine : List Char)
    : ∀ (c : Char),
  (List.foldl (fun m c => m.insert c (m.getD c 0 + 1)) Std.HashMap.empty magazine).getD c 0 = List.count c magazine := by
    have gen : ∀ (l : List Char) (m : Std.HashMap Char Nat) (c : Char),
      (List.foldl (fun m c => m.insert c (m.getD c 0 + 1)) m l).getD c 0 = m.getD c 0 + List.count c l := by
      expose_names; exact (correctness_goal_0_0)
    intro c
    simp [gen magazine Std.HashMap.empty c, Std.HashMap.getD_empty]

theorem foldl_false_stays_false (l : List Char) (m : Std.HashMap Char ℕ) :
    (List.foldl
          (fun state c =>
            if state.1 = true then
              if (state.2.getD c 0 == 0) = true then (false, state.2)
              else (true, state.2.insert c (state.2.getD c 0 - 1))
            else state)
          (false, m) l).1 = false := by
  induction l generalizing m with
  | nil => simp [List.foldl]
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact ih m

theorem hashmap_getD_insert (m : Std.HashMap Char ℕ) (k k' : Char) (v : ℕ) :
    (m.insert k v).getD k' 0 = if k == k' then v else m.getD k' 0 := by
  simp [Std.HashMap.getD_insert]

theorem foldl_false_stays_false' (l : List Char) (m : Std.HashMap Char ℕ) :
    (List.foldl
          (fun state c =>
            if state.1 = true then
              if state.2.getD c 0 = 0 then (false, state.2)
              else (true, state.2.insert c (state.2.getD c 0 - 1))
            else state)
          (false, m) l).1 = false := by
  induction l generalizing m with
  | nil => simp [List.foldl]
  | cons hd tl ih =>
    simp only [List.foldl_cons, Bool.false_eq_true, ↓reduceIte]
    exact ih m


theorem correctness_goal_1_0 : ∀ (l : List Char) (m : Std.HashMap Char ℕ),
  (List.foldl
          (fun state c =>
            if state.1 = true then
              if (state.2.getD c 0 == 0) = true then (false, state.2)
              else (true, state.2.insert c (state.2.getD c 0 - 1))
            else state)
          (true, m) l).1 =
      true ↔
    ∀ (c : Char), List.count c l ≤ m.getD c 0 := by
    intro l
    induction l with
    | nil =>
      intro m
      simp [List.foldl, List.count]
    | cons hd tl ih =>
      intro m
      simp only [List.foldl_cons, decide_eq_true_eq, beq_iff_eq]
      by_cases h_zero : m.getD hd 0 = 0
      · -- m.getD hd 0 = 0, state becomes (false, m)
        simp only [h_zero, ↓reduceIte]
        rw [foldl_false_stays_false']
        constructor
        · intro h; exact absurd h (by decide)
        · intro h
          have h_hd := h hd
          simp [List.count_cons_self] at h_hd
          omega
      · -- m.getD hd 0 ≠ 0
        have h_pos : m.getD hd 0 > 0 := Nat.pos_of_ne_zero h_zero
        simp only [h_zero, ↓reduceIte]
        -- Now the goal should be about the foldl over tl with (true, m.insert hd (m.getD hd 0 - 1))
        -- But the foldl function uses `== 0` which was simplified to `= 0` by beq_iff_eq
        -- Let me use convert or try to match the ih
        have key : ∀ (m' : Std.HashMap Char ℕ),
          (List.foldl
            (fun state c =>
              if state.1 = true then
                if state.2.getD c 0 = 0 then (false, state.2)
                else (true, state.2.insert c (state.2.getD c 0 - 1))
              else state)
            (true, m') tl).1 = true ↔
          ∀ (c : Char), List.count c tl ≤ m'.getD c 0 := by
          intro m'
          have := ih m'
          simp only [decide_eq_true_eq, beq_iff_eq] at this
          exact this
        rw [key]
        constructor
        · intro h c
          by_cases hc : hd = c
          · subst hc
            have := h hd
            simp [hashmap_getD_insert, beq_self_eq_true] at this
            simp [List.count_cons_self]
            omega
          · have := h c
            simp [hashmap_getD_insert, beq_iff_eq, hc] at this
            simp [List.count_cons_of_ne hc]
            exact this
        · intro h c
          by_cases hc : hd = c
          · subst hc
            have := h hd
            simp [List.count_cons_self] at this
            simp [hashmap_getD_insert, beq_self_eq_true]
            omega
          · have := h c
            simp [List.count_cons_of_ne hc] at this
            simp [hashmap_getD_insert, beq_iff_eq, hc]
            exact this

theorem correctness_goal_1
    (ransomNote : List Char)
    (magazine : List Char)
    : ∀ (counts : Std.HashMap Char ℕ),
  (∀ (c : Char), counts.getD c 0 = List.count c magazine) →
    ((List.foldl
            (fun state c =>
              if state.1 = true then
                if (state.2.getD c 0 == 0) = true then (false, state.2)
                else (true, state.2.insert c (state.2.getD c 0 - 1))
              else state)
            (true, counts) ransomNote).1 =
        true ↔
      ∀ (c : Char), List.count c ransomNote ≤ List.count c magazine) := by
  -- We prove by strong induction with a generalized invariant.
  -- Key helper: the foldl with (true, m) over a list l returns true iff for all c, l.count c ≤ m.getD c 0
  have h_general : ∀ (l : List Char) (m : Std.HashMap Char ℕ),
    (List.foldl
            (fun state c =>
              if state.1 = true then
                if (state.2.getD c 0 == 0) = true then (false, state.2)
                else (true, state.2.insert c (state.2.getD c 0 - 1))
              else state)
            (true, m) l).1 = true ↔
      ∀ (c : Char), List.count c l ≤ m.getD c 0 := by expose_names; exact (correctness_goal_1_0)
  intro counts h_counts
  rw [h_general]
  constructor
  · intro h c
    rw [← h_counts c]
    exact h c
  · intro h c
    rw [h_counts c]
    exact h c

theorem correctness_goal
    (ransomNote : List Char)
    (magazine : List Char)
    : postcondition ransomNote magazine (implementation ransomNote magazine) := by
    unfold postcondition implementation canConstructProp
    simp only []
    -- Phase 1: magCounts correctness
    have h_mag : ∀ c : Char, (List.foldl (fun (m : Std.HashMap Char Nat) c => m.insert c (m.getD c 0 + 1)) Std.HashMap.empty magazine).getD c 0 = List.count c magazine := by expose_names; exact (correctness_goal_0 magazine)
    -- Phase 2: the fold over ransomNote correctly checks the condition
    have h_phase2 : ∀ (counts : Std.HashMap Char Nat),
      (∀ c, counts.getD c 0 = List.count c magazine) →
      ((List.foldl
        (fun state c =>
          if state.1 = true then
            if (state.2.getD c 0 == 0) = true then (false, state.2) else (true, state.2.insert c (state.2.getD c 0 - 1))
          else state)
        (true, counts) ransomNote).1 = true ↔
      ∀ (c : Char), List.count c ransomNote ≤ List.count c magazine) := by expose_names; exact (correctness_goal_1 ransomNote magazine)
    exact (h_phase2 _ h_mag)
end Proof
