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

section Specs
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
method RansomNote (ransomNote : List Char) (magazine : List Char)
  return (result : Bool)
  require precondition ransomNote magazine
  ensures postcondition ransomNote magazine result
  do
  let magArr : Array Char := magazine.toArray
  let noteArr : Array Char := ransomNote.toArray
  -- Build frequency map from magazine
  let mut freqMap : Std.HashMap Char Nat := Std.HashMap.empty
  let mut i : Nat := 0
  while i < magArr.size
    -- Invariant: i is bounded by array size
    -- Init: i=0, trivially 0 ≤ 0 ∧ 0 ≤ magArr.size
    -- Pres: i increments by 1 while i < magArr.size
    -- Suff: needed for safe array access and termination
    invariant "i_bound" 0 ≤ i ∧ i ≤ magArr.size
    -- Invariant: freqMap maps each char to its count in magArr[0..i]
    -- Init: i=0, empty map getD returns 0, take 0 count is 0
    -- Pres: inserting c with cur+1 updates count correctly
    -- Suff: at loop exit, freqMap holds full magazine char counts
    invariant "freq_map_counts" ∀ c : Char, freqMap.getD c 0 = (magArr.toList.take i).count c
    decreasing magArr.size - i
  do
    let c := magArr[i]!
    let cur := freqMap.getD c 0
    freqMap := freqMap.insert c (cur + 1)
    i := i + 1
  -- Check ransom note against frequency map
  let mut j : Nat := 0
  let mut canConstruct : Bool := true
  while j < noteArr.size ∧ canConstruct
    -- Invariant: j is bounded by array size
    -- Init: j=0, trivially holds
    -- Pres: j increments by 1 only in else branch
    -- Suff: needed for safe array access
    invariant "j_bound" 0 ≤ j ∧ j ≤ noteArr.size
    -- Invariant: freqMap reflects magazine counts minus consumed ransom note chars
    -- Init: j=0, take 0 is empty, so magazine.count c - 0 = magazine.count c
    -- Pres: in else branch, decrement freqMap for char c and advance j
    -- Suff: at exit, freqMap reflects remaining availability
    invariant "freq_map_remaining" ∀ c : Char, freqMap.getD c 0 = magazine.count c - (noteArr.toList.take j).count c
    -- Invariant: if canConstruct is true, all chars so far were available
    -- Init: j=0, vacuously true (take 0 is empty)
    -- Pres: only advance j when cur > 0
    -- Suff: at exit with canConstruct=true and j=noteArr.size, all ransomNote chars available
    invariant "can_construct_means_sufficient" canConstruct = true → ∀ c : Char, (noteArr.toList.take j).count c ≤ magazine.count c
    -- Invariant: if canConstruct is false, some char in ransomNote exceeds magazine supply
    -- Init: canConstruct=true, vacuously true
    -- Pres: set to false when cur=0, meaning magazine.count c = (take j).count c,
    --   but ransomNote has more of c (at index j and beyond), so magazine.count c < ransomNote.count c
    -- Suff: at exit with canConstruct=false, ¬canConstructProp
    invariant "cannot_construct_means_fail" canConstruct = false → ∃ c : Char, magazine.count c < ransomNote.count c
    done_with (j = noteArr.size ∨ canConstruct = false)
    -- Decreasing: composite measure that decreases in both branches
    -- When cur > 0: j increases, so 2*(size-j) decreases by 2
    -- When cur = 0: canConstruct goes true→false, so +1 → +0, decreases by 1
    decreasing 2 * (noteArr.size - j) + (if canConstruct then 1 else 0)
  do
    let c := noteArr[j]!
    let cur := freqMap.getD c 0
    if cur = 0 then
      canConstruct := false
    else
      freqMap := freqMap.insert c (cur - 1)
      j := j + 1
  return canConstruct
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

#assert_same_evaluation #[((RansomNote test1_ransomNote test1_magazine).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((RansomNote test2_ransomNote test2_magazine).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((RansomNote test3_ransomNote test3_magazine).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((RansomNote test4_ransomNote test4_magazine).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((RansomNote test5_ransomNote test5_magazine).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((RansomNote test6_ransomNote test6_magazine).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((RansomNote test7_ransomNote test7_magazine).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((RansomNote test8_ransomNote test8_magazine).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((RansomNote test9_ransomNote test9_magazine).run), DivM.res test9_Expected ]
end Assertions

section Pbt
velvet_plausible_test RansomNote (config := { maxMs := some 20000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000

theorem goal_0
    (magazine : List Char)
    (freqMap : Std.HashMap Char ℕ)
    (i : ℕ)
    (invariant_freq_map_counts : ∀ (c : Char), freqMap.getD c (OfNat.ofNat 0) = List.count c (List.take i magazine))
    (if_pos : i < magazine.length)
    : ∀ (c : Char), (freqMap.insert (magazine[i]?.getD 'A') (freqMap.getD (magazine[i]?.getD 'A') (OfNat.ofNat 0) + OfNat.ofNat 1)).getD c (OfNat.ofNat 0) = List.count c (List.take (i + OfNat.ofNat 1) magazine) := by
    intro c
    have h_get : magazine[i]?.getD 'A' = magazine[i]'if_pos := by
      simp [List.getD_getElem?, if_pos]
    rw [h_get]
    rw [List.take_succ_eq_append_getElem if_pos]
    rw [List.count_append, List.count_singleton]
    rw [Std.HashMap.getD_insert]
    by_cases hc : magazine[i]'if_pos == c
    · have hceq : magazine[i]'if_pos = c := beq_iff_eq.mp hc
      simp [hceq, invariant_freq_map_counts]
    · have hcne : ¬(magazine[i]'if_pos = c) := by
        intro h
        simp [h] at hc
      simp [hcne, invariant_freq_map_counts]

theorem goal_1
    (ransomNote : List Char)
    (magazine : List Char)
    (freqMap_1 : Std.HashMap Char ℕ)
    (j : ℕ)
    (invariant_freq_map_remaining : ∀ (c : Char), freqMap_1.getD c (OfNat.ofNat 0) = List.count c magazine - List.count c (List.take j ransomNote))
    (a_4 : j < ransomNote.length)
    (if_pos : freqMap_1.getD (ransomNote[j]?.getD 'A') (OfNat.ofNat 0) = OfNat.ofNat 0)
    (invariant_can_construct_means_sufficient : ∀ (c : Char), List.count c (List.take j ransomNote) ≤ List.count c magazine)
    : ∃ c, List.count c magazine < List.count c ransomNote := by
    set c₀ := ransomNote[j]?.getD 'A' with hc₀_def
    have h1 : List.count c₀ magazine - List.count c₀ (List.take j ransomNote) = 0 := by
      have := invariant_freq_map_remaining c₀
      rw [if_pos] at this
      exact this.symm
    have h2 : List.count c₀ (List.take j ransomNote) ≤ List.count c₀ magazine :=
      invariant_can_construct_means_sufficient c₀
    have h3 : List.count c₀ magazine = List.count c₀ (List.take j ransomNote) := by omega
    have hj : j < ransomNote.length := a_4
    have hc₀ : c₀ = ransomNote[j] := by
      simp [hc₀_def, List.getD_getElem?, hj]
    have hdrop : List.drop j ransomNote = ransomNote[j] :: List.drop (j + 1) ransomNote :=
      List.drop_eq_getElem_cons hj
    have hsplit : List.count c₀ ransomNote = List.count c₀ (List.take j ransomNote) + List.count c₀ (List.drop j ransomNote) := by
      conv_lhs => rw [← List.take_append_drop j ransomNote]
      rw [List.count_append]
    have hcount_drop : List.count c₀ (List.drop j ransomNote) ≥ 1 := by
      rw [hdrop, hc₀, List.count_cons_self]
      omega
    exact ⟨c₀, by omega⟩

theorem goal_2_0
    (ransomNote : List Char)
    (j : ℕ)
    (a_4 : j < ransomNote.length)
    (h_getElem_some : ransomNote[j]? = some ransomNote[j])
    : ∀ (c : Char),
  List.count c (List.take (j + 1) ransomNote) =
    List.count c (List.take j ransomNote) + List.count c ransomNote[j]?.toList := by
    intro c
    rw [List.take_succ_eq_append_getElem a_4, List.count_append]
    congr 1
    rw [h_getElem_some, Option.toList_some]

theorem goal_2
    (ransomNote : List Char)
    (magazine : List Char)
    (i_2 : ℕ)
    (freqMap_1 : Std.HashMap Char ℕ)
    (j : ℕ)
    (invariant_freq_map_remaining : ∀ (c : Char), freqMap_1.getD c (OfNat.ofNat 0) = List.count c magazine - List.count c (List.take j ransomNote))
    (a_4 : j < ransomNote.length)
    (if_neg : ¬freqMap_1.getD (ransomNote[j]?.getD 'A') (OfNat.ofNat 0) = OfNat.ofNat 0)
    (a_1 : i_2 ≤ magazine.length)
    (done_1 : magazine.length ≤ i_2)
    (invariant_can_construct_means_sufficient : ∀ (c : Char), List.count c (List.take j ransomNote) ≤ List.count c magazine)
    : ∀ (c : Char), (freqMap_1.insert (ransomNote[j]?.getD 'A') (freqMap_1.getD (ransomNote[j]?.getD 'A') (OfNat.ofNat 0) - OfNat.ofNat 1)).getD c (OfNat.ofNat 0) = List.count c magazine - List.count c (List.take (j + OfNat.ofNat 1) ransomNote) := by
    have h_getElem_some : ransomNote[j]? = some ransomNote[j] := by
      exact List.getElem?_eq_some_getElem_iff (by omega) |>.mpr trivial
    have h_ch_eq : ransomNote[j]?.getD 'A' = ransomNote[j] := by
      rw [h_getElem_some]; simp
    have h_count_succ : ∀ c : Char, List.count c (List.take (j + 1) ransomNote) = List.count c (List.take j ransomNote) + List.count c (ransomNote[j]?.toList) := by
      expose_names; exact (goal_2_0 ransomNote j a_4 h_getElem_some)
    have h_count_toList : ∀ c : Char, List.count c (ransomNote[j]?.toList) = if ransomNote[j] == c then 1 else 0 := by
      expose_names; intros; expose_names; try simp_all; try grind
    have h_sufficient_ch : List.count (ransomNote[j]) (List.take j ransomNote) < List.count (ransomNote[j]) magazine := by
      expose_names; intros; expose_names; try simp_all; try grind
    intro c
    rw [h_count_succ, h_count_toList, h_ch_eq]
    by_cases hc : c = ransomNote[j]
    · -- Case c = ransomNote[j]
      subst hc
      have h_getD_insert_eq : (freqMap_1.insert ransomNote[j] (freqMap_1.getD ransomNote[j] 0 - 1)).getD ransomNote[j] 0 = freqMap_1.getD ransomNote[j] 0 - 1 := by
        expose_names; intros; expose_names; try simp_all; try grind
      rw [h_getD_insert_eq]
      simp [beq_self_eq_true]
      rw [invariant_freq_map_remaining ransomNote[j]]
      omega
    · -- Case c ≠ ransomNote[j]
      have hne : ¬(ransomNote[j] == c) = true := by
        simp; exact fun h => hc h.symm
      have h_getD_insert_ne : (freqMap_1.insert (ransomNote[j]) (freqMap_1.getD (ransomNote[j]) 0 - 1)).getD c 0 = freqMap_1.getD c 0 := by
        expose_names; intros; expose_names; try simp_all; try grind
      rw [h_getD_insert_ne]
      simp [hne]
      exact invariant_freq_map_remaining c

theorem goal_3
    (ransomNote : List Char)
    (magazine : List Char)
    (freqMap_1 : Std.HashMap Char ℕ)
    (j : ℕ)
    (invariant_freq_map_remaining : ∀ (c : Char), freqMap_1.getD c (OfNat.ofNat 0) = List.count c magazine - List.count c (List.take j ransomNote))
    (a_4 : j < ransomNote.length)
    (if_neg : ¬freqMap_1.getD (ransomNote[j]?.getD 'A') (OfNat.ofNat 0) = OfNat.ofNat 0)
    (invariant_can_construct_means_sufficient : ∀ (c : Char), List.count c (List.take j ransomNote) ≤ List.count c magazine)
    : ∀ (c : Char), List.count c (List.take (j + OfNat.ofNat 1) ransomNote) ≤ List.count c magazine := by
    intro c
    have h_some : ransomNote[j]? = some ransomNote[j] := List.getElem?_eq_getElem a_4
    have h_getD : ransomNote[j]?.getD 'A' = ransomNote[j] := by simp [h_some]
    rw [List.take_succ_eq_append_getElem a_4, List.count_append]
    by_cases hc : c = ransomNote[j]
    · -- c = ransomNote[j]: count increases by 1
      subst hc
      rw [List.count_singleton_self]
      have h_freq := invariant_freq_map_remaining ransomNote[j]
      rw [h_getD] at if_neg
      rw [h_freq] at if_neg
      have h_suff := invariant_can_construct_means_sufficient ransomNote[j]
      -- if_neg : ¬(magazine.count _ - (take j).count _ = 0)
      -- h_suff : (take j).count _ ≤ magazine.count _
      -- goal : (take j).count _ + 1 ≤ magazine.count _
      change ¬(_ = (0 : ℕ)) at if_neg
      omega
    · -- c ≠ ransomNote[j]: count unchanged
      have : List.count c [ransomNote[j]] = 0 := by
        rw [List.count_singleton]
        simp [Ne.symm hc]
      rw [this, Nat.add_zero]
      exact invariant_can_construct_means_sufficient c


prove_correct RansomNote by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at *); try (conv => congr <;> simp) ; try expose_names)
  exact (goal_0 magazine freqMap i invariant_freq_map_counts if_pos)
  exact (goal_1 ransomNote magazine freqMap_1 j invariant_freq_map_remaining a_4 if_pos invariant_can_construct_means_sufficient)
  exact (goal_2 ransomNote magazine i_2 freqMap_1 j invariant_freq_map_remaining a_4 if_neg a_1 done_1 invariant_can_construct_means_sufficient)
  exact (goal_3 ransomNote magazine freqMap_1 j invariant_freq_map_remaining a_4 if_neg invariant_can_construct_means_sufficient)
end Proof
