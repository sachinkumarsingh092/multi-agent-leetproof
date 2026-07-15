import Lean
import Mathlib.Tactic
import Velvet.Std

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
  -- Build frequency table for ASCII chars (0..127) in O(n) time.
  -- We use `get!`/`set!` because the table is always of size 128.
  let counts : Array Nat :=
    s.foldl
      (fun acc ch =>
        let i := ch.toNat
        if h : i < 128 then
          let cur := acc.get! i
          acc.set! i (cur + 1)
        else
          acc)
      (Array.mkArray 128 0)

  -- Scan for first index whose character has frequency 1.
  let rec findFirst (idx : Nat) : Int :=
    if h : idx < s.size then
      let ch := s[idx]!
      let i := ch.toNat
      if hi : i < 128 then
        if counts.get! i = 1 then
          Int.ofNat idx
        else
          findFirst (idx + 1)
      else
        findFirst (idx + 1)
    else
      (-1)
  findFirst 0
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

section Proof
theorem correctness_goal_0_0
    (s : Array Char)
    (h_precond : precondition s)
    (counts : Array ℕ)
    (hcounts : counts =
  Array.foldl (fun acc ch => if h : ch.toNat < 128 then acc.setIfInBounds ch.toNat (acc.get! ch.toNat + 1) else acc)
    (mkArray 128 0) s)
    (c : Char)
    (hc : isASCII c)
    (hfold_bridge : Array.foldl (fun acc ch => if h : ch.toNat < 128 then acc.setIfInBounds ch.toNat (acc.get! ch.toNat + 1) else acc)
    (mkArray 128 0) s =
  List.foldl (fun acc ch => if h : ch.toNat < 128 then acc.setIfInBounds ch.toNat (acc.get! ch.toNat + 1) else acc)
    (mkArray 128 0) s.toList)
    : (List.foldl (fun acc ch => if h : ch.toNat < 128 then acc.setIfInBounds ch.toNat (acc.get! ch.toNat + 1) else acc)
        (mkArray 128 0) s.toList).get!
    c.toNat =
  List.countP (fun x => decide (x = c)) s.toList := by
    sorry

theorem correctness_goal_0
    (s : Array Char)
    (h_precond : precondition s)
    (counts : Array ℕ)
    (hcounts : counts =
  Array.foldl (fun acc ch => if h : ch.toNat < 128 then acc.setIfInBounds ch.toNat (acc.get! ch.toNat + 1) else acc)
    (mkArray 128 0) s)
    : ∀ (c : Char), isASCII c → counts.get! c.toNat = charCount s c := by
  intro c hc
  dsimp [isASCII] at hc

  have hfold_bridge :
      Array.foldl
          (fun acc ch =>
            if h : ch.toNat < 128 then acc.setIfInBounds ch.toNat (acc.get! ch.toNat + 1) else acc)
          (Array.mkArray 128 0) s
        =
      List.foldl
          (fun acc ch =>
            if h : ch.toNat < 128 then acc.setIfInBounds ch.toNat (acc.get! ch.toNat + 1) else acc)
          (Array.mkArray 128 0) s.toList := by
    expose_names; intros; expose_names; try simp_all; try grind

  have hfold_list :
      (List.foldl
          (fun acc ch =>
            if h : ch.toNat < 128 then acc.setIfInBounds ch.toNat (acc.get! ch.toNat + 1) else acc)
          (Array.mkArray 128 0) s.toList).get! c.toNat
        =
      s.toList.countP (fun x => decide (x = c)) := by
    expose_names; exact (correctness_goal_0_0 s h_precond counts hcounts c hc hfold_bridge)

  -- finish
  rw [hcounts]
  change
      (Array.foldl
          (fun acc ch =>
            if h : ch.toNat < 128 then acc.setIfInBounds ch.toNat (acc.get! ch.toNat + 1) else acc)
          (mkArray 128 0) s).get!
        c.toNat
      = charCount s c
  -- use bridge
  rw [hfold_bridge]
  -- unfold charCount and rewrite array countP to list countP
  dsimp [charCount]
  rw [← Array.countP_toList (xs := s) (p := fun x => decide (x = c))]
  -- now the goal matches
  exact hfold_list

theorem correctness_goal_1
    (s : Array Char)
    (h_precond : precondition s)
    (counts : Array ℕ)
    (h_counts_spec : ∀ (c : Char), isASCII c → counts.get! c.toNat = charCount s c)
    : postcondition s (implementation.findFirst s counts 0) := by
  classical

  -- In-bounds `get!` agrees with `getElem`.
  have getBang_eq_get (i : Nat) (hi : i < s.size) : s[i]! = s[i] := by
    simp [Array.get!, hi]

  refine And.intro ?uniqueCase ?noUniqueCase

  · intro hex
    let p : Nat → Prop := fun i => i < s.size ∧ charCount s (s[i]!) = 1
    have hp : ∃ i, p i := hex
    let m : Nat := Nat.find hp
    have hm : p m := Nat.find_spec hp
    have hm_lt : m < s.size := hm.1

    have hnoneBefore : ∀ j, j < m → charCount s (s[j]!) ≠ 1 := by
      intro j hj
      have hjSize : j < s.size := lt_trans hj hm_lt
      have hnotp : ¬ p j := Nat.find_min hp hj
      intro hcount
      apply hnotp
      exact ⟨hjSize, hcount⟩

    have hfind_from : ∀ idx, idx ≤ m → implementation.findFirst s counts idx = (Int.ofNat m) := by
      intro idx hidx
      generalize hd : m - idx = d
      induction d generalizing idx with
      | zero =>
          have hmle : m ≤ idx := (Nat.sub_eq_zero_iff_le).1 hd
          have hidx' : idx = m := Nat.le_antisymm hidx hmle
          subst hidx'
          have hascii! : isASCII (s[m]!) := h_precond m hm_lt
          have hascii : isASCII (s[m]) := by
            simpa [getBang_eq_get m hm_lt] using hascii!
          have hiNat : (s[m]).toNat < 128 := by
            simpa [isASCII] using hascii
          have hm2 : charCount s (s[m]) = 1 := by
            simpa [getBang_eq_get m hm_lt] using hm.2
          have hcount : counts.get! (s[m]).toNat = 1 := by
            simpa [h_counts_spec (s[m]) hascii] using hm2
          unfold implementation.findFirst
          simp [hm_lt, hiNat, hcount]
      | succ d ih =>
          have hlt : idx < m := Nat.lt_of_sub_eq_succ hd
          have hidxSize : idx < s.size := lt_trans hlt hm_lt
          have hascii! : isASCII (s[idx]!) := h_precond idx hidxSize
          have hascii : isASCII (s[idx]) := by
            simpa [getBang_eq_get idx hidxSize] using hascii!
          have hiNat : (s[idx]).toNat < 128 := by
            simpa [isASCII] using hascii
          have hcountNe! : charCount s (s[idx]!) ≠ 1 := hnoneBefore idx hlt
          have hcountNe : charCount s (s[idx]) ≠ 1 := by
            simpa [getBang_eq_get idx hidxSize] using hcountNe!
          have hneq : counts.get! (s[idx]).toNat ≠ 1 := by
            simpa [h_counts_spec (s[idx]) hascii] using hcountNe
          have hrecurse : implementation.findFirst s counts idx = implementation.findFirst s counts (idx + 1) := by
            conv_lhs =>
              unfold implementation.findFirst
              simp [hidxSize, hiNat, hneq]
          have hidx' : idx + 1 ≤ m := Nat.succ_le_of_lt hlt
          have hd' : m - (idx + 1) = d := by
            simpa [Nat.succ_eq_add_one, hd] using (Nat.sub_succ m idx)
          calc
            implementation.findFirst s counts idx
                = implementation.findFirst s counts (idx + 1) := hrecurse
            _   = Int.ofNat m := ih (idx := idx + 1) hidx' hd'

    have hfind : implementation.findFirst s counts 0 = (Int.ofNat m) :=
      hfind_from 0 (Nat.zero_le _)

    refine And.intro ?nonneg ?rest
    · simpa [hfind] using (Int.ofNat_nonneg m)
    · refine And.intro ?idxBound ?rest2
      · simpa [hfind, Int.toNat_ofNat] using hm_lt
      refine And.intro ?countEq ?minimal
      · simpa [hfind, Int.toNat_ofNat] using hm.2
      · intro j hj
        have hj' : j < m := by
          simpa [hfind, Int.toNat_ofNat] using hj
        exact hnoneBefore j hj'

  · intro hnone
    have hnoneAll : ∀ i, i < s.size → charCount s (s[i]!) ≠ 1 := by
      intro i hi
      intro hcount
      apply hnone
      exact ⟨i, hi, hcount⟩

    have hfind_neg1_from : ∀ idx, idx ≤ s.size → implementation.findFirst s counts idx = (-1) := by
      intro idx hle
      generalize hd : s.size - idx = d
      induction d generalizing idx with
      | zero =>
          have hge : s.size ≤ idx := (Nat.sub_eq_zero_iff_le).1 hd
          have hnotlt : ¬ idx < s.size := Nat.not_lt.mpr hge
          unfold implementation.findFirst
          simp [hnotlt]
      | succ d ih =>
          have hlt : idx < s.size := Nat.lt_of_sub_eq_succ hd
          have hascii! : isASCII (s[idx]!) := h_precond idx hlt
          have hascii : isASCII (s[idx]) := by
            simpa [getBang_eq_get idx hlt] using hascii!
          have hiNat : (s[idx]).toNat < 128 := by
            simpa [isASCII] using hascii
          have hcountNe! : charCount s (s[idx]!) ≠ 1 := hnoneAll idx hlt
          have hcountNe : charCount s (s[idx]) ≠ 1 := by
            simpa [getBang_eq_get idx hlt] using hcountNe!
          have hneq : counts.get! (s[idx]).toNat ≠ 1 := by
            simpa [h_counts_spec (s[idx]) hascii] using hcountNe
          have hrecurse : implementation.findFirst s counts idx = implementation.findFirst s counts (idx + 1) := by
            conv_lhs =>
              unfold implementation.findFirst
              simp [hlt, hiNat, hneq]
          have hle' : idx + 1 ≤ s.size := Nat.succ_le_of_lt hlt
          have hd' : s.size - (idx + 1) = d := by
            simpa [Nat.succ_eq_add_one, hd] using (Nat.sub_succ s.size idx)
          calc
            implementation.findFirst s counts idx
                = implementation.findFirst s counts (idx + 1) := hrecurse
            _   = -1 := ih (idx := idx + 1) hle' hd'

    have hres : implementation.findFirst s counts 0 = (-1) :=
      hfind_neg1_from 0 (Nat.zero_le _)

    refine And.intro hres ?_
    intro i hi
    exact hnoneAll i hi

theorem correctness_goal
    (s : Array Char)
    (h_precond : precondition s)
    : postcondition s (implementation s) := by
  classical
  -- unfold implementation enough to expose the internal scanner and counts
  simp [implementation]
  -- goal is now about `implementation.findFirst` with the computed `counts`
  -- Name the computed counts table.
  set counts : Array Nat :=
    Array.foldl
      (fun acc ch =>
        if h : ch.toNat < 128 then
          acc.setIfInBounds ch.toNat (acc.get! ch.toNat + 1)
        else
          acc)
      (Array.mkArray 128 0) s with hcounts

  -- Bridge lemma: the table entry equals `charCount` for ASCII characters.
  have h_counts_spec :
      ∀ c : Char, isASCII c → counts.get! c.toNat = charCount s c := by
    expose_names; exact (correctness_goal_0 s h_precond counts hcounts)

  -- Prove the postcondition for the scanner output.
  have h_scan : postcondition s (implementation.findFirst s counts 0) := by
    expose_names; exact (correctness_goal_1 s h_precond counts h_counts_spec)

  simpa [hcounts] using h_scan
end Proof
