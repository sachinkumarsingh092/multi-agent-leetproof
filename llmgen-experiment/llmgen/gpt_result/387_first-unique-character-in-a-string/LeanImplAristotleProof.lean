/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: b28819e2-393a-4674-8c8c-079a611b3782

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem correctness_goal_0_0 (s : Array Char) (h_precond : precondition s) (counts : Array ℕ) (hcounts : counts =
  Array.foldl (fun acc ch => if h : ch.toNat < 128 then acc.setIfInBounds ch.toNat (acc.get! ch.toNat + 1) else acc)
    (mkArray 128 0) s) (c : Char) (hc : isASCII c) (hfold_bridge : Array.foldl (fun acc ch => if h : ch.toNat < 128 then acc.setIfInBounds ch.toNat (acc.get! ch.toNat + 1) else acc)
    (mkArray 128 0) s =
  List.foldl (fun acc ch => if h : ch.toNat < 128 then acc.setIfInBounds ch.toNat (acc.get! ch.toNat + 1) else acc)
    (mkArray 128 0) s.toList) : (List.foldl (fun acc ch => if h : ch.toNat < 128 then acc.setIfInBounds ch.toNat (acc.get! ch.toNat + 1) else acc)
        (mkArray 128 0) s.toList).get!
    c.toNat =
  List.countP (fun x => decide (x = c)) s.toList
-/

import Lean

import Mathlib.Tactic


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

section Proof

theorem correctness_goal_0_0 (s : Array Char) (h_precond : precondition s) (counts : Array ℕ) (hcounts : counts =
  Array.foldl (fun acc ch => if h : ch.toNat < 128 then acc.setIfInBounds ch.toNat (acc.get! ch.toNat + 1) else acc)
    (mkArray 128 0) s) (c : Char) (hc : isASCII c) (hfold_bridge : Array.foldl (fun acc ch => if h : ch.toNat < 128 then acc.setIfInBounds ch.toNat (acc.get! ch.toNat + 1) else acc)
    (mkArray 128 0) s =
  List.foldl (fun acc ch => if h : ch.toNat < 128 then acc.setIfInBounds ch.toNat (acc.get! ch.toNat + 1) else acc)
    (mkArray 128 0) s.toList) : (List.foldl (fun acc ch => if h : ch.toNat < 128 then acc.setIfInBounds ch.toNat (acc.get! ch.toNat + 1) else acc)
        (mkArray 128 0) s.toList).get!
    c.toNat =
  List.countP (fun x => decide (x = c)) s.toList := by
    -- By induction on the list, we can show that the count of character c in the list is equal to the value at index c.toNat in the array after folding.
    have h_ind : ∀ (l : List Char) (c : Char), isASCII c → (List.foldl (fun (acc : Array ℕ) (ch : Char) => if h : ch.toNat < 128 then acc.setIfInBounds ch.toNat (acc.get! ch.toNat + 1) else acc) (Array.mkArray 128 0) l).get! c.toNat = List.countP (fun x => x = c) l := by
      -- We'll use induction on the list `l`.
      intro l c hc
      induction' l using List.reverseRecOn with l ih;
      · -- Since the array is initialized with zeros and the index is within bounds, the get! operation returns 0.
        have h_index_valid : c.toNat < 128 := by
          exact hc;
        have h_get_zero : ∀ i < 128, (Array.replicate 128 0).get! i = 0 := by
          native_decide;
        exact h_get_zero _ h_index_valid;
      · by_cases h : ih.toNat < 128 <;> simp_all +decide [ Array.get! ];
        · split_ifs <;> simp_all +decide [ Array.getElem?_setIfInBounds ];
          · rw [ if_pos ];
            · rfl;
            · induction' l using List.reverseRecOn with l ih;
              · exact h.trans_le ( by native_decide );
              · induction' ( l ++ [ ih ] ) using List.reverseRecOn with l ih <;> aesop;
          · split_ifs <;> simp_all +decide [ Char.ext_iff ];
            exact ‹¬ih.val = c.val› ( by rw [ ← Char.ofNat_toNat ih, ← Char.ofNat_toNat c ] ; aesop );
        · split_ifs <;> simp_all +decide [ Nat.not_lt_of_ge h ];
          · linarith;
          · exact h.not_lt hc;
    exact h_ind _ _ hc

end Proof