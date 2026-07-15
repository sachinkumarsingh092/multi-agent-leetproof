import Lean
import Mathlib.Tactic
import Helper

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

section Proof

theorem correctness_goal_1_0 (s : Array Char) (h_precond : precondition s) (result : ℤ × ℕ) (c : Char) (hc : c.toNat < 128) (hresult_def : result =
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
    (-1, 0) s) (h_counts_size : (Array.foldl
      (fun acc c =>
        let idx := c.toNat;
        if idx < acc.size then acc.set! idx (acc[idx]! + 1) else acc)
      (mkArray 128 0) s).size =
  128) (f : Array ℕ → Char → Array ℕ) (hf_def : f = fun acc ch =>
  let idx := ch.toNat;
  if idx < acc.size then acc.set! idx (acc[idx]! + 1) else acc) : ∀ (ch : Char), ch.toNat < 128 → (Array.foldl f (mkArray 128 0) s)[ch.toNat]! = Array.countP (fun x => decide (x = ch)) s := by
    intro ch hch
    subst hf_def
    rw [← Array.foldl_toList, ← Array.countP_toList]
    rw [foldl_freq_count_list s.toList ch hch (mkArray 128 0) (by simp [mkArray])]
    set_option maxRecDepth 2048 in
    have : (mkArray 128 (0:Nat))[ch.toNat]! = 0 := by
      show Array.getD (mkArray 128 0) ch.toNat 0 = 0
      simp only [Array.getD, mkArray, Array.size, List.length_replicate, hch, ↓reduceDIte, Array.getInternal]
      exact List.getElem_replicate ..
    omega
end Proof
