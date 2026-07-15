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
  pure (-1)

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
