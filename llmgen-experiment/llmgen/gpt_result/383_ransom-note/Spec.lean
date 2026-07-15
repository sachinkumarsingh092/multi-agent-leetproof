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
  pure false  -- placeholder

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
