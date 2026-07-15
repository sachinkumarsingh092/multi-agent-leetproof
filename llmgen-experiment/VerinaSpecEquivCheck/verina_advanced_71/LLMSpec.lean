import Velvet.Std
import Extensions.Tactics
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false
set_option pp.funBinderTypes true
set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

/- Problem Description
    ShortestSubstringWithKOnes: Find the shortest contiguous substring of a binary string containing exactly k occurrences of '1'.
    Natural language breakdown:
    1. The input s is a finite sequence of characters, and it is intended to be binary: every character is '0' or '1'.
    2. A candidate answer is a non-empty contiguous substring of s.
    3. A candidate is valid exactly when it contains exactly k characters equal to '1'.
    4. If at least one valid candidate exists, the output must be a valid candidate with minimal length.
    5. If multiple valid candidates have the same minimal length, the output must be the lexicographically smallest among them.
    6. If no valid candidate exists, the output must be the empty sequence.
-/

section Specs
-- We model the input/output "string" as `List Char` to avoid `String` indexing with `String.Pos`.
-- A contiguous substring is described by a start index `i` and a length `len`.

def sliceChars (s : List Char) (i : Nat) (len : Nat) : List Char :=
  (s.drop i).take len

def isBinaryChars (s : List Char) : Prop :=
  ∀ (c : Char), c ∈ s → c = '0' ∨ c = '1'

def onesCount (t : List Char) : Nat :=
  t.count '1'

def isSubstringByRange (s : List Char) (t : List Char) : Prop :=
  ∃ (i : Nat) (len : Nat),
    len > 0 ∧ i + len ≤ s.length ∧ t = sliceChars s i len

def isValidCandidate (s : List Char) (k : Nat) (t : List Char) : Prop :=
  isSubstringByRange s t ∧ onesCount t = k

def precondition (s : List Char) (k : Nat) : Prop :=
  isBinaryChars s

def postcondition (s : List Char) (k : Nat) (result : List Char) : Prop :=
  (¬ (∃ (t : List Char), isValidCandidate s k t) ∧ result = []) ∨
  ((∃ (t : List Char), isValidCandidate s k t) ∧
    isValidCandidate s k result ∧
    (∀ (t : List Char), isValidCandidate s k t →
      (result.length < t.length) ∨ (result.length = t.length ∧ result ≤ t)))
end Specs

section Impl
method ShortestSubstringWithKOnes (s : List Char) (k : Nat)
  return (result : List Char)
  require precondition s k
  ensures postcondition s k result
  do
  pure []

end Impl

section TestCases
-- Test case 1: example
-- s = "10010", k = 2 -> shortest valid substring is "1001"
def test1_s : List Char := ['1','0','0','1','0']
def test1_k : Nat := 2
def test1_Expected : List Char := ['1','0','0','1']

-- Test case 2: single-character solution exists
-- s = "00100", k = 1 -> "1"
def test2_s : List Char := ['0','0','1','0','0']
def test2_k : Nat := 1
def test2_Expected : List Char := ['1']

-- Test case 3: k = 0 and zeros exist -> shortest is "0"
def test3_s : List Char := ['0','0','0']
def test3_k : Nat := 0
def test3_Expected : List Char := ['0']

-- Test case 4: k = 0 and no zeros -> no valid non-empty substring
-- Result must be empty
def test4_s : List Char := ['1','1','1']
def test4_k : Nat := 0
def test4_Expected : List Char := []

-- Test case 5: alternating pattern
-- s = "10101", k = 2 -> "101" (length 3)
def test5_s : List Char := ['1','0','1','0','1']
def test5_k : Nat := 2
def test5_Expected : List Char := ['1','0','1']

-- Test case 6: empty input
-- No non-empty substrings exist, so result is empty for any k
def test6_s : List Char := []
def test6_k : Nat := 0
def test6_Expected : List Char := []

-- Test case 7: singleton input, k = 1
-- The whole string is the unique valid candidate
def test7_s : List Char := ['1']
def test7_k : Nat := 1
def test7_Expected : List Char := ['1']

-- Test case 8: k larger than the number of ones -> no solution
def test8_s : List Char := ['0','1','0','1','0']
def test8_k : Nat := 3
def test8_Expected : List Char := []

-- Test case 9: consecutive ones give shortest "11"
def test9_s : List Char := ['0','0','1','1','1','0','0']
def test9_k : Nat := 2
def test9_Expected : List Char := ['1','1']

-- Recommend to validate: empty input, k = 0 behavior, lexicographic tie-breaking
end TestCases
