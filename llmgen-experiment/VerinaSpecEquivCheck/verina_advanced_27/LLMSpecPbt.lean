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
    LongestCommonSubsequence: compute a longest common subsequence (LCS) of two input strings.
    **Important: complexity should be O(n*m)**
    Natural language breakdown:
    1. The inputs are two finite sequences of characters (strings).
    2. A sequence r is a subsequence of a sequence s if r can be obtained by deleting zero or more characters from s without changing the order of the remaining characters.
    3. The output r must be a subsequence of the first input.
    4. The output r must be a subsequence of the second input.
    5. The output r must be as long as possible among all sequences that are subsequences of both inputs.
    6. If multiple different longest common subsequences exist, returning any one of them is acceptable.
    7. Empty inputs are allowed, and then the empty string is a valid common subsequence.
-/

section Specs
-- Helper definitions

-- `isSubseqList r s` means `r` is a subsequence of `s`.
-- It is witnessed by an order-preserving index mapping from positions of `r` to positions of `s`.
-- We use natural-number indexing via `List.get!` (safe because we require the indices are in range).
--
-- Note: This definition avoids depending on any particular library name for subsequence.
-- It also avoids mixing `Array` and `List` in specifications; we specify everything over `List Char`.
def isSubseqList (r : List Char) (s : List Char) : Prop :=
  ∃ f : Nat → Nat,
    (∀ (i : Nat), i < r.length → f i < s.length) ∧
    (∀ (i : Nat) (j : Nat), i < j → j < r.length → f i < f j) ∧
    (∀ (i : Nat), i < r.length → r.get! i = s.get! (f i))

def isCommonSubseqList (s1 : List Char) (s2 : List Char) (r : List Char) : Prop :=
  isSubseqList r s1 ∧ isSubseqList r s2

-- `r` is a longest common subsequence iff it is a common subsequence and
-- no other common subsequence is longer.
def isLCSList (s1 : List Char) (s2 : List Char) (r : List Char) : Prop :=
  isCommonSubseqList s1 s2 r ∧
  ∀ (t : List Char), isSubseqList t s1 → isSubseqList t s2 → t.length ≤ r.length

-- No input restrictions.
def precondition (s1 : String) (s2 : String) : Prop :=
  True

def postcondition (s1 : String) (s2 : String) (result : String) : Prop :=
  isLCSList s1.data s2.data result.data
end Specs

section Impl
method LongestCommonSubsequence (s1 : String) (s2 : String)
  return (result : String)
  require precondition s1 s2
  ensures postcondition s1 s2 result
  do
  -- Placeholder implementation only.
  pure ""

prove_correct LongestCommonSubsequence by sorry
end Impl

section TestCases
-- Test case 1: typical case with a non-trivial LCS
-- s1 = "abcdaf", s2 = "acbcf"; one LCS is "abcf".
def test1_s1 : String := "abcdaf"
def test1_s2 : String := "acbcf"
def test1_Expected : String := "abcf"

-- Test case 2: both inputs empty

def test2_s1 : String := ""
def test2_s2 : String := ""
def test2_Expected : String := ""

-- Test case 3: first empty, second non-empty

def test3_s1 : String := ""
def test3_s2 : String := "xyz"
def test3_Expected : String := ""

-- Test case 4: second empty, first non-empty

def test4_s1 : String := "pq"
def test4_s2 : String := ""
def test4_Expected : String := ""

-- Test case 5: identical inputs (entire string is an LCS)

def test5_s1 : String := "lean"
def test5_s2 : String := "lean"
def test5_Expected : String := "lean"

-- Test case 6: no common characters

def test6_s1 : String := "abc"
def test6_s2 : String := "xyz"
def test6_Expected : String := ""

-- Test case 7: repeated characters (LCS uses multiplicity)

def test7_s1 : String := "aaa"
def test7_s2 : String := "aa"
def test7_Expected : String := "aa"

-- Test case 8: singleton strings

def test8_s1 : String := "a"
def test8_s2 : String := "a"
def test8_Expected : String := "a"

-- Test case 9: classic textbook example
-- s1 = "AGGTAB", s2 = "GXTXAYB"; one LCS is "GTAB".

def test9_s1 : String := "AGGTAB"
def test9_s2 : String := "GXTXAYB"
def test9_Expected : String := "GTAB"

-- Recommend to validate: empty inputs, disjoint alphabets, repeated characters
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test9' (result : String) :
  result ≠ test9_Expected →
  ¬ postcondition test9_s1 test9_s2 result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test9_Expected]) (config := { numInst := 100000 })
