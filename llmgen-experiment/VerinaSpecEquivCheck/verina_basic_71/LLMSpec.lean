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
    LongestCommonPrefix: compute the longest common prefix of two lists of characters.

    Natural language breakdown:
    1. Inputs are two lists of characters, str1 and str2.
    2. The result is a list of characters.
    3. The result must be a prefix of str1.
    4. The result must be a prefix of str2.
    5. Among all lists that are prefixes of both str1 and str2, the result has maximal length.
    6. If either input list is empty, the longest common prefix is the empty list.
    7. If the first characters differ, the longest common prefix is the empty list.
-/

section Specs
-- We use Mathlib/Lean's propositional prefix relation `p <+: s`.
-- `p <+: s` means: there exists some suffix t such that p ++ t = s.

-- No input restrictions.
def precondition (str1 : List Char) (str2 : List Char) : Prop :=
  True

-- Postcondition: `result` is a common prefix and is longest by length.
def postcondition (str1 : List Char) (str2 : List Char) (result : List Char) : Prop :=
  (result <+: str1) ∧
  (result <+: str2) ∧
  (∀ (p : List Char), (p <+: str1) → (p <+: str2) → p.length ≤ result.length)
end Specs

section Impl
method LongestCommonPrefix (str1 : List Char) (str2 : List Char)
  return (result : List Char)
  require precondition str1 str2
  ensures postcondition str1 str2 result
  do
  pure ([] : List Char)  -- placeholder

end Impl

section TestCases
-- Test case 1: both empty
-- Expected longest common prefix: []
def test1_str1 : List Char := []
def test1_str2 : List Char := []
def test1_Expected : List Char := []

-- Test case 2: first empty, second non-empty
-- Expected: []
def test2_str1 : List Char := []
def test2_str2 : List Char := ['a', 'b']
def test2_Expected : List Char := []

-- Test case 3: first non-empty, second empty
-- Expected: []
def test3_str1 : List Char := ['x']
def test3_str2 : List Char := []
def test3_Expected : List Char := []

-- Test case 4: first characters differ
-- Expected: []
def test4_str1 : List Char := ['a', 'b', 'c']
def test4_str2 : List Char := ['z', 'b', 'c']
def test4_Expected : List Char := []

-- Test case 5: identical lists
-- Expected: the full list
def test5_str1 : List Char := ['a', 'b', 'c']
def test5_str2 : List Char := ['a', 'b', 'c']
def test5_Expected : List Char := ['a', 'b', 'c']

-- Test case 6: one list is a strict prefix of the other
-- Expected: the shorter list
def test6_str1 : List Char := ['a', 'b']
def test6_str2 : List Char := ['a', 'b', 'c', 'd']
def test6_Expected : List Char := ['a', 'b']

-- Test case 7: common prefix then divergence
-- Expected: prefix up to the first mismatch
def test7_str1 : List Char := ['a', 'b', 'x', 'y']
def test7_str2 : List Char := ['a', 'b', 'z']
def test7_Expected : List Char := ['a', 'b']

-- Test case 8: common prefix of length 1
-- Expected: ['q']
def test8_str1 : List Char := ['q', 'r', 's']
def test8_str2 : List Char := ['q']
def test8_Expected : List Char := ['q']

-- Test case 9: no common prefix due to singletons mismatch
-- Expected: []
def test9_str1 : List Char := ['a']
def test9_str2 : List Char := ['b']
def test9_Expected : List Char := []
end TestCases
