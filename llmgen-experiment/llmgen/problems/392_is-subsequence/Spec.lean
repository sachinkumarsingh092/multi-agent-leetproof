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
    392. Is Subsequence: decide whether s is a subsequence of t.
    **Important: complexity should be O(n) time and O(1) space**
    Natural language breakdown:
    1. Inputs are two sequences of characters s and t.
    2. s is a subsequence of t if we can delete zero or more characters from t and obtain exactly s.
    3. Deletions may be none; the relative order of the remaining characters must be preserved.
    4. The output is true exactly when s is a subsequence of t, and false otherwise.
    5. The empty sequence is a subsequence of any sequence.
    6. If s is longer than t, then s cannot be a subsequence of t.
-/

section Specs
-- We define the subsequence relation via an order-preserving index embedding.
-- This avoids relying on a particular library name for subsequence.
--
-- `subseqByIndex s t` means: there exists a (partial) index map f from indices of `s`
-- into indices of `t` such that:
--  * f maps valid indices of s to valid indices of t
--  * f is strictly increasing on indices < s.length
--  * each character of s matches the character of t at the mapped index

def subseqByIndex (s : List Char) (t : List Char) : Prop :=
  ∃ f : Nat → Nat,
    (∀ i : Nat, i < s.length → f i < t.length) ∧
    StrictMonoOn f (Set.Iio s.length) ∧
    (∀ i : Nat, i < s.length → s.get! i = t.get! (f i))

def precondition (s : List Char) (t : List Char) : Prop :=
  True

def postcondition (s : List Char) (t : List Char) (result : Bool) : Prop :=
  (result = true ↔ subseqByIndex s t)
end Specs

section Impl
method IsSubsequence (s : List Char) (t : List Char)
  return (result : Bool)
  require precondition s t
  ensures postcondition s t result
  do
  pure false

end Impl

section TestCases
-- Test case 1: Example 1
-- s = "abc", t = "ahbgdc" => true

def test1_s : List Char := ['a', 'b', 'c']
def test1_t : List Char := ['a', 'h', 'b', 'g', 'd', 'c']
def test1_Expected : Bool := true

-- Test case 2: Example 2
-- s = "axc", t = "ahbgdc" => false

def test2_s : List Char := ['a', 'x', 'c']
def test2_t : List Char := ['a', 'h', 'b', 'g', 'd', 'c']
def test2_Expected : Bool := false

-- Test case 3: Empty s is a subsequence of any t

def test3_s : List Char := []
def test3_t : List Char := ['z', 'y']
def test3_Expected : Bool := true

-- Test case 4: Non-empty s cannot be subsequence of empty t

def test4_s : List Char := ['a']
def test4_t : List Char := []
def test4_Expected : Bool := false

-- Test case 5: s equals t

def test5_s : List Char := ['l', 'e', 'a', 'n']
def test5_t : List Char := ['l', 'e', 'a', 'n']
def test5_Expected : Bool := true

-- Test case 6: Single character present later in t

def test6_s : List Char := ['c']
def test6_t : List Char := ['a', 'b', 'c']
def test6_Expected : Bool := true

-- Test case 7: Single character absent from t

def test7_s : List Char := ['x']
def test7_t : List Char := ['a', 'b', 'c']
def test7_Expected : Bool := false

-- Test case 8: Repeated characters succeed when enough occurrences exist
-- s = "aa" is subsequence of "abca" (use positions 0 and 3)

def test8_s : List Char := ['a', 'a']
def test8_t : List Char := ['a', 'b', 'c', 'a']
def test8_Expected : Bool := true

-- Test case 9: Repeated characters fail when not enough occurrences exist

def test9_s : List Char := ['a', 'a', 'a']
def test9_t : List Char := ['a', 'a']
def test9_Expected : Bool := false

-- Recommend to validate: empty-s behavior, repeated-character behavior, order-preservation
end TestCases
