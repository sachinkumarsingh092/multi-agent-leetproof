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
    PalindromeChars: Determine whether a given list of characters is a palindrome.
    Natural language breakdown:
    1. Input x is a List Char and may be empty or non-empty.
    2. The output is a Bool.
    3. The output is true exactly when x reads the same forwards and backwards.
    4. Being a palindrome means x equals its reversal.
    5. The empty list is considered a palindrome.
    6. There are no additional preconditions on x.
-/

section Specs
-- Helper predicate: x is a palindrome iff it equals its reverse.
-- We keep this as a Prop so it can be used in a logical postcondition.
def IsPalindrome (x : List Char) : Prop :=
  x.reverse = x

def precondition (x : List Char) : Prop :=
  True

def postcondition (x : List Char) (result : Bool) : Prop :=
  (result = true ↔ IsPalindrome x)
end Specs

section Impl
method PalindromeChars (x : List Char)
  return (result : Bool)
  require precondition x
  ensures postcondition x result
  do
  pure true

prove_correct PalindromeChars by sorry
end Impl

section TestCases
-- Test case 1: empty list is a palindrome
-- (Problem note: empty list is considered a palindrome.)
def test1_x : List Char := []
def test1_Expected : Bool := true

-- Test case 2: singleton list is a palindrome

def test2_x : List Char := ['a']
def test2_Expected : Bool := true

-- Test case 3: two equal characters is a palindrome

def test3_x : List Char := ['z', 'z']
def test3_Expected : Bool := true

-- Test case 4: two different characters is not a palindrome

def test4_x : List Char := ['a', 'b']
def test4_Expected : Bool := false

-- Test case 5: odd length palindrome

def test5_x : List Char := ['r', 'a', 'r']
def test5_Expected : Bool := true

-- Test case 6: even length palindrome

def test6_x : List Char := ['n', 'o', 'o', 'n']
def test6_Expected : Bool := true

-- Test case 7: typical non-palindrome

def test7_x : List Char := ['h', 'e', 'l', 'l', 'o']
def test7_Expected : Bool := false

-- Test case 8: longer palindrome with repeated characters

def test8_x : List Char := ['a', 'b', 'c', 'b', 'a']
def test8_Expected : Bool := true

-- Test case 9: longer non-palindrome with matching ends but mismatch inside

def test9_x : List Char := ['a', 'b', 'c', 'a']
def test9_Expected : Bool := false
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test9' (result : Bool) :
  result ≠ test9_Expected →
  ¬ postcondition test9_x result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test9_Expected]) (config := { numInst := 100000 })
