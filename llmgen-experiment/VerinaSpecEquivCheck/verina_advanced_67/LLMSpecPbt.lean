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
    RunLengthEncode: Run-length encode an input string by grouping consecutive identical characters.
    Natural language breakdown:
    1. The input is a finite string of characters, scanned from left to right.
    2. Consecutive identical characters form a run.
    3. The output is a list of pairs (character, runLength) describing each run in order.
    4. Each runLength is a positive natural number (never zero).
    5. Adjacent pairs in the output must not have the same character.
    6. Decoding the output by repeating each character runLength times and concatenating
       must reconstruct exactly the original input string.
-/

section Specs
-- Helper: expose the character sequence of a String once, so specs talk uniformly about `List Char`.
-- Note: `String.data` is the underlying list of characters.
def chars (s : String) : List Char :=
  s.data

-- Decode a run-length encoding back into a list of characters.
-- This is used only as a semantic observation of the output.
def addRun (acc : List Char) (p : Char × Nat) : List Char :=
  acc ++ (List.replicate p.2 p.1)

def decodeRLE (rle : List (Char × Nat)) : List Char :=
  rle.foldl addRun []

-- Adjacent pairs have different characters.
def adjacentCharsDifferent (rle : List (Char × Nat)) : Prop :=
  ∀ (i : Nat), i + 1 < rle.length → (rle.get! i).1 ≠ (rle.get! (i + 1)).1

-- All run lengths are strictly positive.
def allRunLengthsPositive (rle : List (Char × Nat)) : Prop :=
  ∀ (p : Char × Nat), p ∈ rle → 0 < p.2

-- Precondition: no restrictions.
def precondition (s : String) : Prop :=
  True

-- Postcondition: the result is a valid run-length encoding whose decoding equals the input.
def postcondition (s : String) (result : List (Char × Nat)) : Prop :=
  allRunLengthsPositive result ∧
  adjacentCharsDifferent result ∧
  decodeRLE result = chars s
end Specs

section Impl
method RunLengthEncode (s : String)
  return (result : List (Char × Nat))
  require precondition s
  ensures postcondition s result
  do
  pure []

prove_correct RunLengthEncode by sorry
end Impl

section TestCases
-- Test case 1: example "aaabbc" -> [('a',3),('b',2),('c',1)]
def test1_s : String := "aaabbc"
def test1_Expected : List (Char × Nat) := [('a', 3), ('b', 2), ('c', 1)]

-- Test case 2: empty input encodes to empty list

def test2_s : String := ""
def test2_Expected : List (Char × Nat) := []

-- Test case 3: singleton input

def test3_s : String := "x"
def test3_Expected : List (Char × Nat) := [('x', 1)]

-- Test case 4: all characters the same

def test4_s : String := "zzzz"
def test4_Expected : List (Char × Nat) := [('z', 4)]

-- Test case 5: alternating characters (all runs length 1)

def test5_s : String := "ababa"
def test5_Expected : List (Char × Nat) := [('a', 1), ('b', 1), ('a', 1), ('b', 1), ('a', 1)]

-- Test case 6: includes a newline character

def test6_s : String := "\n\na"
def test6_Expected : List (Char × Nat) := [('\n', 2), ('a', 1)]

-- Test case 7: multiple runs with varying lengths

def test7_s : String := "aabcccd"
def test7_Expected : List (Char × Nat) := [('a', 2), ('b', 1), ('c', 3), ('d', 1)]

-- Test case 8: digits as characters

def test8_s : String := "111223333"
def test8_Expected : List (Char × Nat) := [('1', 3), ('2', 2), ('3', 4)]

-- Test case 9: two runs only

def test9_s : String := "aaab"
def test9_Expected : List (Char × Nat) := [('a', 3), ('b', 1)]

-- Recommend to validate: empty input, singleton input, multiple-run mixed characters
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test3' (result : List (Char × Nat)) :
  result ≠ test3_Expected →
  ¬ postcondition test3_s result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test3_Expected]) (config := { numInst := 100000 })
