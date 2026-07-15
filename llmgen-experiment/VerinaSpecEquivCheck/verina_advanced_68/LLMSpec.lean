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
    RunLengthEncode: Run-Length Encoding (RLE) for a string of non-digit characters.
    Natural language breakdown:
    1. The input is a string of characters, and digit characters are not allowed in the input.
    2. The output is an encoded string formed from (character, digit) pairs.
    3. The output strictly alternates between a non-digit character and a digit character.
    4. Each pair (c, d) represents a run of character c repeated n times, where n is the numeric value of digit d.
    5. The encoded runs are maximal: adjacent run characters differ, and run boundaries correspond to changes in the input.
    6. Decoding the output by expanding each run reconstructs exactly the original input.
    7. The output is non-empty if and only if the input is non-empty.
    8. Because counts are represented by a single digit, inputs containing a run of length ≥ 10 are excluded by the precondition.
-/

section Specs
-- Helper: a character is a digit iff Char.isDigit returns true.
def isDigit (c : Char) : Bool :=
  c.isDigit

-- Helper: interpret a digit character as a Nat in [0, 9] when the character is a digit.
-- (When c is not a digit, this expression still returns some Nat; specs guard its use with digit checks.)
def digitVal (c : Char) : Nat :=
  c.toNat - ('0').toNat

-- Helper: input contains no digit characters.
def inputHasNoDigits (input : String) : Prop :=
  ∀ (c : Char), c ∈ input.toList → isDigit c = false

-- Helper: input has no run of length ≥ 10.
-- Equivalently: in every window of length 10, some adjacent pair differs.
def noRunLengthGE10 (input : String) : Prop :=
  let inp := input.toList
  ∀ (i : Nat), i + 9 < inp.length → ∃ (t : Nat), t < 9 ∧ inp[i + t]! ≠ inp[i + t + 1]!

-- Helpers for observing an output encoding as pairs at indices 2*j and 2*j+1.
def runChar (out : List Char) (j : Nat) : Char :=
  out[2 * j]!

def runCount (out : List Char) (j : Nat) : Nat :=
  digitVal (out[2 * j + 1]!)

-- Start index in the decoded string for the j-th run (0-based) as a prefix sum of counts.
def runStart (out : List Char) (j : Nat) : Nat :=
  (List.range j).foldl (fun (acc : Nat) (r : Nat) => acc + runCount out r) 0

-- Preconditions
-- 1) input has no digits
-- 2) input has no run longer than 9 (since counts are single digits)
def precondition (input : String) : Prop :=
  inputHasNoDigits input ∧
  noRunLengthGE10 input

-- Postconditions
-- Characterize a valid RLE encoding with single-digit counts.
def postcondition (input : String) (result : String) : Prop :=
  let inp := input.toList
  let out := result.toList
  let k : Nat := out.length / 2
  (out.length % 2 = 0) ∧
  -- Alternation: even indices are non-digits, odd indices are digits with values 1..9.
  (∀ (i : Nat), i < out.length →
      (i % 2 = 0 → isDigit out[i]! = false) ∧
      (i % 2 = 1 → isDigit out[i]! = true ∧ 1 ≤ digitVal out[i]! ∧ digitVal out[i]! ≤ 9)) ∧
  -- Runs are maximal: adjacent run characters differ.
  (∀ (j : Nat), j + 1 < k → runChar out j ≠ runChar out (j + 1)) ∧
  -- Total decoded length equals input length (sum of counts).
  (runStart out k = inp.length) ∧
  -- Decoding correctness: each run expands to the corresponding segment of the input,
  -- and boundaries in the input match run boundaries.
  (∀ (j : Nat), j < k →
      let s := runStart out j
      let n := runCount out j
      (s + n ≤ inp.length) ∧
      (∀ (t : Nat), t < n → inp[s + t]! = runChar out j) ∧
      (j + 1 < k → inp[s + n]! ≠ runChar out j)) ∧
  -- Non-emptiness equivalence.
  (result = "" ↔ input = "")
end Specs

section Impl
method RunLengthEncode (input : String)
  return (result : String)
  require precondition input
  ensures postcondition input result
  do
  pure ""  -- placeholder

end Impl

section TestCases
-- Test case 1: example from description: "aaabb" -> "a3b2"
def test1_input : String := "aaabb"
def test1_Expected : String := "a3b2"

-- Test case 2: empty input -> empty output
-- (Valid: no digits, and no long run)
def test2_input : String := ""
def test2_Expected : String := ""

-- Test case 3: singleton run length 1
def test3_input : String := "x"
def test3_Expected : String := "x1"

-- Test case 4: two different chars, both runs length 1
def test4_input : String := "ab"
def test4_Expected : String := "a1b1"

-- Test case 5: long run at the single-digit boundary (9)
def test5_input : String := "zzzzzzzzz"
def test5_Expected : String := "z9"

-- Test case 6: multiple runs with varying lengths
def test6_input : String := "aabcccd"
def test6_Expected : String := "a2b1c3d1"

-- Test case 7: alternating characters (all runs length 1)
def test7_input : String := "pqpqp"
def test7_Expected : String := "p1q1p1q1p1"

-- Test case 8: includes non-alphanumeric non-digit characters
def test8_input : String := "!!?"
def test8_Expected : String := "!2?1"

-- Test case 9: multiple separated runs of same character (allowed, but not adjacent)
def test9_input : String := "aabbaaa"
def test9_Expected : String := "a2b2a3"

-- Recommend to validate: empty input, boundary run length 9, mixed punctuation
end TestCases
