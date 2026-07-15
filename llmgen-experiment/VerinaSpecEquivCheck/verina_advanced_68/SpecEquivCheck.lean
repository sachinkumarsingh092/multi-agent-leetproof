import Mathlib.Tactic

namespace VerinaSpec


def runLengthEncoder_precond (input : String) : Prop :=
  input.all (fun c => ¬c.isDigit)  -- no digits allowed in input (ambiguous encoding)

def runLengthEncoder_postcond (input : String) (result: String) : Prop :=
  let chars : String → List Char := fun s => s.data
  let parseEncodedString : String → List (Char × Nat) :=
    let rec parseState : List Char → Option Char → Option Nat → List (Char × Nat) → List (Char × Nat) :=
      fun remaining currentChar currentCount acc =>
        match remaining with
        | [] =>
          match currentChar, currentCount with
          | some c, some n => (c, n) :: acc
          | _, _ => acc
        | c :: cs =>
          if c.isDigit then
            match currentChar with
            | none => [] -- Invalid format: digit without preceding character
            | some ch =>
              let digit := c.toNat - 48
              let newCount :=
                match currentCount with
                | none => digit
                | some n => n * 10 + digit
              parseState cs currentChar (some newCount) acc
          else
            let newAcc :=
              match currentChar, currentCount with
              | some ch, some n => (ch, n) :: acc
              | _, _ => acc
            parseState cs (some c) none newAcc
    fun s =>
      let result := parseState (chars s) none none []
      result.reverse
  let formatValid : Bool :=
    let rec checkPairs (chars : List Char) (nowDigit : Bool) : Bool :=
      match chars with
      | [] => true
      | c :: cs =>
        if nowDigit && c.isDigit then
          checkPairs cs true
        else
          match cs with
          | [] => false -- Ending with character, no digits
          | d :: ds =>
            if d.isDigit then
              checkPairs ds true
            else
              false -- No digit after character
    checkPairs (chars result) false
  let contentValid : Bool :=
    let pairs := parseEncodedString result
    let expanded := pairs.flatMap (fun (c, n) => List.replicate n c)
    expanded == chars input
  let nonEmptyValid : Bool :=
    input.isEmpty = result.isEmpty
  formatValid && contentValid && nonEmptyValid

end VerinaSpec

namespace LLMSpec

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

end LLMSpec

section Proof

theorem precondition_equiv (input : String) :
  VerinaSpec.runLengthEncoder_precond input ↔ LLMSpec.precondition input := by
  sorry

theorem postcondition_equiv (input : String) (result: String) :
  LLMSpec.precondition input →
  (VerinaSpec.runLengthEncoder_postcond input result ↔ LLMSpec.postcondition input result) := by
  sorry

end Proof
