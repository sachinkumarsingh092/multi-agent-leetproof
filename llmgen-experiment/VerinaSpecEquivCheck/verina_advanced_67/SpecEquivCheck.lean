import Mathlib.Tactic

namespace VerinaSpec


def runLengthEncode_precond (s : String) : Prop :=
  True

def decodeRLE (lst : List (Char × Nat)) : String :=
  match lst with
  | [] => ""
  | (ch, cnt) :: tail =>
    let repeated := String.mk (List.replicate cnt ch)
    repeated ++ decodeRLE tail

def runLengthEncode_postcond (s : String) (result: List (Char × Nat)) : Prop :=
  (∀ pair ∈ result, pair.snd > 0) ∧
  (∀ i : Nat, i < result.length - 1 → (result[i]!).fst ≠ (result[i+1]!).fst) ∧
  decodeRLE result = s

end VerinaSpec

namespace LLMSpec

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

end LLMSpec

section Proof

theorem precondition_equiv (s : String) :
  VerinaSpec.runLengthEncode_precond s ↔ LLMSpec.precondition s := by
  sorry

theorem postcondition_equiv (s : String) (result: List (Char × Nat)) :
  LLMSpec.precondition s →
  (VerinaSpec.runLengthEncode_postcond s result ↔ LLMSpec.postcondition s result) := by
  sorry

end Proof
