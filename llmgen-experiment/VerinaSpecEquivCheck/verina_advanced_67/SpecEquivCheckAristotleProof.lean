/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: b53825b2-bac2-4967-848b-a4664577b636

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (s : String) : VerinaSpec.runLengthEncode_precond s ↔ LLMSpec.precondition s

- theorem postcondition_equiv (s : String) (result : List (Char × Nat)) : LLMSpec.precondition s →
  (VerinaSpec.runLengthEncode_postcond s result ↔ LLMSpec.postcondition s result)
-/

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

theorem precondition_equiv (s : String) : VerinaSpec.runLengthEncode_precond s ↔ LLMSpec.precondition s := by
  -- Since both preconditions are True, their equivalence is trivial.
  simp [VerinaSpec.runLengthEncode_precond, LLMSpec.precondition]

theorem postcondition_equiv (s : String) (result : List (Char × Nat)) : LLMSpec.precondition s →
  (VerinaSpec.runLengthEncode_postcond s result ↔ LLMSpec.postcondition s result) := by
  unfold LLMSpec.precondition LLMSpec.postcondition VerinaSpec.runLengthEncode_postcond;
  -- By definition of `decodeRLE`, we know that `decodeRLE result = s` if and only if `decodeRLE result = chars s`.
  have h_decode_eq : VerinaSpec.decodeRLE result = s ↔ LLMSpec.decodeRLE result = LLMSpec.chars s := by
    -- By definition of `String.data`, we know that `String.data (decodeRLE result) = decodeRLE result`.
    have h_data : ∀ (l : List (Char × ℕ)), String.data (VerinaSpec.decodeRLE l) = LLMSpec.decodeRLE l := by
      intro l;
      induction l <;> simp_all +decide [ VerinaSpec.decodeRLE, LLMSpec.decodeRLE ];
      unfold LLMSpec.addRun; aesop;
    rw [ ← h_data, String.ext_iff ];
    rfl;
  -- By combining the results from h_decode_eq and the definitions of the postconditions, we can conclude the equivalence.
  simp [h_decode_eq, LLMSpec.allRunLengthsPositive, LLMSpec.adjacentCharsDifferent];
  grind +ring

end Proof