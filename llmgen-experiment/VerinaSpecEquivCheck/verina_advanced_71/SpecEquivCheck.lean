import Mathlib.Tactic

namespace VerinaSpec


def countOnes (lst : List Char) : Nat :=
  lst.foldl (fun acc c => if c = '1' then acc + 1 else acc) 0

def shortestBeautifulSubstring_precond (s : String) (k : Nat) : Prop :=
  s.toList.all (fun c => c = '0' ∨ c = '1')

def listToString (lst : List Char) : String :=
  String.mk lst

def isLexSmaller (a b : List Char) : Bool :=
  listToString a < listToString b

def allSubstrings (s : List Char) : List (List Char) :=
  let n := s.length
  (List.range n).flatMap (fun i =>
    (List.range (n - i)).map (fun j =>
      s.drop i |>.take (j + 1)))

#eval allSubstrings "11011".toList

def shortestBeautifulSubstring_postcond (s : String) (k : Nat) (result: String) : Prop :=
  let chars := s.data
  let substrings := (List.range chars.length).flatMap (fun i =>
    (List.range (chars.length - i + 1)).map (fun len =>
      chars.drop i |>.take len))
  let isBeautiful := fun sub => countOnes sub = k
  let beautiful := substrings.filter (fun sub => isBeautiful sub)
  let targets := beautiful.map (·.asString) |>.filter (fun s => s ≠ "")
  (result = "" ∧ targets = []) ∨
  (result ∈ targets ∧
   ∀ r ∈ targets, r.length ≥ result.length ∨ (r.length = result.length ∧ result ≤ r))

theorem test0 :
  shortestBeautifulSubstring_postcond "11011" 3 "1101" := by
  simp [shortestBeautifulSubstring_postcond]
  apply And.intro
  · use ['1', '1', '0', '1']
    simp +decide
  · intros; expose_names



end VerinaSpec

namespace LLMSpec

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

theorem test0 :
  postcondition "11011".toList 3 "11011".toList := by
  simp [postcondition]
  sorry

end LLMSpec

section Proof

theorem precondition_equiv (s : String) (k : Nat) :
  VerinaSpec.shortestBeautifulSubstring_precond s k ↔ LLMSpec.precondition s.toList k := by
  sorry

theorem postcondition_equiv (s : String) (k : Nat) (result: String) :
  LLMSpec.precondition s.toList k →
  (VerinaSpec.shortestBeautifulSubstring_postcond s k result ↔ LLMSpec.postcondition s.toList k result.toList) := by
  sorry



end Proof
