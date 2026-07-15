import Mathlib.Tactic

namespace VerinaSpec


def hasChordIntersection_precond (N : Nat) (chords : List (List Nat)) : Prop :=
  N ≥ 2 ∧
  chords.all (fun chord => chord.length = 2 ∧ chord[0]! ≥ 1 ∧ chord[0]! ≤ 2 * N ∧ chord[1]! ≥ 1 ∧ chord[1]! ≤ 2 * N) ∧
  List.Nodup (chords.flatMap id)

def hasChordIntersection_postcond (N : Nat) (chords : List (List Nat)) (result: Bool) : Prop :=
  let sortedChords := chords.map (fun chord =>
    let a := chord[0]!
    let b := chord[1]!
    if a > b then [b, a] else [a, b]
  )
  let rec hasIntersection (chord1 : List Nat) (chord2 : List Nat) : Bool :=
    let a1 := chord1[0]!
    let b1 := chord1[1]!
    let a2 := chord2[0]!
    let b2 := chord2[1]!
    (a1 < a2 && a2 < b1 && b1 < b2) || (a2 < a1 && a1 < b2 && b2 < b1)
  let rec checkAllPairs (chords : List (List Nat)) : Bool :=
    match chords with
    | [] => false
    | x :: xs =>
      if xs.any (fun y => hasIntersection x y) then true
      else checkAllPairs xs
  ((List.Pairwise (fun x y => !hasIntersection x y) sortedChords) → ¬ result) ∧
  ((sortedChords.any (fun x => chords.any (fun y => hasIntersection x y))) → result)

end VerinaSpec

namespace LLMSpec

-- Helper: read endpoints from a chord represented as a list of two Nats.
-- Total even when malformed (uses default 0), but precondition will enforce well-formedness.
def chordA (ch : List Nat) : Nat := ch.getD 0 0

def chordB (ch : List Nat) : Nat := ch.getD 1 0

-- Helper: normalize a chord to (lo, hi) with lo ≤ hi.
def chordLo (ch : List Nat) : Nat := Nat.min (chordA ch) (chordB ch)

def chordHi (ch : List Nat) : Nat := Nat.max (chordA ch) (chordB ch)

-- Predicate: a chord input is well-formed (exactly 2 endpoints, and endpoints are distinct).
-- Note: We use `getD` so this is total; the length constraint ensures the `getD` values are the true endpoints.
def chordWellFormed (ch : List Nat) : Prop :=
  ch.length = 2 ∧ chordA ch ≠ chordB ch

-- Helper: collect all endpoints in a single list.
-- We avoid `List.join` and `List.bind` (not available in this environment) by flattening via `foldr`.
def allEndpoints (chords : List (List Nat)) : List Nat :=
  List.foldr (fun (ch : List Nat) (acc : List Nat) => ch ++ acc) [] chords

-- Predicate: endpoints of all chords are pairwise distinct.
def allEndpointsNodup (chords : List (List Nat)) : Prop :=
  (allEndpoints chords).Nodup

-- Predicate: every endpoint lies within 1..2*N.
def endpointsInRange (N : Nat) (chords : List (List Nat)) : Prop :=
  ∀ (k : Nat), k ∈ allEndpoints chords → (1 ≤ k ∧ k ≤ 2 * N)

-- Predicate: two normalized chords intersect (their endpoints alternate).
def chordsIntersect (ch1 : List Nat) (ch2 : List Nat) : Prop :=
  let a := chordLo ch1
  let b := chordHi ch1
  let c := chordLo ch2
  let d := chordHi ch2
  (a < c ∧ c < b ∧ b < d) ∨ (c < a ∧ a < d ∧ d < b)

-- Predicate: existence of an intersecting pair among the chords.
def hasAnyIntersection (chords : List (List Nat)) : Prop :=
  ∃ (i : Nat) (j : Nat),
    i < j ∧ j < chords.length ∧ chordsIntersect (chords[i]!) (chords[j]!)

-- Preconditions
-- Note: we require:
-- * N is within the given bounds.
-- * chords has length N.
-- * each chord is a 2-element list with distinct endpoints.
-- * all endpoints across all chords are distinct.
-- * endpoints all lie in [1, 2*N].
def precondition (N : Nat) (chords : List (List Nat)) : Prop :=
  2 ≤ N ∧ N ≤ 200000 ∧
  chords.length = N ∧
  (∀ (i : Nat), i < chords.length → chordWellFormed (chords[i]!)) ∧
  allEndpointsNodup chords ∧
  endpointsInRange N chords

-- Postcondition: result is true iff there exists an intersecting pair of chords.
def postcondition (N : Nat) (chords : List (List Nat)) (result : Bool) : Prop :=
  (result = true ↔ hasAnyIntersection chords)

end LLMSpec

section Proof

theorem precondition_equiv (N : Nat) (chords : List (List Nat)) :
  VerinaSpec.hasChordIntersection_precond N chords ↔ LLMSpec.precondition N chords := by
  sorry

theorem postcondition_equiv (N : Nat) (chords : List (List Nat)) (result: Bool) :
  LLMSpec.precondition N chords →
  (VerinaSpec.hasChordIntersection_postcond N chords result ↔ LLMSpec.postcondition N chords result) := by
  sorry

end Proof
