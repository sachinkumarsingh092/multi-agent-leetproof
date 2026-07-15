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
    ChordIntersections: Determine whether any pair of chords on a circle intersects.

    Natural language breakdown:
    1. The circle has 2*N labeled points in clockwise order, labeled 1..2*N.
    2. Each chord connects two distinct labeled points.
    3. The input provides N chords as a list of length N, where each chord is given by a list of exactly two endpoints.
    4. All endpoints appearing across all chords are distinct and are within the range 1..2*N.
    5. For two chords with endpoints {a,b} and {c,d}, normalize each so that a<b and c<d.
    6. The chords intersect inside the circle exactly when their endpoints alternate around the circle, i.e.
       (a < c ∧ c < b ∧ b < d) or (c < a ∧ a < d ∧ d < b).
    7. The method returns true iff there exists at least one pair of distinct chords that intersect.

    Constraints:
    - 2 ≤ N ≤ 2×10^5
    - 1 ≤ endpoints ≤ 2N
    - All endpoints across all chords are distinct
-/

section Specs
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
end Specs

section Impl
method ChordIntersections (N : Nat) (chords : List (List Nat))
  return (result : Bool)
  require precondition N chords
  ensures postcondition N chords result
  do
  pure false  -- placeholder

end Impl

section TestCases
-- Test case 1: N=2, disjoint chords (no intersection)
def test1_N : Nat := 2

def test1_chords : List (List Nat) := [[1, 2], [3, 4]]

def test1_Expected : Bool := false

-- Test case 2: N=2, crossing chords (intersection)
def test2_N : Nat := 2

def test2_chords : List (List Nat) := [[1, 3], [2, 4]]

def test2_Expected : Bool := true

-- Test case 3: N=2, nested chords (no intersection)
def test3_N : Nat := 2

def test3_chords : List (List Nat) := [[1, 4], [2, 3]]

def test3_Expected : Bool := false

-- Test case 4: N=3, simple intersection exists (1,4) intersects (2,5)
def test4_N : Nat := 3

def test4_chords : List (List Nat) := [[1, 4], [2, 5], [3, 6]]

def test4_Expected : Bool := true

-- Test case 5: N=3, fully non-intersecting (one outer chord with two disjoint inner chords)
def test5_N : Nat := 3

def test5_chords : List (List Nat) := [[1, 6], [2, 3], [4, 5]]

def test5_Expected : Bool := false

-- Test case 6: N=4, many intersections (ladder pattern)
def test6_N : Nat := 4

def test6_chords : List (List Nat) := [[1, 5], [2, 6], [3, 7], [4, 8]]

def test6_Expected : Bool := true

-- Test case 7: N=3, all chords are adjacent pairs (no intersection)
def test7_N : Nat := 3

def test7_chords : List (List Nat) := [[1, 2], [3, 4], [5, 6]]

def test7_Expected : Bool := false

-- Test case 8: N=4, all chords are adjacent pairs (no intersection)
def test8_N : Nat := 4

def test8_chords : List (List Nat) := [[1, 2], [3, 4], [5, 6], [7, 8]]

def test8_Expected : Bool := false

-- Test case 9: N=4, intersection between interior chords under an outer chord
-- (2,5) intersects (4,7)
def test9_N : Nat := 4

def test9_chords : List (List Nat) := [[1, 8], [2, 5], [3, 6], [4, 7]]

def test9_Expected : Bool := true

-- Recommend to validate: precondition_satisfiable, intersection_alternation_logic, endpoint_distinctness
end TestCases
