import Velvet.Std
import Extensions.Tactics
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic

set_option maxHeartbeats 10000000
set_option pp.coercions false
set_option pp.funBinderTypes true
set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

/- Problem Description
Implement a pure function that counts how many votes a given candidate received
in an election round.

Input:
- votes : List Nat — each element is the node ID the voter voted for; the same
  ID may appear multiple times (duplicates allowed). The list may be empty.
- candidate : Nat — the candidate ID to count votes for.

Output:
- A Nat equal to the number of elements in the votes list that equal the
  candidate ID.

Preconditions: none beyond the types; the votes list may be empty and may
contain duplicates.

Edge cases:
- Empty votes list returns 0.
- Candidate not present in the list returns 0.
- All votes for the candidate returns the list length.

Determinism: the function is pure; identical inputs always produce identical
outputs.
-/

section Specs

def countOccurrences (votes : List Nat) (candidate : Nat) : Nat :=
  votes.count candidate

def precondition (votes : List Nat) (candidate : Nat) : Prop :=
  True

def postcondition (votes : List Nat) (candidate : Nat) (result : Nat) : Prop :=
  result = countOccurrences votes candidate

end Specs

section Impl

method countVotesForCandidate (votes : List Nat) (candidate : Nat)
    return (result : Nat)
  require precondition votes candidate
  ensures postcondition votes candidate result
  do
    return 0

prove_correct countVotesForCandidate by sorry

end Impl

section TestCases

-- Test 1: representative case with duplicates and other candidates mixed in
def test1_votes : List Nat := [1, 2, 1, 3, 1]
def test1_candidate : Nat := 1
def test1_Expected : Nat := 3

-- Test 2: edge case — empty votes list returns 0
def test2_votes : List Nat := []
def test2_candidate : Nat := 5
def test2_Expected : Nat := 0

-- Test 3: edge case — candidate not present in the list returns 0
def test3_votes : List Nat := [2, 3, 4]
def test3_candidate : Nat := 5
def test3_Expected : Nat := 0

-- Test 4: edge case — all votes for the candidate returns the list length
def test4_votes : List Nat := [7, 7, 7]
def test4_candidate : Nat := 7
def test4_Expected : Nat := 3

-- Test 5: boundary case — candidate ID 0
def test5_votes : List Nat := [0, 1, 0]
def test5_candidate : Nat := 0
def test5_Expected : Nat := 2

end TestCases
