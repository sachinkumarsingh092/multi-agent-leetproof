import Velvet.Std
import Extensions.Tactics
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic

namespace Generated.CountVotesForCandidate

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
    let arr : Array Nat := votes.toArray
    let mut count := 0
    let mut i := 0
    while i < arr.size
      -- Invariant 1: i stays within bounds; holds at entry (i = 0) and preserved by i := i + 1
      invariant "i_bounds" i ≤ arr.size
      -- Invariant 2: count equals occurrences of candidate in the processed prefix of votes;
      -- at entry take 0 gives [], count = 0; each step extends prefix by one element,
      -- incrementing count exactly when arr[i]! = candidate; at exit i = arr.size = votes.length,
      -- so count = votes.count candidate, giving the postcondition
      invariant "count_prefix" count = (votes.take i).count candidate
      -- Decreasing: distance to the loop bound, decreases since i increases each iteration
      decreasing arr.size - i
    do
      if arr[i]! = candidate then
        count := count + 1
      i := i + 1
    return count
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

section Assertions
-- Test case 1

#assert_same_evaluation #[((countVotesForCandidate test1_votes test1_candidate).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((countVotesForCandidate test2_votes test2_candidate).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((countVotesForCandidate test3_votes test3_candidate).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((countVotesForCandidate test4_votes test4_candidate).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((countVotesForCandidate test5_votes test5_candidate).run), DivM.res test5_Expected ]
end Assertions

section Pbt
-- Integration omitted this command: PBT passed before namespacing.
-- velvet_plausible_test countVotesForCandidate (config := { maxMs := some 20000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000

theorem goal_0
    (votes : List ℕ)
    (i : ℕ)
    (if_pos : i < votes.length)
    : List.count (votes[i]?.getD (OfNat.ofNat 0)) (List.take i votes) + OfNat.ofNat 1 = List.count (votes[i]?.getD (OfNat.ofNat 0)) (List.take (i + OfNat.ofNat 1) votes) := by
  have h : votes[i]? = some votes[i] := List.getElem?_eq_getElem if_pos
  rw [h]
  show List.count votes[i] (List.take i votes) + 1 = List.count votes[i] (List.take (i + 1) votes)
  rw [List.take_succ, h, List.count_append]
  simp

theorem goal_1
    (votes : List ℕ)
    (candidate : ℕ)
    (i : ℕ)
    (if_pos : i < votes.length)
    (if_neg : ¬votes[i]?.getD (OfNat.ofNat 0) = candidate)
    : List.count candidate (List.take i votes) = List.count candidate (List.take (i + OfNat.ofNat 1) votes) := by
  have h : votes[i]? = some votes[i] := List.getElem?_eq_getElem if_pos
  rw [h] at if_neg
  simp at if_neg
  rw [List.take_succ, h, List.count_append]
  simp [List.count_singleton, if_neg]


prove_correct countVotesForCandidate by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at * <;> expose_names); try (conv => congr <;> simp) ; try rfl; try expose_names)
  exact (goal_0 votes i if_pos)
  exact (goal_1 votes candidate i if_pos if_neg)
end Proof
end Generated.CountVotesForCandidate
