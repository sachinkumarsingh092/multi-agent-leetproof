import Velvet.Std
import Extensions.Tactics
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic

namespace Generated.HasMajority

set_option maxHeartbeats 10000000
set_option pp.coercions false
set_option pp.funBinderTypes true
set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

/- Problem Description
Implement the quorum check for leader election: a candidate wins only with a
strict majority of the total cluster size.

Input:
- voteCount (Nat): the number of votes the candidate received.
- totalNodes (Nat): the total number of nodes in the cluster.

Output:
- Bool: return true if and only if 2 * voteCount > totalNodes (strict majority).
  This must be computed with natural-number arithmetic; do not use division that
  could truncate incorrectly.

Preconditions:
- voteCount <= totalNodes.
- totalNodes may be 0, in which case the result must be false
  (note: with voteCount <= totalNodes, totalNodes = 0 forces voteCount = 0,
  and 2 * 0 > 0 is false, so this follows from the strict-majority condition).

Edge cases:
- totalNodes = 0 returns false.
- An exact half (e.g., 2 of 4) is NOT a majority and returns false.
- 3 of 5 returns true.
- 1 of 1 returns true.

Determinism: the function is pure; identical inputs always produce identical
outputs.
-/

section Specs
def isStrictMajority (voteCount : Nat) (totalNodes : Nat) : Prop :=
  2 * voteCount > totalNodes

def precondition (voteCount : Nat) (totalNodes : Nat) : Prop :=
  voteCount ≤ totalNodes

def postcondition (voteCount : Nat) (totalNodes : Nat) (result : Bool) : Prop :=
  result = true ↔ isStrictMajority voteCount totalNodes
end Specs

section Impl
method hasMajority (voteCount : Nat) (totalNodes : Nat) return (result : Bool)
  require precondition voteCount totalNodes
  ensures postcondition voteCount totalNodes result
do
  if 2 * voteCount > totalNodes then
    return true
  else
    return false
end Impl

section TestCases
-- Test 1: representative true case, 3 of 5 is a strict majority
def test1_voteCount : Nat := 3
def test1_totalNodes : Nat := 5
def test1_Expected : Bool := true

-- Test 2: exact half is NOT a majority, 2 of 4
def test2_voteCount : Nat := 2
def test2_totalNodes : Nat := 4
def test2_Expected : Bool := false

-- Test 3: edge case, totalNodes = 0 returns false
def test3_voteCount : Nat := 0
def test3_totalNodes : Nat := 0
def test3_Expected : Bool := false

-- Test 4: edge case, 1 of 1 is a strict majority
def test4_voteCount : Nat := 1
def test4_totalNodes : Nat := 1
def test4_Expected : Bool := true

-- Test 5: below half, 2 of 5
def test5_voteCount : Nat := 2
def test5_totalNodes : Nat := 5
def test5_Expected : Bool := false

-- Test 6: representative true case, 5 of 9
def test6_voteCount : Nat := 5
def test6_totalNodes : Nat := 9
def test6_Expected : Bool := true
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((hasMajority test1_voteCount test1_totalNodes).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((hasMajority test2_voteCount test2_totalNodes).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((hasMajority test3_voteCount test3_totalNodes).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((hasMajority test4_voteCount test4_totalNodes).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((hasMajority test5_voteCount test5_totalNodes).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((hasMajority test6_voteCount test6_totalNodes).run), DivM.res test6_Expected ]
end Assertions

section Pbt
velvet_plausible_test hasMajority (config := { maxMs := some 20000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000


prove_correct hasMajority by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at * <;> expose_names); try (conv => congr <;> simp) ; try rfl; try expose_names)
end Proof
end Generated.HasMajority
