import Velvet.Std
import Extensions.Tactics
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic

namespace Generated.ShouldAcceptTerm

set_option maxHeartbeats 10000000
set_option pp.coercions false
set_option pp.funBinderTypes true
set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

/- Problem Description

Implement the term-validation rule used when a node receives a leadership
claim: a claim is only accepted if it comes from a strictly newer election
term, which prevents stale leaders from reasserting authority.

Input:
- currentTerm (Nat): the receiving node's current term number.
- proposedTerm (Nat): the term number carried by the incoming leadership claim.

Output:
- Bool: return true if and only if proposedTerm > currentTerm (strictly
  greater). Equal terms and older terms must be rejected (return false).

Preconditions: none beyond the types; both terms may be 0.

Edge cases:
- Equal terms return false.
- proposedTerm = 0 with currentTerm = 0 returns false.
- Any proposedTerm strictly greater than currentTerm returns true, regardless
  of the gap size.

Determinism: the function is pure; identical inputs always produce identical
outputs.
-/

section Specs
def precondition (currentTerm : Nat) (proposedTerm : Nat) : Prop :=
  True

def postcondition (currentTerm : Nat) (proposedTerm : Nat) (result : Bool) : Prop :=
  result = true ↔ proposedTerm > currentTerm
end Specs

section Impl
method shouldAcceptTerm (currentTerm : Nat) (proposedTerm : Nat)
  return (result : Bool)
  require precondition currentTerm proposedTerm
  ensures postcondition currentTerm proposedTerm result
do
  if proposedTerm > currentTerm then
    return true
  else
    return false
end Impl

section TestCases
-- Test 1: proposedTerm strictly greater than currentTerm (accept)
def test1_currentTerm : Nat := 3
def test1_proposedTerm : Nat := 4
def test1_Expected : Bool := true

-- Test 2: equal terms (reject)
def test2_currentTerm : Nat := 3
def test2_proposedTerm : Nat := 3
def test2_Expected : Bool := false

-- Test 3: proposedTerm older than currentTerm (reject)
def test3_currentTerm : Nat := 5
def test3_proposedTerm : Nat := 2
def test3_Expected : Bool := false

-- Test 4: both terms zero (reject)
def test4_currentTerm : Nat := 0
def test4_proposedTerm : Nat := 0
def test4_Expected : Bool := false

-- Test 5: large gap, proposedTerm strictly greater (accept)
def test5_currentTerm : Nat := 0
def test5_proposedTerm : Nat := 100
def test5_Expected : Bool := true
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((shouldAcceptTerm test1_currentTerm test1_proposedTerm).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((shouldAcceptTerm test2_currentTerm test2_proposedTerm).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((shouldAcceptTerm test3_currentTerm test3_proposedTerm).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((shouldAcceptTerm test4_currentTerm test4_proposedTerm).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((shouldAcceptTerm test5_currentTerm test5_proposedTerm).run), DivM.res test5_Expected ]
end Assertions

section Pbt
velvet_plausible_test shouldAcceptTerm (config := { maxMs := some 20000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000


prove_correct shouldAcceptTerm by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at * <;> expose_names); try (conv => congr <;> simp) ; try rfl; try expose_names)
end Proof
end Generated.ShouldAcceptTerm
