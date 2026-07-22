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

Successor lookup for a ring-based leader election topology: given the ring
membership and the current node, find the node that election messages should
be forwarded to next.

Input domain:
- ringIds : List Nat — a non-empty list of natural-number node IDs, sorted in
  strictly increasing order (hence duplicate-free).
- currentId : Nat — guaranteed to be an element of ringIds.

Output domain:
- Nat — the smallest ID in ringIds strictly greater than currentId; if
  currentId is the largest ID in the ring, wrap around and return the smallest
  ID in ringIds.

Preconditions (invalid inputs are excluded by the precondition; behavior on
inputs violating the precondition is unconstrained):
- ringIds is non-empty,
- ringIds is strictly increasing (pairwise <, so duplicate-free),
- currentId ∈ ringIds.

Edge cases / boundary behavior:
- A single-node ring returns currentId itself (it wraps to itself).
- currentId equal to the maximum of ringIds wraps to the minimum of ringIds.

Determinism:
- The function is pure; identical inputs always produce identical outputs.

Units: node IDs are unitless natural numbers.
-/

section Specs

-- ringIds is sorted in strictly increasing order (pairwise <).
def strictlyIncreasing (l : List Nat) : Prop :=
  List.Pairwise (· < ·) l

-- All elements of ringIds strictly greater than currentId, in ring order.
-- Since ringIds is strictly increasing, the head of this list (when non-empty)
-- is the smallest ID strictly greater than currentId.
def greaterIds (ringIds : List Nat) (currentId : Nat) : List Nat :=
  ringIds.filter (fun x => decide (currentId < x))

-- Reference specification of the successor in the ring:
-- the smallest ID strictly greater than currentId, or, when no such ID
-- exists (currentId is the maximum), wrap around to the smallest ID in the
-- ring (the head, since ringIds is strictly increasing and non-empty).
def nextInRingSpec (ringIds : List Nat) (currentId : Nat) : Nat :=
  match greaterIds ringIds currentId with
  | [] => ringIds.headD 0
  | y :: _ => y

def precondition (ringIds : List Nat) (currentId : Nat) : Prop :=
  ringIds ≠ [] ∧ strictlyIncreasing ringIds ∧ currentId ∈ ringIds

def postcondition (ringIds : List Nat) (currentId : Nat) (result : Nat) : Prop :=
  result = nextInRingSpec ringIds currentId

end Specs

section Impl

method nextNodeInRing (ringIds : List Nat) (currentId : Nat) return (result : Nat)
  require precondition ringIds currentId
  ensures postcondition ringIds currentId result
  do
    return 0

prove_correct nextNodeInRing by sorry

end Impl

section TestCases

-- Test 1: interior element — successor is next larger ID.
def test1_ringIds : List Nat := [1, 3, 5, 9]
def test1_currentId : Nat := 3
def test1_Expected : Nat := 5

-- Test 2: currentId is the maximum — wraps around to the minimum.
def test2_ringIds : List Nat := [1, 3, 5, 9]
def test2_currentId : Nat := 9
def test2_Expected : Nat := 1

-- Test 3: single-node ring — wraps to itself.
def test3_ringIds : List Nat := [4]
def test3_currentId : Nat := 4
def test3_Expected : Nat := 4

-- Test 4: two-node ring, currentId is the minimum.
def test4_ringIds : List Nat := [2, 7]
def test4_currentId : Nat := 2
def test4_Expected : Nat := 7

-- Test 5: currentId is 0, the smallest possible Nat and the ring minimum.
def test5_ringIds : List Nat := [0, 10, 20]
def test5_currentId : Nat := 0
def test5_Expected : Nat := 10

end TestCases
