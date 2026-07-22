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

Implement a pure function that extracts the IDs of alive nodes from a cluster
membership snapshot.

Input domain: a list of pairs (nodeId, isAlive), where nodeId is a Nat and
isAlive is a Bool. Node IDs in the input are pairwise distinct. The list may
be empty.

Output domain: a list of Nat containing exactly the nodeId values whose
isAlive flag is true, preserving the original input order.

Preconditions: node IDs in the input list are pairwise distinct. The list may
be empty.

Edge cases:
- An empty input list returns an empty list.
- If no node is alive, return an empty list.
- If all nodes are alive, return all IDs in the original order.

Determinism: the function is pure; identical inputs always produce identical
outputs.

Assumptions: no units are involved; nodeId values are arbitrary natural
numbers. The output is fully determined by the input: it equals the first
components of the input pairs whose second component is true, kept in input
order.
-/

section Specs

-- The reference extraction: keep pairs whose flag is true, project the ids,
-- preserving input order.
def aliveIds (nodes : List (Nat × Bool)) : List Nat :=
  (nodes.filter (fun p => p.2)).map (fun p => p.1)

def precondition (nodes : List (Nat × Bool)) : Prop :=
  (nodes.map Prod.fst).Nodup

def postcondition (nodes : List (Nat × Bool)) (result : List Nat) : Prop :=
  result = aliveIds nodes

end Specs

section Impl

method filterAliveNodes (nodes : List (Nat × Bool)) return (result : List Nat)
  require precondition nodes
  ensures postcondition nodes result
  do
    return []

prove_correct filterAliveNodes by sorry

end Impl

section TestCases

-- Test 1: mixed alive and dead nodes; order preserved.
def test1_nodes : List (Nat × Bool) := [(1, true), (2, false), (3, true)]
def test1_Expected : List Nat := [1, 3]

-- Test 2: empty input returns empty output.
def test2_nodes : List (Nat × Bool) := []
def test2_Expected : List Nat := []

-- Test 3: no node alive returns empty output.
def test3_nodes : List (Nat × Bool) := [(7, false), (4, false)]
def test3_Expected : List Nat := []

-- Test 4: single alive node.
def test4_nodes : List (Nat × Bool) := [(5, true)]
def test4_Expected : List Nat := [5]

-- Test 5: all nodes alive; all IDs returned in input order.
def test5_nodes : List (Nat × Bool) := [(10, true), (2, true), (8, true)]
def test5_Expected : List Nat := [10, 2, 8]

end TestCases
