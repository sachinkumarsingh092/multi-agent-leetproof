import Velvet.Std
import Extensions.Tactics
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic

namespace Generated.FilterAliveNodes

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
    let mut acc : List Nat := []
    let mut rest : List (Nat × Bool) := nodes
    while rest ≠ []
      -- Invariant: acc holds exactly the alive ids of the processed prefix,
      -- i.e., appending the alive ids of the remaining suffix recovers the full answer.
      -- Init: acc = [] and rest = nodes, so [] ++ aliveIds nodes = aliveIds nodes.
      -- Preservation: processing head p either appends p.1 (if p.2) matching filter/map unfolding, or skips it.
      -- Sufficiency: at exit rest = [], so acc ++ [] = aliveIds nodes, giving the postcondition.
      invariant "acc_partial" acc ++ aliveIds rest = aliveIds nodes
      -- Decreasing: rest shrinks by one element (tail) each iteration.
      decreasing rest.length
    do
      let p := rest.head!
      if p.2 then
        acc := acc ++ [p.1]
      rest := rest.tail
    return acc
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

section Assertions
-- Test case 1

#assert_same_evaluation #[((filterAliveNodes test1_nodes).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((filterAliveNodes test2_nodes).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((filterAliveNodes test3_nodes).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((filterAliveNodes test4_nodes).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((filterAliveNodes test5_nodes).run), DivM.res test5_Expected ]
end Assertions

section Pbt
-- Integration omitted this command: PBT passed before namespacing.
-- velvet_plausible_test filterAliveNodes (config := { maxMs := some 20000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000

theorem goal_0
    (nodes : List (ℕ × Bool))
    (acc : List ℕ)
    (rest : List (ℕ × Bool))
    (invariant_acc_partial : acc ++ List.map (fun (p : ℕ × Bool) => p.1) (List.filter (fun (p : ℕ × Bool) => p.2) rest) = List.map (fun (p : ℕ × Bool) => p.1) (List.filter (fun (p : ℕ × Bool) => p.2) nodes))
    (if_pos : ¬rest = [])
    (if_pos_1 : rest.head!.2 = true)
    : acc ++ rest.head!.1 :: List.map (fun (p : ℕ × Bool) => p.1) (List.filter (fun (p : ℕ × Bool) => p.2) rest.tail) = List.map (fun (p : ℕ × Bool) => p.1) (List.filter (fun (p : ℕ × Bool) => p.2) nodes) := by
    cases rest with
    | nil => exact absurd rfl if_pos
    | cons p t =>
      simp only [List.head!_cons, List.tail_cons] at *
      rw [List.filter_cons_of_pos (by simpa using if_pos_1)] at invariant_acc_partial
      simpa using invariant_acc_partial

theorem goal_1
    (rest : List (ℕ × Bool))
    (if_pos : ¬rest = [])
    : OfNat.ofNat 0 < rest.length := by
    intros; expose_names; exact List.length_pos.mpr if_pos

theorem goal_2
    (nodes : List (ℕ × Bool))
    (acc : List ℕ)
    (rest : List (ℕ × Bool))
    (invariant_acc_partial : acc ++ List.map (fun (p : ℕ × Bool) => p.1) (List.filter (fun (p : ℕ × Bool) => p.2) rest) = List.map (fun (p : ℕ × Bool) => p.1) (List.filter (fun (p : ℕ × Bool) => p.2) nodes))
    (if_pos : ¬rest = [])
    (if_neg : rest.head!.2 = false)
    : acc ++ List.map (fun (p : ℕ × Bool) => p.1) (List.filter (fun (p : ℕ × Bool) => p.2) rest.tail) = List.map (fun (p : ℕ × Bool) => p.1) (List.filter (fun (p : ℕ × Bool) => p.2) nodes) := by
    cases rest with
    | nil => exact absurd rfl if_pos
    | cons p t =>
      simp [List.head!] at if_neg
      simpa [List.filter_cons, if_neg] using invariant_acc_partial

theorem goal_3
    (rest : List (ℕ × Bool))
    (if_pos : ¬rest = [])
    : OfNat.ofNat 0 < rest.length := by
    intros; expose_names; exact goal_1 rest if_pos


prove_correct filterAliveNodes by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at * <;> expose_names); try (conv => congr <;> simp) ; try rfl; try expose_names)
  exact (goal_0 nodes acc rest invariant_acc_partial if_pos if_pos_1)
  exact (goal_1 rest if_pos)
  exact (goal_2 nodes acc rest invariant_acc_partial if_pos if_neg)
  exact (goal_3 rest if_pos)
end Proof
end Generated.FilterAliveNodes
