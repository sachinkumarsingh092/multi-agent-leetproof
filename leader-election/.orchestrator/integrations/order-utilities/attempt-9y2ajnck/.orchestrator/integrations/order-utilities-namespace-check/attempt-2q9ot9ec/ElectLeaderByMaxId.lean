import Velvet.Std
import Extensions.Tactics
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic

namespace Generated.ElectLeaderByMaxId

set_option maxHeartbeats 10000000
set_option pp.coercions false
set_option pp.funBinderTypes true
set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

/- Problem Description

Bully-style leader election core rule: among the alive node IDs, the node with
the highest ID becomes leader.

Input:
- aliveIds : List Nat — the IDs of the alive nodes. IDs are pairwise distinct
  (precondition), but the list is in arbitrary order. The list may be empty.

Output:
- Option Nat.
  - If the list is nonempty, return `some maxId` where `maxId` is the largest
    ID occurring in the list (the maximum may appear at any position).
  - If the list is empty, return `none` (no leader can be elected).

Preconditions:
- The IDs in `aliveIds` are pairwise distinct (`aliveIds.Nodup`).
- The list may be empty.

Edge cases:
- Empty list returns `none`.
- A single-element list returns `some` of that element.
- The maximum may appear at any position in the list.

Determinism:
- The function is pure; identical inputs always produce identical outputs.
  The result depends only on the set of IDs: any permutation of the same
  multiset of IDs yields the same result. This follows from the postcondition,
  which characterizes the result purely in terms of membership and ordering.
-/

section Specs
def precondition (aliveIds : List Nat) : Prop :=
  aliveIds.Nodup

def postcondition (aliveIds : List Nat) (result : Option Nat) : Prop :=
  (aliveIds = [] → result = none) ∧
  (aliveIds ≠ [] →
    ∃ m : Nat, result = some m ∧ m ∈ aliveIds ∧ ∀ x ∈ aliveIds, x ≤ m)
end Specs

section Impl
method electLeaderByMaxId (aliveIds : List Nat) return (result : Option Nat)
  require precondition aliveIds
  ensures postcondition aliveIds result
do
  let arr : Array Nat := aliveIds.toArray
  if arr.size = 0 then
    return none
  else
    let mut best := arr[0]!
    let mut i := 1
    while i < arr.size
      -- Invariant 1: i stays within bounds; initialized at i = 1 (arr.size > 0), preserved by i := i + 1
      invariant "i_bounds" 1 ≤ i ∧ i ≤ arr.size
      -- Invariant 2: best is always an element of aliveIds; initialized with arr[0]!, preserved since updates take arr[i]!
      invariant "best_mem" best ∈ aliveIds
      -- Invariant 3: best is an upper bound of the scanned prefix arr[0..i); at exit i = arr.size, giving best ≥ all elements
      invariant "best_max_prefix" ∀ k, k < i → arr[k]! ≤ best
      -- Decreasing: distance to loop bound decreases since i increments each iteration
      decreasing arr.size - i
    do
      if arr[i]! > best then
        best := arr[i]!
      i := i + 1
    return some best
end Impl

section TestCases
-- Test 1: maximum in the middle of the list
def test1_aliveIds : List Nat := [3, 1, 7, 2]
def test1_Expected : Option Nat := some 7

-- Test 2: empty list — no leader can be elected
def test2_aliveIds : List Nat := []
def test2_Expected : Option Nat := none

-- Test 3: single-element list returns that element
def test3_aliveIds : List Nat := [42]
def test3_Expected : Option Nat := some 42

-- Test 4: maximum at the first position
def test4_aliveIds : List Nat := [9, 5, 1]
def test4_Expected : Option Nat := some 9

-- Test 5: maximum at the last position, including ID 0
def test5_aliveIds : List Nat := [0, 1]
def test5_Expected : Option Nat := some 1
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((electLeaderByMaxId test1_aliveIds).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((electLeaderByMaxId test2_aliveIds).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((electLeaderByMaxId test3_aliveIds).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((electLeaderByMaxId test4_aliveIds).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((electLeaderByMaxId test5_aliveIds).run), DivM.res test5_Expected ]
end Assertions

section Pbt
velvet_plausible_test electLeaderByMaxId (config := { maxMs := some 20000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000

theorem goal_0
    (aliveIds : List ℕ)
    (if_pos : aliveIds = [])
    : postcondition aliveIds none := by
    intros; expose_names; try simp_all; try grind


prove_correct electLeaderByMaxId by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at * <;> expose_names); try (conv => congr <;> simp) ; try rfl; try expose_names)
  exact (goal_0 aliveIds if_pos)
end Proof
end Generated.ElectLeaderByMaxId
