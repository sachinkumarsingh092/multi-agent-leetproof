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
    let arr : Array Nat := ringIds.toArray
    let mut i := 0
    let mut found := false
    let mut candidate := 0
    while i < arr.size ∧ found = false
      -- Invariant 1: i stays within array bounds.
      -- Init: i = 0 ≤ arr.size. Preserved: i incremented only when i < arr.size.
      invariant "i_bound" i ≤ arr.size
      -- Invariant 2: all elements greater than currentId lie in the unscanned suffix.
      -- Init: drop 0 = ringIds. Preserved: skipped elements fail the filter (¬ currentId < arr[i]!).
      -- Sufficiency: at i = arr.size with found = false, greaterIds = [], so wrap to arr[0]! = headD 0.
      invariant "filter_drop" greaterIds ringIds currentId = greaterIds (ringIds.drop i) currentId
      -- Invariant 3: if found, candidate is the current element and exceeds currentId,
      -- hence it is the head of greaterIds (drop i), which equals greaterIds ringIds by Inv 2.
      invariant "found_state" found = true → i < arr.size ∧ candidate = arr[i]! ∧ currentId < candidate
      done_with (i = arr.size ∨ found = true)
      -- Decreasing: lexicographic-style measure. In the else branch i increments,
      -- so the measure drops by 2. In the then branch i is unchanged but found flips
      -- false → true, so the (if found then 0 else 1) term drops from 1 to 0.
      decreasing 2 * (arr.size - i) + (if found then 0 else 1)
    do
      if currentId < arr[i]! then
        candidate := arr[i]!
        found := true
      else
        i := i + 1
    if found then
      return candidate
    else
      return arr[0]!
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

section Assertions
-- Test case 1

#assert_same_evaluation #[((nextNodeInRing test1_ringIds test1_currentId).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((nextNodeInRing test2_ringIds test2_currentId).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((nextNodeInRing test3_ringIds test3_currentId).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((nextNodeInRing test4_ringIds test4_currentId).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((nextNodeInRing test5_ringIds test5_currentId).run), DivM.res test5_Expected ]
end Assertions

section Pbt
velvet_plausible_test nextNodeInRing (config := { maxMs := some 20000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000

theorem goal_0
    (ringIds : List ℕ)
    (currentId : ℕ)
    (i : ℕ)
    (invariant_filter_drop : List.filter (fun (x : ℕ) => decide (currentId < x)) ringIds = List.filter (fun (x : ℕ) => decide (currentId < x)) (List.drop i ringIds))
    (a : i < ringIds.length)
    (if_neg : ringIds[i]?.getD (OfNat.ofNat 0) ≤ currentId)
    : List.filter (fun (x : ℕ) => decide (currentId < x)) ringIds = List.filter (fun (x : ℕ) => decide (currentId < x)) (List.drop (i + OfNat.ofNat 1) ringIds) := by
  have hdrop : List.drop i ringIds = ringIds[i] :: List.drop (i + 1) ringIds :=
    List.drop_eq_getElem_cons a
  have hle : ringIds[i] ≤ currentId := by
    simpa [List.getElem?_eq_getElem a] using if_neg
  rw [invariant_filter_drop, hdrop, List.filter_cons]
  simp [Nat.not_lt.mpr hle]

theorem goal_1
    (ringIds : List ℕ)
    (currentId : ℕ)
    (i_1 : ℕ)
    (i_3 : ℕ)
    (invariant_filter_drop : List.filter (fun (x : ℕ) => decide (currentId < x)) ringIds = List.filter (fun (x : ℕ) => decide (currentId < x)) (List.drop i_3 ringIds))
    (invariant_found_state : i_3 < ringIds.length ∧ i_1 = ringIds[i_3]?.getD (OfNat.ofNat 0) ∧ currentId < i_1)
    : postcondition ringIds currentId i_1 := by
  obtain ⟨hlt, hi1, hcur⟩ := invariant_found_state
  have hget : ringIds[i_3]?.getD (OfNat.ofNat 0) = ringIds[i_3] := by
    rw [List.getElem?_eq_getElem hlt]
    rfl
  have hi1' : i_1 = ringIds[i_3] := by rw [hi1, hget]
  have hdrop : List.drop i_3 ringIds = ringIds[i_3] :: List.drop (i_3 + 1) ringIds :=
    List.drop_eq_getElem_cons hlt
  have hdec : decide (currentId < ringIds[i_3]) = true := by
    simp only [decide_eq_true_eq]
    omega
  simp only [postcondition, nextInRingSpec, greaterIds]
  rw [invariant_filter_drop, hdrop, List.filter_cons, hdec]
  simp [hi1']

theorem goal_2
    (ringIds : List ℕ)
    (currentId : ℕ)
    (require_1 : ¬ringIds = [] ∧ List.Pairwise (fun (x1 x2 : ℕ) => x1 < x2) ringIds ∧ currentId ∈ ringIds)
    (i_1 : ℕ)
    (i_2 : Bool)
    (i_3 : ℕ)
    (invariant_filter_drop : List.filter (fun (x : ℕ) => decide (currentId < x)) ringIds = List.filter (fun (x : ℕ) => decide (currentId < x)) (List.drop i_3 ringIds))
    (if_neg : i_2 = false)
    (invariant_i_bound : i_3 ≤ ringIds.length)
    (done_1 : i_3 = ringIds.length ∨ i_2 = true)
    (invariant_found_state : i_2 = true → i_3 < ringIds.length ∧ i_1 = ringIds[i_3]?.getD (OfNat.ofNat 0) ∧ currentId < i_1)
    : postcondition ringIds currentId (ringIds[OfNat.ofNat 0]?.getD (OfNat.ofNat 0)) := by
  have hi3 : i_3 = ringIds.length := by
    cases done_1 with
    | inl h => exact h
    | inr h => simp [if_neg] at h
  have hdrop : List.drop i_3 ringIds = [] := by
    simp [hi3]
  have hfilter : List.filter (fun x => decide (currentId < x)) ringIds = [] := by
    rw [invariant_filter_drop, hdrop]; rfl
  simp only [postcondition, nextInRingSpec, greaterIds, hfilter]
  cases ringIds with
  | nil => rfl
  | cons a l => rfl


prove_correct nextNodeInRing by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at * <;> expose_names); try (conv => congr <;> simp) ; try rfl; try expose_names)
  exact (goal_0 ringIds currentId i invariant_filter_drop a if_neg)
  exact (goal_1 ringIds currentId i_1 i_3 invariant_filter_drop invariant_found_state)
  exact (goal_2 ringIds currentId require_1 i_1 i_2 i_3 invariant_filter_drop if_neg invariant_i_bound done_1 invariant_found_state)
end Proof
