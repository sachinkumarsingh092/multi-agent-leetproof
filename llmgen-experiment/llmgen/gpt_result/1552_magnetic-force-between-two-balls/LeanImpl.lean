import Lean
import Mathlib.Tactic
import Velvet.Std
import Extensions.VelvetPBT

set_option maxHeartbeats 10000000

section Specs
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false
set_option pp.funBinderTypes true

/- Problem Description
    1552. Magnetic Force Between Two Balls: maximize the minimum distance between any two placed balls.
    **Important: complexity should be O(n log n) time and O(1) space**
    Natural language breakdown:
    1. We are given n basket positions as natural numbers in an array `position`.
    2. The input array `position` is given in ascending sorted order.
    3. We must place exactly m balls into m distinct baskets (so we choose m distinct indices).
    4. The magnetic force between two balls at positions x and y is |x - y|.
    5. For a particular placement, its score is the minimum force among all pairs of chosen baskets.
    6. The required answer is the maximum score achievable over all valid placements.
    7. Constraints imply m ≥ 2 and m ≤ n; basket positions are pairwise distinct.
-/

-- Strictly increasing indices inside an array.
def StrictlyIncreasing (idxs : Array Nat) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < idxs.size → idxs[i]! < idxs[j]!

-- All indices are within bounds of the positions array.
def IndicesInRange (pos : Array Nat) (idxs : Array Nat) : Prop :=
  ∀ (k : Nat), k < idxs.size → idxs[k]! < pos.size

-- Pairwise distance lower bound for the chosen indices.
def PairwiseDistGE (pos : Array Nat) (idxs : Array Nat) (d : Nat) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < idxs.size →
    d ≤ (pos[idxs[j]!]!) - (pos[idxs[i]!]!)

-- Feasibility predicate: there exists a selection of exactly m baskets
-- whose pairwise distances are all at least d.
def Feasible (pos : Array Nat) (m : Nat) (d : Nat) : Prop :=
  ∃ (idxs : Array Nat),
    idxs.size = m ∧
    StrictlyIncreasing idxs ∧
    IndicesInRange pos idxs ∧
    PairwiseDistGE pos idxs d

def precondition (position : Array Nat) (m : Nat) : Prop :=
  m ≥ 2 ∧ m ≤ position.size ∧ StrictlyIncreasing position

-- The result is the maximum d such that placing m balls with minimum pairwise distance ≥ d is feasible.
def postcondition (position : Array Nat) (m : Nat) (result : Nat) : Prop :=
  Feasible position m result ∧
  (∀ (d' : Nat), result < d' → ¬ Feasible position m d')
end Specs

section Impl
def implementation (position : Array Nat) (m : Nat) : Nat :=
  let n := position.size
  if n = 0 then
    0
  else
    let minPos := position[0]!
    let maxPos := position[n - 1]!

    -- Greedy feasibility check in one left-to-right pass.
    let canPlace (d : Nat) : Bool :=
      let (count, _last) :=
        position.foldl
          (fun (st : Nat × Nat) (cur : Nat) =>
            let (count, last) := st
            if count = 0 then
              (1, cur)
            else if last + d ≤ cur then
              (count + 1, cur)
            else
              (count, last))
          (0, 0)
      count ≥ m

    let hi0 := maxPos - minPos

    -- Construct the maximum feasible distance by setting bits from high to low.
    -- We use `hi0.size` bits, which is enough for unbounded `Nat`.
    let rec loop (b : Nat) (ans : Nat) : Nat :=
      match b with
      | 0 => ans
      | b' + 1 =>
        let bit : Nat := Nat.shiftLeft 1 b'
        let cand := ans + bit
        let ans' := if cand ≤ hi0 ∧ canPlace cand then cand else ans
        loop b' ans'

    loop hi0.size 0
end Impl

section TestCases
-- Test case 1: Example 1 (sorted)
-- position = [1,2,3,4,7], m = 3 => 3
def test1_position : Array Nat := #[1, 2, 3, 4, 7]
def test1_m : Nat := 3
def test1_Expected : Nat := 3

-- Test case 2: Example 2 (sorted)
-- position = [1,2,3,4,5,1000000000], m = 2 => 999999999
def test2_position : Array Nat := #[1, 2, 3, 4, 5, 1000000000]
def test2_m : Nat := 2
def test2_Expected : Nat := 999999999

-- Test case 3: Smallest valid n and m (two baskets, two balls)
def test3_position : Array Nat := #[10, 20]
def test3_m : Nat := 2
def test3_Expected : Nat := 10

-- Test case 4: m = n (must place in every basket; answer is min adjacent gap)
def test4_position : Array Nat := #[1, 6, 11, 20]
def test4_m : Nat := 4
def test4_Expected : Nat := 5

-- Test case 5: Spread-out positions; m=2 => max distance between endpoints
def test5_position : Array Nat := #[0, 7, 10, 19]
def test5_m : Nat := 2
def test5_Expected : Nat := 19

-- Test case 6: Many close positions; m=3
-- Choose 0,4,10 gives min distance 4; cannot reach 5.
def test6_position : Array Nat := #[0, 1, 2, 4, 8, 10]
def test6_m : Nat := 3
def test6_Expected : Nat := 4

-- Test case 7: Sorted input; m=3
-- Choose 1,9,17 gives min 8.
def test7_position : Array Nat := #[1, 9, 10, 17]
def test7_m : Nat := 3
def test7_Expected : Nat := 8

-- Test case 8: Symmetric spacing; m=3
-- Choose 0,3,6 yields min 3.
def test8_position : Array Nat := #[0, 2, 3, 5, 6]
def test8_m : Nat := 3
def test8_Expected : Nat := 3

-- Test case 9: Sorted; m=2 (answer is distance between min and max)
def test9_position : Array Nat := #[0, 25, 50, 75, 100]
def test9_m : Nat := 2
def test9_Expected : Nat := 100
end TestCases

section Assertions
-- Test case 1
#assert_same_evaluation #[(implementation test1_position test1_m), test1_Expected]

-- Test case 2
#assert_same_evaluation #[(implementation test2_position test2_m), test2_Expected]

-- Test case 3
#assert_same_evaluation #[(implementation test3_position test3_m), test3_Expected]

-- Test case 4
#assert_same_evaluation #[(implementation test4_position test4_m), test4_Expected]

-- Test case 5
#assert_same_evaluation #[(implementation test5_position test5_m), test5_Expected]

-- Test case 6
#assert_same_evaluation #[(implementation test6_position test6_m), test6_Expected]

-- Test case 7
#assert_same_evaluation #[(implementation test7_position test7_m), test7_Expected]

-- Test case 8
#assert_same_evaluation #[(implementation test8_position test8_m), test8_Expected]

-- Test case 9
#assert_same_evaluation #[(implementation test9_position test9_m), test9_Expected]
end Assertions

section Pbt
method implementationPbt (position : Array Nat) (m : Nat)
  return (result : Nat)
  require precondition position m
  ensures postcondition position m result
  do
  return (implementation position m)

velvet_plausible_test implementationPbt (config := { maxMs := some 20000 })
end Pbt

section Proof
theorem correctness_goal_0_0
    (position : Array ℕ)
    (m : ℕ)
    (h_precond : precondition position m)
    : Feasible position m 0 := by
  classical
  -- We'll witness feasibility using the first `m` indices.
  let idxs : Array Nat := Array.range m
  have hidxs_size : idxs.size = m := by
    simp [idxs, Array.size_range]

  have hrange_get! : ∀ (i : Nat), i < m → idxs[i]! = i := by
    intro i hi
    -- `idxs = Array.range m`, and `get!` agrees with the range value in-bounds.
    -- We compute via `getD` and the `getElem?_range` characterization.
    simp [idxs, Array.get!_eq_getD, Array.getD, Array.getElem?_range, hi]

  refine ⟨idxs, hidxs_size, ?_, ?_, ?_⟩
  · -- StrictlyIncreasing
    intro i j hij hj
    have hjm : j < m := by
      simpa [hidxs_size] using hj
    have him : i < m := Nat.lt_trans hij hjm
    simpa [hrange_get! i him, hrange_get! j hjm] using hij
  · -- IndicesInRange
    intro k hk
    have hkm : k < m := by
      simpa [hidxs_size] using hk
    have hm_le : m ≤ position.size := h_precond.2.1
    have hkpos : k < position.size := Nat.lt_of_lt_of_le hkm hm_le
    simpa [hrange_get! k hkm] using hkpos
  · -- PairwiseDistGE with d = 0 is trivial on `Nat`.
    intro i j hij hj
    exact Nat.zero_le _

theorem correctness_goal_0_1
    (position : Array ℕ)
    (m : ℕ)
    (h_precond : precondition position m)
    (hFeas0 : Feasible position m 0)
    : ∀ (d : ℕ),
  m ≤
      (Array.foldl
          (fun st cur =>
            Prod.casesOn st fun fst snd =>
              (fun count last =>
                  if count = 0 then (1, cur) else if last + d ≤ cur then (count + 1, cur) else (count, last))
                fst snd)
          (0, 0) position).1 →
    Feasible position m d := by
    sorry

theorem correctness_goal_0_2
    (position : Array ℕ)
    (m : ℕ)
    : ∀ (canPlace : ℕ → Bool) (hi0 b ans : ℕ),
  Feasible position m ans →
    (∀ (d : ℕ), canPlace d = true → Feasible position m d) →
      Feasible position m (implementation.loop canPlace hi0 b ans) := by
  intro canPlace hi0 b ans hFeas hCan
  induction b generalizing ans with
  | zero =>
      simpa [implementation.loop] using hFeas
  | succ b ih =>
      -- unfold one step and reduce to the induction hypothesis
      simp [implementation.loop]
      -- show feasibility of the updated answer
      have hFeas' :
          Feasible position m
            (if ans + 1 <<< b ≤ hi0 ∧ canPlace (ans + 1 <<< b) = true then ans + 1 <<< b else ans) := by
        by_cases h : ans + 1 <<< b ≤ hi0 ∧ canPlace (ans + 1 <<< b) = true
        · have hcand : Feasible position m (ans + 1 <<< b) := hCan (ans + 1 <<< b) h.2
          simp [h, hcand]
        · simp [h, hFeas]
      exact ih _ hFeas'

theorem correctness_goal_0
    (position : Array ℕ)
    (m : ℕ)
    (h_precond : precondition position m)
    : Feasible position m (implementation position m) := by
  classical
  have hFeas0 : Feasible position m 0 := by
    expose_names; exact (correctness_goal_0_0 position m h_precond)

  have h_greedy_sound :
      ∀ (d : Nat),
        m ≤
            (position.foldl
              (fun (st : Nat × Nat) (cur : Nat) =>
                let (count, last) := st
                if count = 0 then (1, cur)
                else if last + d ≤ cur then (count + 1, cur)
                else (count, last))
              (0, 0)).1
          → Feasible position m d := by
    expose_names; exact (correctness_goal_0_1 position m h_precond hFeas0)

  have h_loop_feasible :
      ∀ (canPlace : Nat → Bool) (hi0 : Nat) (b ans : Nat),
        Feasible position m ans →
        (∀ d : Nat, canPlace d = true → Feasible position m d) →
        Feasible position m (implementation.loop canPlace hi0 b ans) := by
    expose_names; exact (correctness_goal_0_2 position m)

  unfold implementation
  by_cases h0 : position.size = 0
  · have hmle : m ≤ 0 := by simpa [h0] using h_precond.2.1
    have hmge : 2 ≤ m := h_precond.1
    have : (2 : Nat) ≤ 0 := le_trans hmge hmle
    omega
  · simp [h0]
    refine h_loop_feasible
      (canPlace :=
        fun d =>
          decide
            (m ≤
              (position.foldl
                (fun (st : Nat × Nat) (cur : Nat) =>
                  let (count, last) := st
                  if count = 0 then (1, cur)
                  else if last + d ≤ cur then (count + 1, cur)
                  else (count, last))
                (0, 0)).1))
      (hi0 := position[position.size - 1]! - position[0]!)
      (b := (position[position.size - 1]! - position[0]!).size)
      (ans := 0)
      ?_ ?_
    · simpa using hFeas0
    · intro d hd
      have : m ≤
          (position.foldl
            (fun (st : Nat × Nat) (cur : Nat) =>
              let (count, last) := st
              if count = 0 then (1, cur)
              else if last + d ≤ cur then (count + 1, cur)
              else (count, last))
            (0, 0)).1 := by
        exact (decide_eq_true_eq.mp hd)
      exact h_greedy_sound d this

theorem correctness_goal_1
    (position : Array ℕ)
    (m : ℕ)
    (h_precond : precondition position m)
    (h_feas : Feasible position m (implementation position m))
    : ∀ (d' : ℕ), implementation position m < d' → ¬Feasible position m d' := by
    sorry

theorem correctness_goal
    (position : Array Nat)
    (m : Nat)
    (h_precond : precondition position m)
    : postcondition position m (implementation position m) := by
  classical
  unfold postcondition
  have h_feas : Feasible position m (implementation position m) := by
    expose_names; exact (correctness_goal_0 position m h_precond)
  have h_max : ∀ (d' : Nat), implementation position m < d' → ¬ Feasible position m d' := by
    expose_names; exact (correctness_goal_1 position m h_precond h_feas)
  exact And.intro h_feas h_max
end Proof
