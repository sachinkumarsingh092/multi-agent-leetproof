import Velvet.Std
import Extensions.Tactics
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false
set_option pp.funBinderTypes true
set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

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

section Specs
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
method MagneticForceBetweenTwoBalls (position : Array Nat) (m : Nat)
  return (result : Nat)
  require precondition position m
  ensures postcondition position m result
  do
  -- Binary search on the answer d, with greedy feasibility check in O(n).
  let n := position.size
  -- precondition gives m ≤ n and n > 0; m ≥ 2.
  let loInit : Nat := 0
  let hiInit : Nat := position[n-1]! - position[0]!

  let mut lo := loInit
  let mut hi := hiInit

  -- Invariant: answer is in [lo, hi]. We use upper-mid to ensure termination.
  while lo < hi
    -- lo/hi stay within initial bounds
    invariant "bs_bounds" lo ≤ hi ∧ hi ≤ hiInit
    -- lo is always feasible
    invariant "bs_lo_feasible" Feasible position m lo
    -- (hi+1) is always infeasible, so hi is an upper bound on the optimum
    invariant "bs_hi1_infeasible" ¬ Feasible position m (hi + 1)
    -- feasibility is monotone decreasing in d
    invariant "bs_mono" (∀ (d1 d2 : Nat), d1 ≤ d2 → Feasible position m d2 → Feasible position m d1)
    decreasing hi - lo
  do
    let mid := (lo + hi + 1) / 2

    -- Greedy check: can we place at least m balls with minimum distance >= mid?
    let mut cnt : Nat := 1
    let mut lastPos : Nat := position[0]!
    let mut i : Nat := 1
    while i < n ∧ cnt < m
      -- i scans the remaining positions
      invariant "gr_i_bounds" 1 ≤ i ∧ i ≤ n
      -- cnt counts placed balls; always within [1,m] and never exceeds i
      invariant "gr_cnt_bounds" 1 ≤ cnt ∧ cnt ≤ m ∧ cnt ≤ i
      -- witness for the greedy placement of size cnt, ending at lastPos, using only indices < i
      invariant "gr_witness" (
        ∃ (idxs : Array Nat),
          idxs.size = cnt ∧
          StrictlyIncreasing idxs ∧
          IndicesInRange position idxs ∧
          PairwiseDistGE position idxs mid ∧
          idxs[cnt-1]! < i ∧
          lastPos = position[idxs[cnt-1]!]!
      )
      -- in any feasible placement with > cnt balls, the cnt-th ball is at position ≥ lastPos
      -- (needed to justify skipping i when position[i] is too close to lastPos)
      invariant "gr_min_extend_prefix" (
        ∀ (idxs2 : Array Nat), cnt < idxs2.size →
          StrictlyIncreasing idxs2 →
          IndicesInRange position idxs2 →
          PairwiseDistGE position idxs2 mid →
          lastPos ≤ position[idxs2[cnt-1]!]!
      )
      -- no feasible placement with > cnt balls can put its (cnt+1)-th ball before i
      invariant "gr_no_more_prefix" (
        ∀ (idxs2 : Array Nat), cnt < idxs2.size →
          StrictlyIncreasing idxs2 →
          IndicesInRange position idxs2 →
          PairwiseDistGE position idxs2 mid →
          i ≤ idxs2[cnt]!
      )
      decreasing n - i
    do
      let p := position[i]!
      if mid ≤ p - lastPos then
        cnt := cnt + 1
        lastPos := p
      i := i + 1

    if cnt ≥ m then
      lo := mid
    else
      -- mid > 0 here because lo < hi implies lo + hi + 1 >= 1
      hi := mid - 1

  return lo
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

#assert_same_evaluation #[((MagneticForceBetweenTwoBalls test1_position test1_m).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((MagneticForceBetweenTwoBalls test2_position test2_m).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((MagneticForceBetweenTwoBalls test3_position test3_m).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((MagneticForceBetweenTwoBalls test4_position test4_m).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((MagneticForceBetweenTwoBalls test5_position test5_m).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((MagneticForceBetweenTwoBalls test6_position test6_m).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((MagneticForceBetweenTwoBalls test7_position test7_m).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((MagneticForceBetweenTwoBalls test8_position test8_m).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((MagneticForceBetweenTwoBalls test9_position test9_m).run), DivM.res test9_Expected ]
end Assertions

section Pbt
velvet_plausible_test MagneticForceBetweenTwoBalls (config := { maxMs := some 20000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000

theorem goal_0
    (position : Array ℕ)
    (m : ℕ)
    (hi : ℕ)
    (lo : ℕ)
    (cnt : ℕ)
    (i : ℕ)
    (lastPos : ℕ)
    (a_4 : OfNat.ofNat 1 ≤ cnt)
    (invariant_gr_witness : ∃ (idxs : Array ℕ), idxs.size = cnt ∧ (∀ (i j : ℕ), i < j → j < idxs.size → idxs[i]! < idxs[j]!) ∧ (∀ k < idxs.size, idxs[k]! < position.size) ∧ (∀ (i j : ℕ), i < j → j < idxs.size → (lo + hi + OfNat.ofNat 1) / OfNat.ofNat 2 ≤ position[idxs[j]!]! - position[idxs[i]!]!) ∧ idxs[cnt - OfNat.ofNat 1]! < i ∧ lastPos = position[idxs[cnt - OfNat.ofNat 1]!]!)
    (a_7 : i < position.size)
    (if_pos_1 : (lo + hi + OfNat.ofNat 1) / OfNat.ofNat 2 ≤ position[i]! - lastPos)
    (require_1 : OfNat.ofNat 2 ≤ m ∧ m ≤ position.size ∧ ∀ (i j : ℕ), i < j → j < position.size → position[i]! < position[j]!)
    : ∃ (idxs : Array ℕ), idxs.size = cnt + OfNat.ofNat 1 ∧ (∀ (i j : ℕ), i < j → j < idxs.size → idxs[i]! < idxs[j]!) ∧ (∀ k < idxs.size, idxs[k]! < position.size) ∧ (∀ (i j : ℕ), i < j → j < idxs.size → (lo + hi + OfNat.ofNat 1) / OfNat.ofNat 2 ≤ position[idxs[j]!]! - position[idxs[i]!]!) ∧ idxs[cnt]! < i + OfNat.ofNat 1 ∧ position[i]! = position[idxs[cnt]!]! := by
  classical
  rcases invariant_gr_witness with ⟨idxs0, hsz0, hinc0, hrng0, hdist0, hlastlt, hlastPos⟩

  -- When `k < xs.size`, `xs[k]!` coincides with the in-bounds `getElem`.
  have getBang_eq_get {xs : Array Nat} {k : Nat} (hk : k < xs.size) : xs[k]! = xs[k]'hk := by
    simp [Array.getElem!_eq_getD, Array.getD, hk]

  have push_getBang_lt {k : Nat} (hk : k < idxs0.size) : (idxs0.push i)[k]! = idxs0[k]! := by
    have hk' : k < (idxs0.push i).size := by
      simpa [Array.size_push] using Nat.lt_of_lt_of_le hk (Nat.le_succ idxs0.size)
    calc
      (idxs0.push i)[k]! = (idxs0.push i)[k]'hk' := getBang_eq_get hk'
      _ = idxs0[k]'hk := by
        simpa using (Array.getElem_push_lt (xs := idxs0) (x := i) (i := k) hk)
      _ = idxs0[k]! := (getBang_eq_get hk).symm

  have push_getBang_eq : (idxs0.push i)[idxs0.size]! = i := by
    have hk' : idxs0.size < (idxs0.push i).size := by
      simpa [Array.size_push] using Nat.lt_succ_self idxs0.size
    calc
      (idxs0.push i)[idxs0.size]! = (idxs0.push i)[idxs0.size]'hk' := getBang_eq_get hk'
      _ = i := by
        simpa using (Array.getElem_push_eq (xs := idxs0) (x := i))

  let idxs : Array Nat := idxs0.push i
  refine ⟨idxs, ?_, ?_, ?_, ?_, ?_, ?_⟩

  · simp [idxs, hsz0, Array.size_push, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

  · -- strictly increasing
    intro p q hpq hq
    have hq' : q < cnt + 1 := by
      simpa [idxs, hsz0, Array.size_push, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hq
    have hqle : q ≤ cnt := Nat.le_of_lt_succ hq'
    cases lt_or_eq_of_le hqle with
    | inl hqcnt =>
        have hp0 : p < idxs0.size := by
          have : p < cnt := Nat.lt_trans hpq hqcnt
          simpa [hsz0] using this
        have hq0 : q < idxs0.size := by simpa [hsz0] using hqcnt
        have hbase : idxs0[p]! < idxs0[q]! := hinc0 p q hpq hq0
        simpa [idxs, push_getBang_lt hp0, push_getBang_lt hq0] using hbase
    | inr hqeq =>
        have hp_lt_cnt : p < cnt := Nat.lt_of_lt_of_le hpq (by simpa [hqeq] using hqle)
        have hp0 : p < idxs0.size := by simpa [hsz0] using hp_lt_cnt
        have hlast : idxs[cnt]! = i := by
          simpa [idxs, hsz0] using push_getBang_eq
        have hp_to_i : idxs[p]! < i := by
          have hp_eq : idxs[p]! = idxs0[p]! := by simpa [idxs] using push_getBang_lt hp0
          by_cases hpc : p = cnt - 1
          · -- p is the last old index
            subst hpc
            simpa [hp_eq] using hlastlt
          ·
            have hpred_lt_cnt : cnt - 1 < cnt := by
              have : cnt - 1 < (cnt - 1) + 1 := Nat.lt_succ_self (cnt - 1)
              simpa [Nat.sub_add_cancel a_4, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
            have hlastBound : cnt - 1 < idxs0.size := by simpa [hsz0] using hpred_lt_cnt
            have hp_le : p ≤ cnt - 1 := Nat.le_pred_of_lt hp_lt_cnt
            have hp_lt : p < cnt - 1 := lt_of_le_of_ne hp_le hpc
            have hlt_lastIdx : idxs0[p]! < idxs0[cnt - 1]! := hinc0 p (cnt - 1) hp_lt hlastBound
            have : idxs0[p]! < i := lt_of_lt_of_le hlt_lastIdx (Nat.le_of_lt hlastlt)
            simpa [hp_eq] using this
        simpa [hqeq, hlast] using hp_to_i

  · -- indices in range
    intro k hk
    have hk' : k < cnt + 1 := by
      simpa [idxs, hsz0, Array.size_push, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hk
    have hkle : k ≤ cnt := Nat.le_of_lt_succ hk'
    cases lt_or_eq_of_le hkle with
    | inl hkcnt =>
        have hk0 : k < idxs0.size := by simpa [hsz0] using hkcnt
        have hkEq : idxs[k]! = idxs0[k]! := by simpa [idxs] using push_getBang_lt hk0
        have : idxs0[k]! < position.size := hrng0 k hk0
        simpa [hkEq] using this
    | inr hkeq =>
        have hlast : idxs[cnt]! = i := by simpa [idxs, hsz0] using push_getBang_eq
        simpa [hkeq, hlast] using a_7

  · -- pairwise distances
    intro p q hpq hq
    have hq' : q < cnt + 1 := by
      simpa [idxs, hsz0, Array.size_push, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hq
    have hqle : q ≤ cnt := Nat.le_of_lt_succ hq'
    cases lt_or_eq_of_le hqle with
    | inl hqcnt =>
        have hp_cnt : p < cnt := Nat.lt_trans hpq hqcnt
        have hp0 : p < idxs0.size := by simpa [hsz0] using hp_cnt
        have hq0 : q < idxs0.size := by simpa [hsz0] using hqcnt
        have hbase : (lo + hi + 1) / 2 ≤ position[idxs0[q]!]! - position[idxs0[p]!]! := hdist0 p q hpq hq0
        simpa [idxs, push_getBang_lt hp0, push_getBang_lt hq0] using hbase
    | inr hqeq =>
        have hp_lt_cnt : p < cnt := Nat.lt_of_lt_of_le hpq (by simpa [hqeq] using hqle)
        have hp0 : p < idxs0.size := by simpa [hsz0] using hp_lt_cnt
        have hlast : idxs[cnt]! = i := by simpa [idxs, hsz0] using push_getBang_eq
        have hpEq : idxs[p]! = idxs0[p]! := by simpa [idxs] using push_getBang_lt hp0
        rcases require_1 with ⟨hm2, hm_le, posStrict⟩
        have hpred_lt_cnt : cnt - 1 < cnt := by
          have : cnt - 1 < (cnt - 1) + 1 := Nat.lt_succ_self (cnt - 1)
          simpa [Nat.sub_add_cancel a_4, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
        have hlastBound : cnt - 1 < idxs0.size := by simpa [hsz0] using hpred_lt_cnt
        have hpos_le : position[idxs0[p]!]! ≤ lastPos := by
          by_cases hpc : p = cnt - 1
          · subst hpc
            simpa [hlastPos]
          ·
            have hp_le : p ≤ cnt - 1 := Nat.le_pred_of_lt hp_lt_cnt
            have hp_lt : p < cnt - 1 := lt_of_le_of_ne hp_le hpc
            have hidx_lt : idxs0[p]! < idxs0[cnt - 1]! := hinc0 p (cnt - 1) hp_lt hlastBound
            have hjpos : idxs0[cnt - 1]! < position.size := hrng0 (cnt - 1) hlastBound
            have hpos_lt : position[idxs0[p]!]! < position[idxs0[cnt - 1]!]! := posStrict _ _ hidx_lt hjpos
            have : position[idxs0[p]!]! ≤ position[idxs0[cnt - 1]!]! := Nat.le_of_lt hpos_lt
            simpa [hlastPos] using this
        have hsub : position[i]! - lastPos ≤ position[i]! - position[idxs0[p]!]! := by
          -- subtraction is antitone in the second argument
          simpa [Nat.sub_eq] using (Nat.sub_le_sub_left hpos_le (position[i]!))
        have : (lo + hi + 1) / 2 ≤ position[i]! - position[idxs0[p]!]! := le_trans if_pos_1 hsub
        simpa [hqeq, hlast, hpEq] using this

  · -- idxs[cnt]! < i + 1
    have hlast : idxs[cnt]! = i := by
      simpa [idxs, hsz0] using push_getBang_eq
    simpa [hlast] using (Nat.lt_succ_self i)

  · -- position[i]! = position[idxs[cnt]!]!
    have hlast : idxs[cnt]! = i := by
      simpa [idxs, hsz0] using push_getBang_eq
    simp [hlast]

theorem goal_1
    (position : Array ℕ)
    (m : ℕ)
    (hi : ℕ)
    (lo : ℕ)
    (cnt : ℕ)
    (i : ℕ)
    (invariant_gr_no_more_prefix : ∀ (idxs2 : Array ℕ), cnt < idxs2.size → (∀ (i j : ℕ), i < j → j < idxs2.size → idxs2[i]! < idxs2[j]!) → (∀ k < idxs2.size, idxs2[k]! < position.size) → (∀ (i j : ℕ), i < j → j < idxs2.size → (lo + hi + OfNat.ofNat 1) / OfNat.ofNat 2 ≤ position[idxs2[j]!]! - position[idxs2[i]!]!) → i ≤ idxs2[cnt]!)
    (require_1 : OfNat.ofNat 2 ≤ m ∧ m ≤ position.size ∧ ∀ (i j : ℕ), i < j → j < position.size → position[i]! < position[j]!)
    : ∀ (idxs2 : Array ℕ), cnt + OfNat.ofNat 1 < idxs2.size → (∀ (i j : ℕ), i < j → j < idxs2.size → idxs2[i]! < idxs2[j]!) → (∀ k < idxs2.size, idxs2[k]! < position.size) → (∀ (i j : ℕ), i < j → j < idxs2.size → (lo + hi + OfNat.ofNat 1) / OfNat.ofNat 2 ≤ position[idxs2[j]!]! - position[idxs2[i]!]!) → position[i]! ≤ position[idxs2[cnt]!]! := by
  intro idxs2 hsz hidxs2_inc hidxs2_range hidxs2_dist
  have hsz' : Nat.succ cnt < idxs2.size := by
    simpa [Nat.succ_eq_add_one] using hsz
  have hcnt_lt : cnt < idxs2.size := Nat.lt_trans (Nat.lt_succ_self cnt) hsz'
  have hle_idx : i ≤ idxs2[cnt]! :=
    invariant_gr_no_more_prefix idxs2 hcnt_lt hidxs2_inc hidxs2_range hidxs2_dist
  rcases require_1 with ⟨_, _, hpos_strict⟩
  have hj_range : idxs2[cnt]! < position.size := hidxs2_range cnt hcnt_lt
  cases lt_or_eq_of_le hle_idx with
  | inl hlt =>
      exact le_of_lt (hpos_strict i (idxs2[cnt]!) hlt hj_range)
  | inr heq =>
      simpa [heq]

theorem goal_2
    (position : Array ℕ)
    (hi : ℕ)
    (lo : ℕ)
    (a : lo ≤ hi)
    (cnt : ℕ)
    (i : ℕ)
    (invariant_gr_no_more_prefix : ∀ (idxs2 : Array ℕ), cnt < idxs2.size → (∀ (i j : ℕ), i < j → j < idxs2.size → idxs2[i]! < idxs2[j]!) → (∀ k < idxs2.size, idxs2[k]! < position.size) → (∀ (i j : ℕ), i < j → j < idxs2.size → (lo + hi + OfNat.ofNat 1) / OfNat.ofNat 2 ≤ position[idxs2[j]!]! - position[idxs2[i]!]!) → i ≤ idxs2[cnt]!)
    : ∀ (idxs2 : Array ℕ), cnt + OfNat.ofNat 1 < idxs2.size → (∀ (i j : ℕ), i < j → j < idxs2.size → idxs2[i]! < idxs2[j]!) → (∀ k < idxs2.size, idxs2[k]! < position.size) → (∀ (i j : ℕ), i < j → j < idxs2.size → (lo + hi + OfNat.ofNat 1) / OfNat.ofNat 2 ≤ position[idxs2[j]!]! - position[idxs2[i]!]!) → i + OfNat.ofNat 1 ≤ idxs2[cnt + OfNat.ofNat 1]! := by
  intro idxs2 hsz hSI hIR hPD
  have hcnt : cnt < idxs2.size := by
    -- cnt < cnt+1 < size
    exact Nat.lt_trans (Nat.lt_succ_self cnt) hsz

  have hi_le : i ≤ idxs2[cnt]! :=
    invariant_gr_no_more_prefix idxs2 hcnt hSI (by
      intro k hk
      exact hIR k hk
    ) (by
      intro i' j' hij hj
      exact hPD i' j' hij hj
    )

  have hlt : idxs2[cnt]! < idxs2[cnt + 1]! := by
    have hcc : cnt < cnt + 1 := Nat.lt_succ_self cnt
    exact hSI cnt (cnt + 1) hcc hsz

  have hstep : idxs2[cnt]! + 1 ≤ idxs2[cnt + 1]! := by
    -- succ a ≤ b from a < b
    simpa [Nat.succ_eq_add_one] using (Nat.succ_le_of_lt hlt)

  have h1 : i + 1 ≤ idxs2[cnt]! + 1 := by
    simpa [Nat.succ_eq_add_one] using (Nat.succ_le_succ hi_le)

  -- combine
  exact Nat.le_trans h1 hstep

theorem goal_3
    (position : Array ℕ)
    (hi : ℕ)
    (lo : ℕ)
    (cnt : ℕ)
    (i : ℕ)
    (lastPos : ℕ)
    (a_4 : OfNat.ofNat 1 ≤ cnt)
    (invariant_gr_min_extend_prefix : ∀ (idxs2 : Array ℕ), cnt < idxs2.size → (∀ (i j : ℕ), i < j → j < idxs2.size → idxs2[i]! < idxs2[j]!) → (∀ k < idxs2.size, idxs2[k]! < position.size) → (∀ (i j : ℕ), i < j → j < idxs2.size → (lo + hi + OfNat.ofNat 1) / OfNat.ofNat 2 ≤ position[idxs2[j]!]! - position[idxs2[i]!]!) → lastPos ≤ position[idxs2[cnt - OfNat.ofNat 1]!]!)
    (invariant_gr_no_more_prefix : ∀ (idxs2 : Array ℕ), cnt < idxs2.size → (∀ (i j : ℕ), i < j → j < idxs2.size → idxs2[i]! < idxs2[j]!) → (∀ k < idxs2.size, idxs2[k]! < position.size) → (∀ (i j : ℕ), i < j → j < idxs2.size → (lo + hi + OfNat.ofNat 1) / OfNat.ofNat 2 ≤ position[idxs2[j]!]! - position[idxs2[i]!]!) → i ≤ idxs2[cnt]!)
    (if_neg : position[i]! - lastPos < (lo + hi + OfNat.ofNat 1) / OfNat.ofNat 2)
    : ∀ (idxs2 : Array ℕ), cnt < idxs2.size → (∀ (i j : ℕ), i < j → j < idxs2.size → idxs2[i]! < idxs2[j]!) → (∀ k < idxs2.size, idxs2[k]! < position.size) → (∀ (i j : ℕ), i < j → j < idxs2.size → (lo + hi + OfNat.ofNat 1) / OfNat.ofNat 2 ≤ position[idxs2[j]!]! - position[idxs2[i]!]!) → i + OfNat.ofNat 1 ≤ idxs2[cnt]! := by
  intro idxs2 hcnt hSI hRange hDist

  have hi_le : i ≤ idxs2[cnt]! :=
    invariant_gr_no_more_prefix idxs2 hcnt hSI hRange hDist

  have hlast_le : lastPos ≤ position[idxs2[cnt - 1]!]! :=
    invariant_gr_min_extend_prefix idxs2 hcnt hSI hRange hDist

  have hne : idxs2[cnt]! ≠ i := by
    intro hEq
    have hcnt0 : cnt ≠ 0 := by
      have : 0 < cnt := lt_of_lt_of_le Nat.zero_lt_one a_4
      exact Nat.ne_of_gt this
    have hltcnt : cnt - 1 < cnt := Nat.sub_one_lt hcnt0

    have hmid_le :
        (lo + hi + 1) / 2 ≤ position[idxs2[cnt]!]! - position[idxs2[cnt - 1]!]! :=
      hDist (cnt - 1) cnt hltcnt hcnt

    have hmid_le' : (lo + hi + 1) / 2 ≤ position[i]! - position[idxs2[cnt - 1]!]! := by
      simpa [hEq] using hmid_le

    have hsub_le : position[i]! - position[idxs2[cnt - 1]!]! ≤ position[i]! - lastPos :=
      Nat.sub_le_sub_left hlast_le (position[i]!)

    have hge : (lo + hi + 1) / 2 ≤ position[i]! - lastPos :=
      le_trans hmid_le' hsub_le

    exact (Nat.not_lt_of_ge hge) if_neg

  have hlt : i < idxs2[cnt]! :=
    lt_of_le_of_ne hi_le (Ne.symm hne)

  simpa [Nat.succ_eq_add_one] using (Nat.succ_le_of_lt hlt)

theorem goal_4
    (position : Array ℕ)
    (m : ℕ)
    (hi : ℕ)
    (lo : ℕ)
    (require_1 : OfNat.ofNat 2 ≤ m ∧ m ≤ position.size ∧ ∀ (i j : ℕ), i < j → j < position.size → position[i]! < position[j]!)
    : ∃ (idxs : Array ℕ), idxs.size = OfNat.ofNat 1 ∧ (∀ (i j : ℕ), i < j → j < idxs.size → idxs[i]! < idxs[j]!) ∧ (∀ k < idxs.size, idxs[k]! < position.size) ∧ (∀ (i j : ℕ), i < j → j < idxs.size → (lo + hi + OfNat.ofNat 1) / OfNat.ofNat 2 ≤ position[idxs[j]!]! - position[idxs[i]!]!) ∧ idxs[OfNat.ofNat 0]! = OfNat.ofNat 0 ∧ position[OfNat.ofNat 0]! = position[idxs[OfNat.ofNat 0]!]! := by
  classical
  -- Use the singleton index array.
  refine ⟨#[0], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · intro i j hij hj
    -- `j < 1` is impossible together with `i < j`.
    have hj0 : j = 0 := (Nat.lt_one_iff.mp (by simpa using hj))
    subst hj0
    exact (False.elim ((Nat.not_lt_zero i) (by simpa using hij)))
  · intro k hk
    -- Only `k = 0` is possible.
    have hk0 : k = 0 := (Nat.lt_one_iff.mp (by simpa using hk))
    subst hk0
    -- From `2 ≤ m ≤ position.size` we get `0 < position.size`.
    have hpos : 0 < position.size := by
      have h2 : (2 : Nat) ≤ position.size := le_trans require_1.1 require_1.2.1
      exact lt_of_lt_of_le (by decide : (0 : Nat) < 2) h2
    simpa using hpos
  · intro i j hij hj
    have hj0 : j = 0 := (Nat.lt_one_iff.mp (by simpa using hj))
    subst hj0
    exact (False.elim ((Nat.not_lt_zero i) (by simpa using hij)))
  · simp
  · simp

theorem goal_5
    (position : Array ℕ)
    (m : ℕ)
    (hi : ℕ)
    (lo : ℕ)
    (require_1 : OfNat.ofNat 2 ≤ m ∧ m ≤ position.size ∧ ∀ (i j : ℕ), i < j → j < position.size → position[i]! < position[j]!)
    : ∀ (idxs2 : Array ℕ), OfNat.ofNat 1 < idxs2.size → (∀ (i j : ℕ), i < j → j < idxs2.size → idxs2[i]! < idxs2[j]!) → (∀ k < idxs2.size, idxs2[k]! < position.size) → (∀ (i j : ℕ), i < j → j < idxs2.size → (lo + hi + OfNat.ofNat 1) / OfNat.ofNat 2 ≤ position[idxs2[j]!]! - position[idxs2[i]!]!) → position[OfNat.ofNat 0]! ≤ position[idxs2[OfNat.ofNat 0]!]! := by
  intro idxs2 hsz _hincIdxs2 hRangeIdxs2 _hdist
  have h0lt : 0 < idxs2.size := Nat.lt_trans Nat.zero_lt_one hsz
  have hidx0_lt : idxs2[0]! < position.size := hRangeIdxs2 0 h0lt
  obtain ⟨_hm2, _hmpos, hposInc⟩ := require_1
  by_cases h0 : idxs2[0]! = 0
  · simp [h0]
  · have h0pos : 0 < idxs2[0]! := Nat.pos_of_ne_zero h0
    have hlt : position[0]! < position[idxs2[0]!]! := hposInc 0 (idxs2[0]!) h0pos hidx0_lt
    exact Nat.le_of_lt hlt

theorem goal_6
    (position : Array ℕ)
    (hi : ℕ)
    (lo : ℕ)
    : ∀ (idxs2 : Array ℕ), OfNat.ofNat 1 < idxs2.size → (∀ (i j : ℕ), i < j → j < idxs2.size → idxs2[i]! < idxs2[j]!) → (∀ k < idxs2.size, idxs2[k]! < position.size) → (∀ (i j : ℕ), i < j → j < idxs2.size → (lo + hi + OfNat.ofNat 1) / OfNat.ofNat 2 ≤ position[idxs2[j]!]! - position[idxs2[i]!]!) → OfNat.ofNat 1 ≤ idxs2[OfNat.ofNat 1]! := by
  intro idxs2 hsz hinc _ _
  have h01 : idxs2[0]! < idxs2[1]! := by
    have h0 : (0 : ℕ) < 1 := by decide
    -- `hsz : 1 < idxs2.size` is exactly what we need for `j < idxs2.size` with `j = 1`.
    simpa using (hinc 0 1 h0 hsz)
  have hpos : (0 : ℕ) < idxs2[1]! := by
    exact lt_of_le_of_lt (Nat.zero_le idxs2[0]!) h01
  -- `0 < n` is equivalent to `1 ≤ n` for naturals.
  have : (1 : ℕ) ≤ idxs2[1]! := (Nat.succ_le_iff).2 hpos
  simpa using this

theorem goal_7
    (position : Array ℕ)
    (m : ℕ)
    (hi : ℕ)
    (lo : ℕ)
    (if_pos : lo < hi)
    (i_1 : ℕ)
    (i_2 : ℕ)
    (invariant_gr_no_more_prefix : ∀ (idxs2 : Array ℕ), i_1 < idxs2.size → (∀ (i j : ℕ), i < j → j < idxs2.size → idxs2[i]! < idxs2[j]!) → (∀ k < idxs2.size, idxs2[k]! < position.size) → (∀ (i j : ℕ), i < j → j < idxs2.size → (lo + hi + OfNat.ofNat 1) / OfNat.ofNat 2 ≤ position[idxs2[j]!]! - position[idxs2[i]!]!) → i_2 ≤ idxs2[i_1]!)
    (if_neg : i_1 < m)
    (done_2 : i_2 < position.size → m ≤ i_1)
    : ∀ (x : Array ℕ), x.size = m → (∀ (i j : ℕ), i < j → j < x.size → x[i]! < x[j]!) → (∀ k < x.size, x[k]! < position.size) → ∃ (x_1 : ℕ) (x_2 : ℕ), x_1 < x_2 ∧ x_2 < x.size ∧ position[x[x_2]!]! - position[x[x_1]!]! < (lo + hi + OfNat.ofNat 1) / OfNat.ofNat 2 - OfNat.ofNat 1 + OfNat.ofNat 1 := by
  classical
  intro x hxsize hxincr hxrange

  -- mid = upper mid used by the binary search
  set mid : Nat := (lo + hi + 1) / 2

  have hi2_not_lt : ¬ i_2 < position.size := by
    intro hi2lt
    have hmle : m ≤ i_1 := done_2 hi2lt
    exact (Nat.not_le_of_lt if_neg) hmle

  have hposle_i2 : position.size ≤ i_2 := Nat.le_of_not_lt hi2_not_lt

  have hmid_pos : 0 < mid := by
    have hhi : 0 < hi := lt_of_le_of_lt (Nat.zero_le lo) if_pos
    have h1le_hi : 1 ≤ hi := Nat.succ_le_iff.2 hhi
    have h2le_hi1 : 2 ≤ hi + 1 := by
      -- 2 = 1+1
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (Nat.add_le_add_right h1le_hi 1)
    have hhi1_le_sum : hi + 1 ≤ lo + hi + 1 := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (Nat.add_le_add_right (Nat.zero_le lo) (hi + 1))
    have h2le_sum : 2 ≤ lo + hi + 1 := le_trans h2le_hi1 hhi1_le_sum
    have : 0 < (lo + hi + 1) / 2 := Nat.div_pos h2le_sum (by decide : 0 < (2:Nat))
    simpa [mid] using this

  have hmid_sub_add : mid - 1 + 1 = mid := by
    simpa [Nat.add_assoc] using (Nat.sub_one_add_one_eq_of_pos hmid_pos)

  have hex : ∃ (x_1 : ℕ) (x_2 : ℕ),
      x_1 < x_2 ∧ x_2 < x.size ∧
        position[x[x_2]!]! - position[x[x_1]!]! < mid := by
    by_contra h
    have hGE : ∀ (i j : ℕ), i < j → j < x.size →
        mid ≤ position[x[j]!]! - position[x[i]!]! := by
      intro i j hij hj
      by_contra hle
      have hlt : position[x[j]!]! - position[x[i]!]! < mid :=
        Nat.lt_of_not_ge hle
      exact h ⟨i, j, hij, hj, hlt⟩

    have hi1lt : i_1 < x.size := lt_of_lt_of_eq if_neg hxsize.symm

    have hineq : i_2 ≤ x[i_1]! :=
      invariant_gr_no_more_prefix x hi1lt hxincr hxrange hGE

    have hxidx : x[i_1]! < position.size := hxrange i_1 hi1lt
    have hposle_xi1 : position.size ≤ x[i_1]! := le_trans hposle_i2 hineq

    exact (Nat.not_lt_of_ge hposle_xi1) hxidx

  rcases hex with ⟨x_1, x_2, hx12, hx2lt, hdiff⟩
  refine ⟨x_1, x_2, hx12, hx2lt, ?_⟩
  -- rewrite the bound `mid - 1 + 1` back to `mid`
  simpa [mid, hmid_sub_add] using hdiff

theorem goal_8
    (position : Array ℕ)
    (m : ℕ)
    (require_1 : OfNat.ofNat 2 ≤ m ∧ m ≤ position.size ∧ ∀ (i j : ℕ), i < j → j < position.size → position[i]! < position[j]!)
    : ∃ (idxs : Array ℕ), idxs.size = m ∧ (∀ (i j : ℕ), i < j → j < idxs.size → idxs[i]! < idxs[j]!) ∧ ∀ k < idxs.size, idxs[k]! < position.size := by
  rcases require_1 with ⟨hm2, hmle, hpos⟩
  refine ⟨Array.range m, ?_, ?_, ?_⟩
  · simp [Array.size_range]
  · intro i j hij hj
    have hi : i < (Array.range m).size := lt_trans hij hj
    have hi_m : i < m := by simpa [Array.size_range] using hi
    have hj_m : j < m := by simpa [Array.size_range] using hj
    have hgi : (Array.range m)[i]! = i := by
      simp [Array.getElem!_eq_getD, Array.getD, Array.getElem?_range, hi_m]
    have hgj : (Array.range m)[j]! = j := by
      simp [Array.getElem!_eq_getD, Array.getD, Array.getElem?_range, hj_m]
    simpa [hgi, hgj] using hij
  · intro k hk
    have hk_m : k < m := by simpa [Array.size_range] using hk
    have hkg : (Array.range m)[k]! = k := by
      simp [Array.getElem!_eq_getD, Array.getD, Array.getElem?_range, hk_m]
    have : k < position.size := lt_of_lt_of_le hk_m hmle
    simpa [hkg] using this

theorem goal_9
    (position : Array ℕ)
    (m : ℕ)
    (require_1 : OfNat.ofNat 2 ≤ m ∧ m ≤ position.size ∧ ∀ (i j : ℕ), i < j → j < position.size → position[i]! < position[j]!)
    : ∀ (x : Array ℕ), x.size = m → (∀ (i j : ℕ), i < j → j < x.size → x[i]! < x[j]!) → (∀ k < x.size, x[k]! < position.size) → ∃ (x_1 : ℕ) (x_2 : ℕ), x_1 < x_2 ∧ x_2 < x.size ∧ position[x[x_2]!]! - position[x[x_1]!]! < position[position.size - OfNat.ofNat 1]! - position[OfNat.ofNat 0]! + OfNat.ofNat 1 := by
  intro x hx _hxInc hxRange

  have hm2 : (2:Nat) ≤ m := require_1.1
  have hm_le : m ≤ position.size := require_1.2.1
  have hposStrict : ∀ (i j : ℕ), i < j → j < position.size → position[i]! < position[j]! := require_1.2.2

  have hposSize2 : (2:Nat) ≤ position.size := le_trans hm2 hm_le
  have hxSize2 : (2:Nat) ≤ x.size := by simpa [hx] using hm2

  have hx1lt : (1:Nat) < x.size :=
    lt_of_lt_of_le (by decide : (1:Nat) < 2) hxSize2
  have hx0lt : (0:Nat) < x.size :=
    lt_of_lt_of_le (by decide : (0:Nat) < 2) hxSize2

  refine ⟨0, 1, ?_⟩
  constructor
  · decide
  constructor
  · exact hx1lt

  -- Monotonicity of `position` derived from strict increase.
  have hmono : ∀ {i j : Nat}, i ≤ j → j < position.size → position[i]! ≤ position[j]! := by
    intro i j hij hj
    rcases lt_or_eq_of_le hij with hijlt | rfl
    · exact le_of_lt (hposStrict i j hijlt hj)
    · exact le_rfl

  have hidx0 : x[0]! < position.size := hxRange 0 hx0lt
  have hidx1 : x[1]! < position.size := hxRange 1 hx1lt

  have hsize_ne0 : position.size ≠ 0 := by
    exact Nat.ne_of_gt (lt_of_lt_of_le (by decide : (0:Nat) < 2) hposSize2)

  have hlast_lt : position.size - 1 < position.size := Nat.sub_one_lt hsize_ne0

  have hpred_eq : Nat.pred position.size = position.size - 1 := by
    cases position.size <;> rfl

  have hidx1le_last : x[1]! ≤ position.size - 1 := by
    have hlePred : x[1]! ≤ Nat.pred position.size := Nat.le_pred_of_lt hidx1
    simpa [hpred_eq] using hlePred

  have hpos0le : position[0]! ≤ position[x[0]!]! := hmono (Nat.zero_le _) hidx0
  have hpos1le_last : position[x[1]!]! ≤ position[position.size - 1]! :=
    hmono hidx1le_last hlast_lt

  have hleA : position[x[1]!]! - position[x[0]!]! ≤ position[position.size - 1]! - position[x[0]!]! := by
    exact Nat.sub_le_sub_right hpos1le_last _

  have hleB : position[position.size - 1]! - position[x[0]!]! ≤ position[position.size - 1]! - position[0]! := by
    simpa using (Nat.sub_le_sub_left hpos0le (position[position.size - 1]!))

  have hle : position[x[1]!]! - position[x[0]!]! ≤ position[position.size - 1]! - position[0]! :=
    le_trans hleA hleB

  have hlt : position[x[1]!]! - position[x[0]!]! < Nat.succ (position[position.size - 1]! - position[0]!) :=
    Nat.lt_succ_of_le hle

  simpa [Nat.succ_eq_add_one] using hlt

theorem goal_10
    (position : Array ℕ)
    (m : ℕ)
    (require_1 : OfNat.ofNat 2 ≤ m ∧ m ≤ position.size ∧ ∀ (i j : ℕ), i < j → j < position.size → position[i]! < position[j]!)
    : ∀ (d1 d2 : ℕ), d1 ≤ d2 → ∀ (x : Array ℕ), x.size = m → (∀ (i j : ℕ), i < j → j < x.size → x[i]! < x[j]!) → (∀ k < x.size, x[k]! < position.size) → (∀ (i j : ℕ), i < j → j < x.size → d2 ≤ position[x[j]!]! - position[x[i]!]!) → ∃ (idxs : Array ℕ), idxs.size = m ∧ (∀ (i j : ℕ), i < j → j < idxs.size → idxs[i]! < idxs[j]!) ∧ (∀ k < idxs.size, idxs[k]! < position.size) ∧ ∀ (i j : ℕ), i < j → j < idxs.size → d1 ≤ position[idxs[j]!]! - position[idxs[i]!]! := by
    intros; expose_names; try simp_all; try grind

theorem goal_11
    (position : Array ℕ)
    (m : ℕ)
    (i : ℕ)
    (lo_1 : ℕ)
    (invariant_bs_lo_feasible : ∃ (idxs : Array ℕ), idxs.size = m ∧ (∀ (i j : ℕ), i < j → j < idxs.size → idxs[i]! < idxs[j]!) ∧ (∀ k < idxs.size, idxs[k]! < position.size) ∧ ∀ (i j : ℕ), i < j → j < idxs.size → lo_1 ≤ position[idxs[j]!]! - position[idxs[i]!]!)
    (a : lo_1 ≤ i)
    (invariant_bs_mono : ∀ (d1 d2 : ℕ), d1 ≤ d2 → ∀ (x : Array ℕ), x.size = m → (∀ (i j : ℕ), i < j → j < x.size → x[i]! < x[j]!) → (∀ k < x.size, x[k]! < position.size) → (∀ (i j : ℕ), i < j → j < x.size → d2 ≤ position[x[j]!]! - position[x[i]!]!) → ∃ (idxs : Array ℕ), idxs.size = m ∧ (∀ (i j : ℕ), i < j → j < idxs.size → idxs[i]! < idxs[j]!) ∧ (∀ k < idxs.size, idxs[k]! < position.size) ∧ ∀ (i j : ℕ), i < j → j < idxs.size → d1 ≤ position[idxs[j]!]! - position[idxs[i]!]!)
    (invariant_bs_hi1_infeasible : ∀ (x : Array ℕ), x.size = m → (∀ (i j : ℕ), i < j → j < x.size → x[i]! < x[j]!) → (∀ k < x.size, x[k]! < position.size) → ∃ (x_1 : ℕ) (x_2 : ℕ), x_1 < x_2 ∧ x_2 < x.size ∧ position[x[x_2]!]! - position[x[x_1]!]! < i + OfNat.ofNat 1)
    (done_1 : i ≤ lo_1)
    : postcondition position m lo_1 := by
  have hlo : lo_1 = i := Nat.le_antisymm a done_1

  have hFeasLo : Feasible position m lo_1 := by
    simpa [Feasible, StrictlyIncreasing, IndicesInRange, PairwiseDistGE] using
      invariant_bs_lo_feasible

  have hNotFeasSucc : ¬ Feasible position m (i + 1) := by
    intro hF
    rcases hF with ⟨x, hxsize, hxinc, hxrange, hxdist⟩
    have hxinc' : (∀ (i j : ℕ), i < j → j < x.size → x[i]! < x[j]!) := by
      simpa [StrictlyIncreasing] using hxinc
    have hxrange' : (∀ k < x.size, x[k]! < position.size) := by
      simpa [IndicesInRange] using hxrange
    rcases invariant_bs_hi1_infeasible x hxsize hxinc' hxrange' with
      ⟨x1, x2, hx12, hx2lt, hlt⟩
    have hge : i + 1 ≤ position[x[x2]!]! - position[x[x1]!]! := by
      simpa [PairwiseDistGE] using hxdist x1 x2 hx12 hx2lt
    exact (Nat.not_lt_of_ge hge) (by simpa using hlt)

  constructor
  · exact hFeasLo
  · intro d' hd'
    have hi_lt : i < d' := by
      simpa [hlo] using hd'
    have hsuc : i + 1 ≤ d' := Nat.succ_le_of_lt hi_lt
    intro hFd'
    -- derive feasibility at (i+1) from feasibility at d' using monotonicity
    rcases hFd' with ⟨x, hxsize, hxinc, hxrange, hxdist⟩
    have hxinc' : (∀ (i j : ℕ), i < j → j < x.size → x[i]! < x[j]!) := by
      simpa [StrictlyIncreasing] using hxinc
    have hxrange' : (∀ k < x.size, x[k]! < position.size) := by
      simpa [IndicesInRange] using hxrange
    have hxdist' : (∀ (i j : ℕ), i < j → j < x.size → d' ≤ position[x[j]!]! - position[x[i]!]!) := by
      simpa [PairwiseDistGE] using hxdist

    rcases invariant_bs_mono (i + 1) d' hsuc x hxsize hxinc' hxrange' hxdist' with
      ⟨idxs, hsz, hinc, hrange, hdist⟩

    have hFeasSucc : Feasible position m (i + 1) := by
      refine ⟨idxs, hsz, ?_, ?_, ?_⟩
      · exact (by simpa [StrictlyIncreasing] using hinc)
      · exact (by simpa [IndicesInRange] using hrange)
      · exact (by
          -- `hdist` is already in the expanded form of `PairwiseDistGE`
          simpa [PairwiseDistGE] using hdist)

    exact hNotFeasSucc hFeasSucc

set_option loom.solver "custom"

macro_rules
| `(tactic|loom_solver) => `(tactic|(
  try injections
  try subst_vars
  try grind (gen := 1)))


prove_correct MagneticForceBetweenTwoBalls by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at *); try (conv => congr <;> simp) ; try expose_names)
  exact (goal_0 position m hi lo cnt i lastPos a_4 invariant_gr_witness a_7 if_pos_1 require_1)
  exact (goal_1 position m hi lo cnt i invariant_gr_no_more_prefix require_1)
  exact (goal_2 position hi lo a cnt i invariant_gr_no_more_prefix)
  exact (goal_3 position hi lo cnt i lastPos a_4 invariant_gr_min_extend_prefix invariant_gr_no_more_prefix if_neg)
  exact (goal_4 position m hi lo require_1)
  exact (goal_5 position m hi lo require_1)
  exact (goal_6 position hi lo)
  exact (goal_7 position m hi lo if_pos i_1 i_2 invariant_gr_no_more_prefix if_neg done_2)
  exact (goal_8 position m require_1)
  exact (goal_9 position m require_1)
  exact (goal_10 position m require_1)
  exact (goal_11 position m i lo_1 invariant_bs_lo_feasible a invariant_bs_mono invariant_bs_hi1_infeasible done_1)
end Proof
