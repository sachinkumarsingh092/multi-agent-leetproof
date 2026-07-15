import Lean
import Mathlib.Tactic
import Velvet.Std

set_option maxHeartbeats 10000000

section Specs
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false

/- Problem Description
    121. Best Time to Buy and Sell Stock: compute the maximum profit from one buy then one later sell.
    **Important: complexity should be O(n) time and O(1) space**
    Natural language breakdown:
    1. Input is an array `prices` where `prices[i]` is the stock price on day `i`.
    2. We may choose at most one transaction consisting of buying on a day `i` and selling on a later day `j`.
    3. The buy day must be strictly before the sell day (i < j).
    4. The profit of choosing days (i,j) is `prices[j] - prices[i]`.
    5. If the profit would be negative, we treat it as 0 by returning the maximum profit over all valid pairs,
       and returning 0 when no profitable transaction exists.
    6. If there are fewer than two days (array length < 2), no transaction is possible and the answer is 0.
-/

-- Profit of buying at day i and selling at day j, using Nat subtraction.
-- This matches the problem rule that we never return a negative profit.
def pairProfit (prices : Array Nat) (i : Nat) (j : Nat) : Nat :=
  prices[j]! - prices[i]!

-- A predicate stating that (i,j) is a valid buy/sell pair.
def ValidPair (prices : Array Nat) (i : Nat) (j : Nat) : Prop :=
  i < j ∧ j < prices.size

-- Preconditions: none (all arrays of Nat are allowed, including empty and singleton).
def precondition (prices : Array Nat) : Prop :=
  True

-- Postconditions:
-- 1. result is an upper bound on all valid pair profits.
-- 2. if there exists any valid pair, then result is achieved by some valid pair.
--    (This makes the specification uniquely characterize the maximum.)
-- 3. if there is no valid pair (size < 2), the result must be 0.
-- 4. if there are valid pairs but all have zero profit, result must be 0 (follows from 1+2 but stated explicitly).

def postcondition (prices : Array Nat) (result : Nat) : Prop :=
  (∀ (i : Nat) (j : Nat), ValidPair prices i j → pairProfit prices i j ≤ result) ∧
  ((prices.size < 2) → result = 0) ∧
  ((prices.size ≥ 2) → (∃ (i : Nat) (j : Nat), ValidPair prices i j ∧ result = pairProfit prices i j))
end Specs

section Impl
def implementation (prices : Array Nat) : Nat :=
  if h : prices.size < 2 then
    0
  else
    -- single pass: maintain minimum price so far and best profit so far
    let rec go (i : Nat) (minSoFar : Nat) (best : Nat) : Nat :=
      if hi : i < prices.size then
        let p := prices[i]!
        let min' := Nat.min minSoFar p
        let best' := Nat.max best (p - minSoFar)
        go (i + 1) min' best'
      else
        best
    termination_by prices.size - i
    -- start with day 0 as initial min
    go 0 (prices[0]!) 0
end Impl

section TestCases
-- Test case 1: Example 1
-- prices = [7,1,5,3,6,4] => max profit = 5
-- buy at 1, sell at 6

def test1_prices : Array Nat := #[7, 1, 5, 3, 6, 4]

def test1_Expected : Nat := 5

-- Test case 2: Example 2
-- prices = [7,6,4,3,1] => 0

def test2_prices : Array Nat := #[7, 6, 4, 3, 1]

def test2_Expected : Nat := 0

-- Test case 3: Empty array (no transaction possible)

def test3_prices : Array Nat := #[]

def test3_Expected : Nat := 0

-- Test case 4: Singleton array (no transaction possible)

def test4_prices : Array Nat := #[5]

def test4_Expected : Nat := 0

-- Test case 5: Two days increasing

def test5_prices : Array Nat := #[1, 2]

def test5_Expected : Nat := 1

-- Test case 6: Two days decreasing

def test6_prices : Array Nat := #[2, 1]

def test6_Expected : Nat := 0

-- Test case 7: All equal prices

def test7_prices : Array Nat := #[3, 3, 3]

def test7_Expected : Nat := 0

-- Test case 8: Includes 0 and 1, best trade uses early 0 to later 3

def test8_prices : Array Nat := #[2, 0, 1, 3]

def test8_Expected : Nat := 3

-- Test case 9: Best sell not at last day
-- buy at 1, sell at 7 => profit 6

def test9_prices : Array Nat := #[4, 1, 7, 2, 5]

def test9_Expected : Nat := 6
end TestCases

section Assertions
-- Test case 1
#assert_same_evaluation #[(implementation test1_prices), test1_Expected]

-- Test case 2
#assert_same_evaluation #[(implementation test2_prices), test2_Expected]

-- Test case 3
#assert_same_evaluation #[(implementation test3_prices), test3_Expected]

-- Test case 4
#assert_same_evaluation #[(implementation test4_prices), test4_Expected]

-- Test case 5
#assert_same_evaluation #[(implementation test5_prices), test5_Expected]

-- Test case 6
#assert_same_evaluation #[(implementation test6_prices), test6_Expected]

-- Test case 7
#assert_same_evaluation #[(implementation test7_prices), test7_Expected]

-- Test case 8
#assert_same_evaluation #[(implementation test8_prices), test8_Expected]

-- Test case 9
#assert_same_evaluation #[(implementation test9_prices), test9_Expected]
end Assertions

section Proof
set_option maxHeartbeats 10000000

theorem correctness_goal
    (prices : Array Nat)
    (h_precond : precondition prices)
    : postcondition prices (implementation prices) := by
  unfold precondition at h_precond
  by_cases hsz : prices.size < 2
  ·
    have hno : ∀ (i j : Nat), ValidPair prices i j → False := by
      intro i j hv
      rcases hv with ⟨hij, hjs⟩
      have hj_succ_le : j.succ ≤ prices.size := Nat.succ_le_of_lt hjs
      have hi1 : (1 : Nat) ≤ i.succ := by
        simpa using (Nat.succ_le_succ (Nat.zero_le i))
      have hj_ge1 : (1 : Nat) ≤ j := le_trans hi1 (Nat.succ_le_of_lt hij)
      have h2_le_jsucc : (2 : Nat) ≤ j.succ := Nat.succ_le_succ hj_ge1
      have h2_le_size : (2 : Nat) ≤ prices.size := le_trans h2_le_jsucc hj_succ_le
      exact (Nat.not_lt_of_ge h2_le_size) hsz

    refine And.intro ?_ (And.intro ?_ ?_)
    · intro i j hv
      cases (hno i j hv)
    · intro _
      simp [implementation, hsz]
    · intro hs
      exfalso
      exact (Nat.not_lt_of_ge hs) hsz

  ·
    let MinInv (i minSoFar : Nat) : Prop :=
      (∃ minIdx : Nat, minIdx < i ∧ prices[minIdx]! = minSoFar) ∧
      (∀ k : Nat, k < i → minSoFar ≤ prices[k]!)
    let BestInv (i best : Nat) : Prop :=
      (∃ bi bj : Nat, bi < bj ∧ bj < i ∧ best = pairProfit prices bi bj) ∧
      (∀ a b : Nat, a < b → b < i → pairProfit prices a b ≤ best)

    let rec go_correct (i minSoFar best : Nat)
        (hi2 : 2 ≤ i) (hile : i ≤ prices.size)
        (hmin : MinInv i minSoFar) (hbest : BestInv i best)
        : (∀ a b : Nat, a < b → b < prices.size → pairProfit prices a b ≤ implementation.go prices i minSoFar best) ∧
          (∃ a b : Nat, ValidPair prices a b ∧ implementation.go prices i minSoFar best = pairProfit prices a b) := by
      by_cases hi : i < prices.size
      ·
        have hgo : implementation.go prices i minSoFar best =
            (let p := prices[i]!
             let min' := Nat.min minSoFar p
             let best' := Nat.max best (p - minSoFar)
             implementation.go prices (i+1) min' best') := by
          -- unfold only the outer call
          conv_lhs => unfold implementation.go
          simp [hi]

        have hile' : i.succ ≤ prices.size := Nat.succ_le_of_lt hi

        rcases hmin.1 with ⟨minIdx, hminIdxLt, hminIdxEq⟩
        have hminLe : ∀ k : Nat, k < i → minSoFar ≤ prices[k]! := hmin.2
        rcases hbest.1 with ⟨bi, bj, hbij, hbjLt, hbestEq⟩
        have hbestUB : ∀ a b : Nat, a < b → b < i → pairProfit prices a b ≤ best := hbest.2

        let p : Nat := prices[i]!
        let min' : Nat := Nat.min minSoFar p
        let bestCand : Nat := p - minSoFar
        let best' : Nat := Nat.max best bestCand

        have hmin' : MinInv i.succ min' := by
          constructor
          · have hcmp : minSoFar ≤ p ∨ p ≤ minSoFar := le_total minSoFar p
            cases hcmp with
            | inl hle =>
              refine ⟨minIdx, Nat.lt_trans hminIdxLt (Nat.lt_succ_self i), ?_⟩
              have : min' = minSoFar := by simp [min', Nat.min_eq_left hle]
              simpa [this, hminIdxEq]
            | inr hle =>
              refine ⟨i, Nat.lt_succ_self i, ?_⟩
              have : min' = p := by simp [min', Nat.min_eq_right hle]
              simpa [this, p]
          · intro k hk
            have hk' : k < i ∨ k = i := by
              have hkle : k ≤ i := Nat.le_of_lt_succ hk
              by_cases hki : k < i
              · exact Or.inl hki
              · have : i ≤ k := Nat.le_of_not_lt hki
                exact Or.inr (le_antisymm hkle this)
            cases hk' with
            | inl hki =>
              have : min' ≤ minSoFar := min_le_left _ _
              exact le_trans this (hminLe k hki)
            | inr hkeq =>
              cases hkeq
              have : min' ≤ p := min_le_right _ _
              simpa [p] using this

        have hbest' : BestInv i.succ best' := by
          constructor
          · by_cases hchoose : bestCand ≤ best
            · refine ⟨bi, bj, hbij, Nat.lt_trans hbjLt (Nat.lt_succ_self i), ?_⟩
              have : best' = best := by simp [best', Nat.max_eq_left hchoose]
              simpa [this, hbestEq]
            · have hbestLt : best < bestCand := lt_of_not_ge hchoose
              have hbestLe : best ≤ bestCand := le_of_lt hbestLt
              refine ⟨minIdx, i, hminIdxLt, Nat.lt_succ_self i, ?_⟩
              have : best' = bestCand := by simp [best', Nat.max_eq_right hbestLe]
              have hCandEq : bestCand = pairProfit prices minIdx i := by
                simp [bestCand, pairProfit, p, hminIdxEq]
              simpa [this, hCandEq]
          · intro a b hab hb
            have hb_cases : b < i ∨ b = i := by
              have hb_le : b ≤ i := Nat.le_of_lt_succ hb
              by_cases hbi : b < i
              · exact Or.inl hbi
              · have : i ≤ b := Nat.le_of_not_lt hbi
                exact Or.inr (le_antisymm hb_le this)
            cases hb_cases with
            | inl hbi =>
              have hle : pairProfit prices a b ≤ best := hbestUB a b hab hbi
              exact le_trans hle (Nat.le_max_left _ _)
            | inr hbeq =>
              cases hbeq
              have ha_lt : a < i := hab
              have hmin_le_ai : minSoFar ≤ prices[a]! := hminLe a ha_lt
              have hsub : pairProfit prices a i ≤ bestCand := by
                have : p - prices[a]! ≤ p - minSoFar := Nat.sub_le_sub_left hmin_le_ai p
                simpa [pairProfit, p, bestCand] using this
              have hleCand : bestCand ≤ best' := Nat.le_max_right _ _
              exact le_trans hsub hleCand

        have hrec := go_correct (i+1) min' best'
          (le_trans hi2 (Nat.le_succ i)) hile' hmin' hbest'

        constructor
        · intro a b hab hb
          have := hrec.1 a b hab hb
          simpa [hgo, p, min', best', bestCand] using this
        · rcases hrec.2 with ⟨a, b, hv, hEq⟩
          refine ⟨a, b, hv, ?_⟩
          simpa [hgo, p, min', best', bestCand] using hEq

      ·
        have hret : implementation.go prices i minSoFar best = best := by
          conv_lhs => unfold implementation.go
          simp [hi]
        constructor
        · intro a b hab hb
          have hsize_le : prices.size ≤ i := Nat.le_of_not_lt hi
          have hb' : b < i := Nat.lt_of_lt_of_le hb hsize_le
          have : pairProfit prices a b ≤ best := hbest.2 a b hab hb'
          simpa [hret] using this
        · rcases hbest.1 with ⟨bi, bj, hbij, hbjLt, hbestEq⟩
          have hsize_le : prices.size ≤ i := Nat.le_of_not_lt hi
          have hisize : i = prices.size := le_antisymm hile hsize_le
          refine ⟨bi, bj, ?_, ?_⟩
          · refine ⟨hbij, ?_⟩
            simpa [hisize] using hbjLt
          · exact hret.trans hbestEq
    termination_by prices.size - i

    have hsize2 : 2 ≤ prices.size := Nat.le_of_not_lt hsz
    have h0lt : 0 < prices.size := lt_of_lt_of_le (by decide : 0 < 2) hsize2
    have h1lt : 1 < prices.size := lt_of_lt_of_le (by decide : 1 < 2) hsize2

    have hunroll : implementation.go prices 0 (prices[0]!) 0 =
        implementation.go prices 2 (Nat.min (prices[0]!) (prices[1]!)) (prices[1]! - prices[0]!) := by
      -- step i=0
      conv_lhs => unfold implementation.go
      simp [h0lt]
      -- now goal is about go 1 ...; unfold just that head occurrence
      conv_lhs => unfold implementation.go
      simp [h1lt, Nat.max_eq_right (Nat.zero_le _)]

    have hmin2 : MinInv 2 (Nat.min (prices[0]!) (prices[1]!)) := by
      constructor
      · have hcmp : prices[0]! ≤ prices[1]! ∨ prices[1]! ≤ prices[0]! := le_total (prices[0]!) (prices[1]!)
        cases hcmp with
        | inl hle =>
          refine ⟨0, by decide, ?_⟩
          simp [Nat.min_eq_left hle]
        | inr hle =>
          refine ⟨1, by decide, ?_⟩
          simp [Nat.min_eq_right hle]
      · intro k hk
        cases k with
        | zero =>
          simpa using (min_le_left (prices[0]!) (prices[1]!))
        | succ k =>
          cases k with
          | zero =>
            simpa using (min_le_right (prices[0]!) (prices[[1]]!))
          | succ k =>
            have h2le : (2 : Nat) ≤ Nat.succ (Nat.succ k) :=
              Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le k))
            exact (Nat.not_lt_of_ge h2le) hk |>.elim

    have hbest2 : BestInv 2 (prices[1]! - prices[0]!) := by
      constructor
      · refine ⟨0, 1, by decide, by decide, ?_⟩
        simp [pairProfit]
      · intro a b hab hb
        cases b with
        | zero =>
          cases (Nat.not_lt_zero a hab)
        | succ b =>
          cases b with
          | zero =>
            have ha0 : a = 0 := by
              apply Nat.eq_zero_of_le_zero
              exact Nat.le_of_lt_succ hab
            cases ha0
            simp [pairProfit]
          | succ b =>
            have h2le : (2 : Nat) ≤ Nat.succ (Nat.succ b) :=
              Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le b))
            exact (Nat.not_lt_of_ge h2le) hb |>.elim

    have hgc := go_correct 2 (Nat.min (prices[0]!) (prices[1]!)) (prices[1]! - prices[0]!)
      (by decide) hsize2 hmin2 hbest2

    have hub : ∀ (i j : Nat), ValidPair prices i j → pairProfit prices i j ≤ implementation.go prices 0 (prices[0]!) 0 := by
      intro i j hv
      have hij : i < j := hv.1
      have hjs : j < prices.size := hv.2
      have hub2 := hgc.1 i j hij hjs
      simpa [hunroll] using hub2

    have hex : 2 ≤ prices.size →
        ∃ i j, ValidPair prices i j ∧ implementation.go prices 0 (prices[0]!) 0 = pairProfit prices i j := by
      intro _hs
      rcases hgc.2 with ⟨i, j, hv, hEq⟩
      refine ⟨i, j, hv, hunroll.trans hEq⟩

    simpa [implementation, hsz, postcondition] using (And.intro hub hex)
end Proof
