import Velvet.Std
import Extensions.Tactics
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false
set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

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

section Specs
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
method MaxProfit (prices : Array Nat)
  return (result : Nat)
  require precondition prices
  ensures postcondition prices result
  do
  -- placeholder implementation
  pure 0

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
