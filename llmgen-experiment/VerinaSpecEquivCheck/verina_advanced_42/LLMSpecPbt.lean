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
    MaxStockProfit: compute the maximum profit obtainable by buying one day and selling on a later day.
    Natural language breakdown:
    1. Input is a list of natural-number prices, where index order represents time order.
    2. A valid transaction chooses two indices i and j with i < j (buy before sell).
    3. The profit of transaction (i,j) is prices[j] - prices[i] using Nat subtraction (so negative profits count as 0).
    4. The output is the maximum profit over all valid transactions.
    5. If the list has fewer than two elements, no transaction is possible and the output must be 0.
    6. If all transactions yield 0 profit, the output is 0.
-/

section Specs
-- A realizable profit value from one buy/sell transaction.
def IsTransactionProfit (prices : List Nat) (p : Nat) : Prop :=
  ∃ (i : Nat) (j : Nat),
    i < j ∧ j < prices.length ∧ p = (prices[j]! - prices[i]!)

-- The result upper-bounds all transaction profits.
def IsUpperBoundProfit (prices : List Nat) (ub : Nat) : Prop :=
  ∀ (i : Nat) (j : Nat),
    i < j → j < prices.length → (prices[j]! - prices[i]!) ≤ ub

def precondition (prices : List Nat) : Prop :=
  True

def postcondition (prices : List Nat) (result : Nat) : Prop :=
  (prices.length < 2 ∧ result = 0) ∨
  (2 ≤ prices.length ∧
    IsTransactionProfit prices result ∧
    IsUpperBoundProfit prices result)
end Specs

section Impl
method MaxStockProfit (prices : List Nat)
  return (result : Nat)
  require precondition prices
  ensures postcondition prices result
  do
  pure 0

prove_correct MaxStockProfit by sorry
end Impl

section TestCases
-- Test case 1: classic mixed prices
def test1_prices : List Nat := [7, 1, 5, 3, 6, 4]
def test1_Expected : Nat := 5

-- Test case 2: empty list (no transaction)
def test2_prices : List Nat := []
def test2_Expected : Nat := 0

-- Test case 3: singleton list (no transaction)
def test3_prices : List Nat := [5]
def test3_Expected : Nat := 0

-- Test case 4: strictly increasing prices
def test4_prices : List Nat := [1, 2, 3, 4, 5]
def test4_Expected : Nat := 4

-- Test case 5: strictly decreasing prices (no profit possible)
def test5_prices : List Nat := [5, 4, 3, 2, 1]
def test5_Expected : Nat := 0

-- Test case 6: all equal prices
def test6_prices : List Nat := [3, 3, 3]
def test6_Expected : Nat := 0

-- Test case 7: includes zeros and later increase
def test7_prices : List Nat := [0, 2, 0, 3]
def test7_Expected : Nat := 3

-- Test case 8: best buy is not the global minimum until later
def test8_prices : List Nat := [8, 6, 7, 1, 10]
def test8_Expected : Nat := 9

-- Test case 9: exactly two elements, increasing
def test9_prices : List Nat := [1, 2]
def test9_Expected : Nat := 1

-- Test case 10: exactly two elements, decreasing
def test10_prices : List Nat := [2, 1]
def test10_Expected : Nat := 0
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test10' (result : Nat) :
  result ≠ test10_Expected →
  ¬ postcondition test10_prices result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test10_Expected]) (config := { numInst := 100000 })
