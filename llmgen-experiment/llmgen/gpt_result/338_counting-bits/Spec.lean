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
    CountingBits: Given a natural number n, return an array ans of length n + 1
    where ans[i] is the number of 1-bits in the binary representation of i.
    **Important: complexity should be O(n) time and O(n) space**
    Natural language breakdown:
    1. The input n is a natural number.
    2. The output ans is an array of natural numbers.
    3. The output array has length exactly n + 1.
    4. For every index i with 0 ≤ i ≤ n (equivalently i < ans.size), ans[i] equals the count of bit positions k
       where the k-th bit of i is 1.
    5. Because i ≤ n, it suffices to count 1-bits among bit positions k < n + 1 (a simple, explicit bound).
       This bound is used only for specification purposes.
-/

section Specs
-- Helper: count of 1-bits of i restricted to bit positions k < bnd.
-- We use `Nat.testBit i k : Bool` and count how many k in `Finset.range bnd` have `testBit = true`.
-- (This avoids relying on a library `Nat.popcount` constant that may not be available.)
def popcountUpTo (bnd : Nat) (i : Nat) : Nat :=
  ((Finset.range bnd).filter (fun k : Nat => i.testBit k)).card

def precondition (n : Nat) : Prop :=
  True

def postcondition (n : Nat) (ans : Array Nat) : Prop :=
  ans.size = n + 1 ∧
  (∀ (i : Nat), i < ans.size → ans[i]! = popcountUpTo (n + 1) i)
end Specs

section Impl
method CountingBits (n : Nat)
  return (ans : Array Nat)
  require precondition n
  ensures postcondition n ans
  do
  -- Placeholder body only
  pure (Array.mkArray (n + 1) 0)

end Impl

section TestCases
-- Test case 1: Example 1
-- Input: n = 2
-- Output: [0,1,1]
def test1_n : Nat := 2
def test1_Expected : Array Nat := #[0, 1, 1]

-- Test case 2: Example 2
-- Input: n = 5
-- Output: [0,1,1,2,1,2]
def test2_n : Nat := 5
def test2_Expected : Array Nat := #[0, 1, 1, 2, 1, 2]

-- Test case 3: Edge case n = 0
-- Output: [0]
def test3_n : Nat := 0
def test3_Expected : Array Nat := #[0]

-- Test case 4: Edge case n = 1
-- Output: [0,1]
def test4_n : Nat := 1
def test4_Expected : Array Nat := #[0, 1]

-- Test case 5: Small n = 3
-- Output: [0,1,1,2]
def test5_n : Nat := 3
def test5_Expected : Array Nat := #[0, 1, 1, 2]

-- Test case 6: n = 8 (includes a power of two)
-- Output: [0,1,1,2,1,2,2,3,1]
def test6_n : Nat := 8
def test6_Expected : Array Nat := #[0, 1, 1, 2, 1, 2, 2, 3, 1]

-- Test case 7: n = 10 (typical mid-size)
-- Output: [0,1,1,2,1,2,2,3,1,2,2]
def test7_n : Nat := 10
def test7_Expected : Array Nat := #[0, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2]

-- Test case 8: n = 16 (includes another power of two)
-- Output: [0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,1]
def test8_n : Nat := 16
def test8_Expected : Array Nat := #[0, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 2, 3, 3, 4, 1]

-- Recommend to validate: test1_n, test2_n, test3_n
end TestCases
