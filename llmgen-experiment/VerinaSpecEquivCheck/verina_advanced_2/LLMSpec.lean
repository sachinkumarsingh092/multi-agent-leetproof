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
    LCSLength: compute the length of the longest common subsequence of two integer arrays.
    Natural language breakdown:
    1. Input consists of two arrays `a` and `b` of integers.
    2. A sequence `c` is a subsequence of an array `x` if we can pick indices in `x` that are strictly increasing
       and the elements of `c` match `x` at those indices.
    3. A common subsequence of `a` and `b` is an array `c` that is a subsequence of both.
    4. The function returns the length (as an `Int`) of a longest common subsequence.
    5. The returned length is nonnegative and is at most `min a.size b.size`.
    6. Maximality: every common subsequence has length at most the returned length.
    7. Existence: there exists some common subsequence whose length equals the returned length.
-/

section Specs
-- `idxs` is a valid index embedding for witnessing that `sub` is a subsequence of `sup`.
-- Intuition: `idxs` lists the positions in `sup` from which we read out the elements of `sub`.

def ValidEmbedding (sub : Array Int) (sup : Array Int) (idxs : Array Nat) : Prop :=
  idxs.size = sub.size ∧
  (∀ i : Nat, i < idxs.size → idxs[i]! < sup.size) ∧
  (∀ i : Nat, i + 1 < idxs.size → idxs[i]! < idxs[i + 1]!) ∧
  (∀ i : Nat, i < sub.size → sub[i]! = sup[idxs[i]!]!)

-- `sub` is a subsequence of `sup`.
def IsSubsequence (sub : Array Int) (sup : Array Int) : Prop :=
  ∃ idxs : Array Nat, ValidEmbedding sub sup idxs

-- `c` is a common subsequence of `a` and `b`.
def IsCommonSubsequence (a : Array Int) (b : Array Int) (c : Array Int) : Prop :=
  IsSubsequence c a ∧ IsSubsequence c b

-- There are no restrictions on inputs.
def precondition (a : Array Int) (b : Array Int) : Prop :=
  True

-- The result is the maximum achievable length among common subsequences.
-- We express maximality and existence using a witness length `k : Nat` and `result = Int.ofNat k`.

def postcondition (a : Array Int) (b : Array Int) (result : Int) : Prop :=
  (∃ k : Nat,
    result = Int.ofNat k ∧
    k ≤ Nat.min a.size b.size ∧
    (∃ c : Array Int, IsCommonSubsequence a b c ∧ c.size = k) ∧
    (∀ c : Array Int, IsCommonSubsequence a b c → c.size ≤ k))
end Specs

section Impl
method LCSLength (a : Array Int) (b : Array Int)
  return (result : Int)
  require precondition a b
  ensures postcondition a b result
  do
  pure (0 : Int)  -- placeholder

end Impl

section TestCases
-- Test case 1: identical arrays
def test1_a : Array Int := #[1, 2, 3]
def test1_b : Array Int := #[1, 2, 3]
def test1_Expected : Int := 3

-- Test case 2: one array empty
def test2_a : Array Int := #[]
def test2_b : Array Int := #[5, 6]
def test2_Expected : Int := 0

-- Test case 3: both arrays empty
def test3_a : Array Int := #[]
def test3_b : Array Int := #[]
def test3_Expected : Int := 0

-- Test case 4: disjoint arrays
def test4_a : Array Int := #[1, 2, 3]
def test4_b : Array Int := #[4, 5]
def test4_Expected : Int := 0

-- Test case 5: classic interleaving subsequence
def test5_a : Array Int := #[1, 3, 4, 1, 2, 3]
def test5_b : Array Int := #[3, 4, 1, 2, 1, 3]
def test5_Expected : Int := 5

-- Test case 6: repeated values (choose as many as possible)
def test6_a : Array Int := #[7, 7, 7]
def test6_b : Array Int := #[7, 7]
def test6_Expected : Int := 2

-- Test case 7: singleton arrays equal
def test7_a : Array Int := #[42]
def test7_b : Array Int := #[42]
def test7_Expected : Int := 1

-- Test case 8: singleton arrays not equal
def test8_a : Array Int := #[42]
def test8_b : Array Int := #[0]
def test8_Expected : Int := 0

-- Test case 9: negative values and order constraints
def test9_a : Array Int := #[-1, 0, 1]
def test9_b : Array Int := #[0, -1, 1]
def test9_Expected : Int := 2
end TestCases
