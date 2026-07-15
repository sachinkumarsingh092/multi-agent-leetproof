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
    InsertSubarrayChars: Insert a subarray of characters into another array of characters at a specified index.
    Natural language breakdown:
    1. We are given an original array `oline` and a natural number `l` describing the effective prefix length of `oline` to consider.
    2. We are given an array `nl` and a natural number `p` describing the effective prefix length of `nl` to insert.
    3. We are given an insertion position `atPos` (0-indexed) where insertion occurs into the first `l` characters of `oline`.
    4. Valid inputs satisfy: `l ≤ oline.size`, `p ≤ nl.size`, and `atPos ≤ l`.
    5. The output `result` is an array of characters of length `l + p`.
    6. For indices before `atPos`, `result` equals the corresponding character of `oline`.
    7. For the next `p` indices starting at `atPos`, `result` equals the corresponding character of `nl`.
    8. For the remaining indices, `result` equals the suffix of `oline` (within its first `l` characters) starting at `atPos`, shifted right by `p` positions.
-/

section Specs
-- Preconditions described in the problem statement.
-- All bounds are on natural numbers, and ensure safe indexing in the postcondition.
def precondition (oline : Array Char) (l : Nat) (nl : Array Char) (p : Nat) (atPos : Nat) : Prop :=
  l ≤ oline.size ∧
  p ≤ nl.size ∧
  atPos ≤ l

-- Postcondition: `result` has size `l + p` and matches the intended piecewise content.
def postcondition (oline : Array Char) (l : Nat) (nl : Array Char) (p : Nat) (atPos : Nat)
    (result : Array Char) : Prop :=
  result.size = l + p ∧
  -- Prefix before insertion position is preserved from `oline`.
  (∀ (i : Nat), i < atPos → result[i]! = oline[i]!) ∧
  -- Inserted segment equals the first `p` characters of `nl`.
  (∀ (i : Nat), i < p → result[atPos + i]! = nl[i]!) ∧
  -- Suffix after insertion position comes from `oline`'s prefix of length `l`, shifted by `p`.
  (∀ (i : Nat), i < l - atPos → result[atPos + p + i]! = oline[atPos + i]!)
end Specs

section Impl
method InsertSubarrayChars (oline : Array Char) (l : Nat) (nl : Array Char) (p : Nat) (atPos : Nat)
  return (result : Array Char)
  require precondition oline l nl p atPos
  ensures postcondition oline l nl p atPos result
  do
  pure #[]  -- placeholder

prove_correct InsertSubarrayChars by sorry
end Impl

section TestCases
-- Test case 1: Typical insertion into the middle of the effective prefix.
-- oline prefix length l=4: a b c d, insert first p=2 of nl: X Y at position 2 => a b X Y c d
def test1_oline : Array Char := #['a', 'b', 'c', 'd', 'e']
def test1_l : Nat := 4
def test1_nl : Array Char := #['X', 'Y', 'Z']
def test1_p : Nat := 2
def test1_atPos : Nat := 2
def test1_Expected : Array Char := #['a', 'b', 'X', 'Y', 'c', 'd']

-- Test case 2: Insert at the beginning (atPos=0).
def test2_oline : Array Char := #['m', 'n', 'o']
def test2_l : Nat := 3
def test2_nl : Array Char := #['A', 'B']
def test2_p : Nat := 2
def test2_atPos : Nat := 0
def test2_Expected : Array Char := #['A', 'B', 'm', 'n', 'o']

-- Test case 3: Insert at the end of the effective prefix (atPos=l).
def test3_oline : Array Char := #['q', 'r', 's', 't']
def test3_l : Nat := 3
def test3_nl : Array Char := #['1', '2', '3']
def test3_p : Nat := 2
def test3_atPos : Nat := 3
def test3_Expected : Array Char := #['q', 'r', 's', '1', '2']

-- Test case 4: Insert an empty segment (p=0), so result is exactly the first l characters of oline.
def test4_oline : Array Char := #['u', 'v', 'w', 'x']
def test4_l : Nat := 3
def test4_nl : Array Char := #['Z']
def test4_p : Nat := 0
def test4_atPos : Nat := 1
def test4_Expected : Array Char := #['u', 'v', 'w']

-- Test case 5: Effective length l=0 (degenerate), inserting into empty prefix atPos=0.
def test5_oline : Array Char := #['h', 'i']
def test5_l : Nat := 0
def test5_nl : Array Char := #['K', 'L']
def test5_p : Nat := 2
def test5_atPos : Nat := 0
def test5_Expected : Array Char := #['K', 'L']

-- Test case 6: Both effective segments empty (l=0, p=0) => empty result.
def test6_oline : Array Char := #[]
def test6_l : Nat := 0
def test6_nl : Array Char := #['p']
def test6_p : Nat := 0
def test6_atPos : Nat := 0
def test6_Expected : Array Char := #[]

-- Test case 7: Inserting a singleton into a singleton effective prefix.
def test7_oline : Array Char := #['a']
def test7_l : Nat := 1
def test7_nl : Array Char := #['b']
def test7_p : Nat := 1
def test7_atPos : Nat := 1
def test7_Expected : Array Char := #['a', 'b']

-- Test case 8: Insertion inside when oline has extra characters beyond l; they must be ignored.
-- Only first l=2 of oline are considered: d e; insert p=2 atPos=1 => d x y e
def test8_oline : Array Char := #['d', 'e', 'f', 'g']
def test8_l : Nat := 2
def test8_nl : Array Char := #['x', 'y', 'z']
def test8_p : Nat := 2
def test8_atPos : Nat := 1
def test8_Expected : Array Char := #['d', 'x', 'y', 'e']

-- Test case 9: Inserting using only the first p characters of nl; remaining nl characters are ignored.
def test9_oline : Array Char := #['c', 'c', 'c']
def test9_l : Nat := 2
def test9_nl : Array Char := #['a', 'b', 'c', 'd']
def test9_p : Nat := 1
def test9_atPos : Nat := 1
def test9_Expected : Array Char := #['c', 'a', 'c']
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test9' (result : Array Char) :
  result ≠ test9_Expected →
  ¬ postcondition test9_oline test9_l test9_nl test9_p test9_atPos result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test9_Expected]) (config := { numInst := 100000 })
