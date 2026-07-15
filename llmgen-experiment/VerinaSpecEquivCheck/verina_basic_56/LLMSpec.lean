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
    ReplaceSegment: update a destination array by replacing a specific segment with values taken from a source array.
    Natural language breakdown:
    1. Inputs are a source array `src`, a source start index `sStart`, a destination array `dest`, a destination start index `dStart`, and a length `len`.
    2. The output `result` is an array of integers.
    3. The output has the same size as `dest`.
    4. For all indices `i` with `i < dStart`, `result[i]` equals `dest[i]`.
    5. For all offsets `k` with `k < len`, the element at index `dStart + k` in `result` equals the element at index `sStart + k` in `src`.
    6. For all indices `i` with `dStart + len ≤ i < dest.size`, `result[i]` equals `dest[i]`.
    7. This operation is only required to be defined when `src.size ≥ sStart + len` and `dest.size ≥ dStart + len`.
-/

section Specs
-- Preconditions: the source and destination segments are within bounds.
def precondition (src : Array Int) (sStart : Nat) (dest : Array Int) (dStart : Nat) (len : Nat) : Prop :=
  src.size ≥ sStart + len ∧ dest.size ≥ dStart + len

-- Postconditions: size preserved, outside segment unchanged, inside segment copied.
def postcondition (src : Array Int) (sStart : Nat) (dest : Array Int) (dStart : Nat) (len : Nat)
    (result : Array Int) : Prop :=
  result.size = dest.size ∧
  (∀ (i : Nat), i < dStart → result[i]! = dest[i]!) ∧
  (∀ (k : Nat), k < len → result[dStart + k]! = src[sStart + k]!) ∧
  (∀ (i : Nat), dStart + len ≤ i → i < dest.size → result[i]! = dest[i]!)
end Specs

section Impl
method ReplaceSegment (src : Array Int) (sStart : Nat) (dest : Array Int) (dStart : Nat) (len : Nat)
  return (result : Array Int)
  require precondition src sStart dest dStart len
  ensures postcondition src sStart dest dStart len result
  do
  -- Placeholder body only (specification-focused).
  pure dest

end Impl

section TestCases
-- Test case 1: typical replacement of a middle segment (example)
def test1_src : Array Int := #[9, 8, 7, 6]
def test1_sStart : Nat := 1
def test1_dest : Array Int := #[1, 2, 3, 4, 5]
def test1_dStart : Nat := 2
def test1_len : Nat := 2
def test1_Expected : Array Int := #[1, 2, 8, 7, 5]

-- Test case 2: replace segment at the beginning (dStart = 0)
def test2_src : Array Int := #[10, 11, 12]
def test2_sStart : Nat := 1
def test2_dest : Array Int := #[1, 2, 3, 4]
def test2_dStart : Nat := 0
def test2_len : Nat := 2
def test2_Expected : Array Int := #[11, 12, 3, 4]

-- Test case 3: replace segment at the end (dStart + len = dest.size)
def test3_src : Array Int := #[5, 6, 7, 8]
def test3_sStart : Nat := 0
def test3_dest : Array Int := #[1, 1, 1, 1]
def test3_dStart : Nat := 2
def test3_len : Nat := 2
def test3_Expected : Array Int := #[1, 1, 5, 6]

-- Test case 4: len = 0 (no changes), with non-empty arrays
def test4_src : Array Int := #[3, 4, 5]
def test4_sStart : Nat := 2
def test4_dest : Array Int := #[7, 8]
def test4_dStart : Nat := 1
def test4_len : Nat := 0
def test4_Expected : Array Int := #[7, 8]

-- Test case 5: both arrays empty, len = 0 (degenerate but valid)
def test5_src : Array Int := #[]
def test5_sStart : Nat := 0
def test5_dest : Array Int := #[]
def test5_dStart : Nat := 0
def test5_len : Nat := 0
def test5_Expected : Array Int := #[]

-- Test case 6: singleton destination, replace its only element
def test6_src : Array Int := #[42]
def test6_sStart : Nat := 0
def test6_dest : Array Int := #[0]
def test6_dStart : Nat := 0
def test6_len : Nat := 1
def test6_Expected : Array Int := #[42]

-- Test case 7: copy from later in src into middle of dest
def test7_src : Array Int := #[1, 2, 3, 4, 5, 6]
def test7_sStart : Nat := 3
def test7_dest : Array Int := #[10, 20, 30, 40, 50]
def test7_dStart : Nat := 1
def test7_len : Nat := 3
def test7_Expected : Array Int := #[10, 4, 5, 6, 50]

-- Test case 8: full overwrite (dStart = 0, len = dest.size)
def test8_src : Array Int := #[9, 8, 7, 6, 5]
def test8_sStart : Nat := 0
def test8_dest : Array Int := #[0, 0, 0]
def test8_dStart : Nat := 0
def test8_len : Nat := 3
def test8_Expected : Array Int := #[9, 8, 7]

-- Test case 9: replace segment of length 1 in the interior
def test9_src : Array Int := #[100, 200]
def test9_sStart : Nat := 1
def test9_dest : Array Int := #[1, 2, 3]
def test9_dStart : Nat := 1
def test9_len : Nat := 1
def test9_Expected : Array Int := #[1, 200, 3]
end TestCases
