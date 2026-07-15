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
    Sorted2DSearch: Search for an integer key in a 2D array where rows and columns are sorted.
    Natural language breakdown:
    1. The input is a 2D array represented as an outer array of rows, each row an array of integers.
    2. The outer array has at least one row.
    3. Each row has the same length, and that common row length is non-zero (rectangular non-empty matrix).
    4. Every row is sorted in non-decreasing order from left to right.
    5. Every column is sorted in non-decreasing order from top to bottom.
    6. The output is a pair (rowIndex, colIndex) of integers.
    7. If the key occurs in the matrix, the output must be an in-bounds index pair pointing to a cell equal to key.
    8. If the key does not occur, the output must be (-1, -1).
    9. If the key occurs multiple times, returning any one of its occurrences is acceptable.
-/

section Specs
-- Number of columns; defined safely even for empty outer arrays.
-- When `a.size = 0`, we define `ncols a = 0`.
-- When `a.size > 0`, we define `ncols a = (a[0]!).size`.
def ncols (a : Array (Array Int)) : Nat :=
  if h : a.size > 0 then
    (a[0]!).size
  else
    0

-- Matrix has at least one row, and all rows have the same positive length.
def isRectangularNonempty (a : Array (Array Int)) : Prop :=
  a.size > 0 ∧
  ncols a > 0 ∧
  (∀ (r : Nat), r < a.size → a[r]!.size = ncols a)

-- Row-wise nondecreasing ordering.
def rowsNondecreasing (a : Array (Array Int)) : Prop :=
  ∀ (r : Nat) (c1 : Nat) (c2 : Nat),
    r < a.size → c1 < c2 → c2 < ncols a → (a[r]!)[c1]! ≤ (a[r]!)[c2]!

-- Column-wise nondecreasing ordering.
def colsNondecreasing (a : Array (Array Int)) : Prop :=
  ∀ (c : Nat) (r1 : Nat) (r2 : Nat),
    c < ncols a → r1 < r2 → r2 < a.size → (a[r1]!)[c]! ≤ (a[r2]!)[c]!

-- The key appears somewhere in the matrix.
def keyOccurs (a : Array (Array Int)) (key : Int) : Prop :=
  ∃ (r : Nat) (c : Nat),
    r < a.size ∧ c < ncols a ∧ (a[r]!)[c]! = key

-- Preconditions: rectangular non-empty matrix, sorted by rows and by columns.
def precondition (a : Array (Array Int)) (key : Int) : Prop :=
  isRectangularNonempty a ∧
  rowsNondecreasing a ∧
  colsNondecreasing a

-- Postcondition:
-- Either the key does not occur and result is (-1,-1),
-- or the key occurs and result is an (Int.ofNat r, Int.ofNat c) pointing to a key cell.
def postcondition (a : Array (Array Int)) (key : Int) (result : Int × Int) : Prop :=
  ((¬ keyOccurs a key) ∧ result = (-1, -1)) ∨
  (∃ (r : Nat) (c : Nat),
    r < a.size ∧
    c < ncols a ∧
    result = (Int.ofNat r, Int.ofNat c) ∧
    (a[r]!)[c]! = key)
end Specs

section Impl
method Sorted2DSearch (a : Array (Array Int)) (key : Int)
  return (result : Int × Int)
  require precondition a key
  ensures postcondition a key result
  do
  pure (-1, -1)  -- placeholder body

prove_correct Sorted2DSearch by sorry
end Impl

section TestCases
-- Test case 1: typical 3x3 matrix, key present at (1,1)
def test1_a : Array (Array Int) := #[(#[1, 2, 3]), (#[4, 5, 6]), (#[7, 8, 9])]
def test1_key : Int := 5
def test1_Expected : Int × Int := (1, 1)

-- Test case 2: same matrix, key absent
def test2_a : Array (Array Int) := #[(#[1, 2, 3]), (#[4, 5, 6]), (#[7, 8, 9])]
def test2_key : Int := 10
def test2_Expected : Int × Int := (-1, -1)

-- Test case 3: 1x1 matrix, key present
def test3_a : Array (Array Int) := #[(#[42])]
def test3_key : Int := 42
def test3_Expected : Int × Int := (0, 0)

-- Test case 4: 1x1 matrix, key absent (uses key = 0 boundary value)
def test4_a : Array (Array Int) := #[(#[42])]
def test4_key : Int := 0
def test4_Expected : Int × Int := (-1, -1)

-- Test case 5: 2x4 matrix with negatives; key present uniquely at (0,2)
-- [ [-3, -1, 0, 1],
--   [-1,  2, 3, 5] ]
def test5_a : Array (Array Int) := #[(#[-3, -1, 0, 1]), (#[-1, 2, 3, 5])]
def test5_key : Int := 0
def test5_Expected : Int × Int := (0, 2)

-- Test case 6: same 2x4 matrix, key absent (uses key = 1 boundary-ish value, not present)
def test6_a : Array (Array Int) := #[(#[-3, -1, 0, 1]), (#[-1, 2, 3, 5])]
def test6_key : Int := 4
def test6_Expected : Int × Int := (-1, -1)

-- Test case 7: 2x2 matrix with unique key in top-left
def test7_a : Array (Array Int) := #[(#[7, 8]), (#[9, 10])]
def test7_key : Int := 7
def test7_Expected : Int × Int := (0, 0)

-- Test case 8: 4x1 (single column), key present uniquely
def test8_a : Array (Array Int) := #[(#[1]), (#[2]), (#[4]), (#[5])]
def test8_key : Int := 2
def test8_Expected : Int × Int := (1, 0)

-- Test case 9: 1x5 (single row), key present at last position
def test9_a : Array (Array Int) := #[(#[0, 1, 1, 2, 10])]
def test9_key : Int := 10
def test9_Expected : Int × Int := (0, 4)

-- Recommend to validate: sortedness-by-row, sortedness-by-column, rectangular-shape
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test9' (result : Int × Int) :
  result ≠ test9_Expected →
  ¬ postcondition test9_a test9_key result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test9_Expected]) (config := { numInst := 100000 })
