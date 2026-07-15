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
    1351. Count Negative Numbers in a Sorted Matrix: count how many entries in a matrix are negative.
    **Important: complexity should be O(m + n) time and O(1) space**
    Natural language breakdown:
    1. The input is a 2D matrix `grid` represented as an array of rows, where each row is an array of integers.
    2. The matrix is rectangular: all rows have the same number of columns.
    3. Each row is sorted in non-increasing order (left to right values never increase).
    4. Each column is sorted in non-increasing order (top to bottom values never increase).
    5. The output is the number of positions (i,j) within the matrix bounds such that `grid[i][j] < 0`.
    6. The output is a natural number.
-/

section Specs
-- Helper: number of columns, defined total (0 for empty grid)
def numCols (grid : Array (Array Int)) : Nat :=
  if h : grid.size = 0 then 0 else (grid[0]!).size

-- Helper: rectangular matrix (nonempty and all rows have same size)
def Rectangular (grid : Array (Array Int)) : Prop :=
  grid.size > 0 ∧
  numCols grid > 0 ∧
  (∀ (i : Nat), i < grid.size → (grid[i]!).size = numCols grid)

-- Helper: row-wise non-increasing order
-- For each row i and adjacent columns j and j+1: grid[i][j] ≥ grid[i][j+1]
def RowWiseNonIncreasing (grid : Array (Array Int)) : Prop :=
  let m := grid.size
  let n := numCols grid
  ∀ (i : Nat), i < m →
    ∀ (j : Nat), j + 1 < n →
      (grid[i]!)[j]! ≥ (grid[i]!)[j + 1]!

-- Helper: column-wise non-increasing order
-- For each column j and adjacent rows i and i+1: grid[i][j] ≥ grid[i+1][j]
def ColWiseNonIncreasing (grid : Array (Array Int)) : Prop :=
  let m := grid.size
  let n := numCols grid
  ∀ (i : Nat), i + 1 < m →
    ∀ (j : Nat), j < n →
      (grid[i]!)[j]! ≥ (grid[i + 1]!)[j]!

-- Helper: mathematical count of negative entries (as a sum over bounded indices)
def negCount (grid : Array (Array Int)) : Nat :=
  let m := grid.size
  let n := numCols grid
  (Finset.range m).sum (fun i =>
    (Finset.range n).sum (fun j => if (grid[i]!)[j]! < 0 then 1 else 0))

-- Preconditions
-- 1) grid is a nonempty rectangular matrix
-- 2) grid is sorted non-increasing in each row and each column
def precondition (grid : Array (Array Int)) : Prop :=
  Rectangular grid ∧
  RowWiseNonIncreasing grid ∧
  ColWiseNonIncreasing grid

-- Postcondition
-- The result equals the number of matrix entries that are negative.
def postcondition (grid : Array (Array Int)) (result : Nat) : Prop :=
  result = negCount grid
end Specs

section Impl
method CountNegatives (grid : Array (Array Int))
  return (result : Nat)
  require precondition grid
  ensures postcondition grid result
  do
  pure 0

end Impl

section TestCases
-- Test case 1: Example 1
-- grid = [[4,3,2,-1],[3,2,1,-1],[1,1,-1,-2],[-1,-1,-2,-3]] has 8 negative entries

def test1_grid : Array (Array Int) :=
  #[#[4, 3, 2, -1], #[3, 2, 1, -1], #[1, 1, -1, -2], #[-1, -1, -2, -3]]

def test1_Expected : Nat := 8

-- Test case 2: Example 2 (no negatives)
def test2_grid : Array (Array Int) := #[#[3, 2], #[1, 0]]

def test2_Expected : Nat := 0

-- Test case 3: 1x1 matrix with a negative value
def test3_grid : Array (Array Int) := #[#[-5]]

def test3_Expected : Nat := 1

-- Test case 4: 1x1 matrix with zero (boundary non-negative)
def test4_grid : Array (Array Int) := #[#[0]]

def test4_Expected : Nat := 0

-- Test case 5: Single row (1 x n) non-increasing, mixed values
def test5_grid : Array (Array Int) := #[#[5, 2, 0, -1, -3]]

def test5_Expected : Nat := 2

-- Test case 6: Single column (m x 1) non-increasing, mixed values
def test6_grid : Array (Array Int) := #[#[4], #[1], #[0], #[-2], #[-2]]

def test6_Expected : Nat := 2

-- Test case 7: All negative entries (2 x 3)
def test7_grid : Array (Array Int) := #[#[-1, -2, -3], #[-2, -3, -4]]

def test7_Expected : Nat := 6

-- Test case 8: Larger with many zeros; negatives appear as a suffix in each row

def test8_grid : Array (Array Int) :=
  #[#[10, 0, 0, -1], #[9, 0, -1, -2], #[8, -1, -2, -3]]

def test8_Expected : Nat := 6

-- Test case 9: 2x2 with one negative

def test9_grid : Array (Array Int) := #[#[1, 0], #[0, -1]]

def test9_Expected : Nat := 1
end TestCases
