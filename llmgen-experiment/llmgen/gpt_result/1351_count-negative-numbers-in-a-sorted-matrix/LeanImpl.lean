import Lean
import Mathlib.Tactic
import Velvet.Std
import Extensions.VelvetPBT

set_option maxHeartbeats 10000000

section Specs
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false

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
def implementation (grid : Array (Array Int)) : Nat :=
  let m := grid.size
  if hm : m = 0 then
    0
  else
    -- compute number of columns without using spec helpers
    let n := (grid[0]!).size
    -- Walk from bottom-left (row = m-1, col = 0), moving either up or right.
    let rec go (i j acc : Nat) : Nat :=
      if hI : i < m then
        if hJ : j < n then
          let x : Int := (grid[i]!)[j]!
          if x < 0 then
            -- since rows are non-increasing, all entries to the right are also negative
            let acc' := acc + (n - j)
            if hi0 : i = 0 then
              acc'
            else
              go (i - 1) j acc'
          else
            -- move right
            go i (j + 1) acc
        else
          acc
      else
        acc
    go (m - 1) 0 0
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

section Assertions
-- Test case 1
#assert_same_evaluation #[(implementation test1_grid), test1_Expected]

-- Test case 2
#assert_same_evaluation #[(implementation test2_grid), test2_Expected]

-- Test case 3
#assert_same_evaluation #[(implementation test3_grid), test3_Expected]

-- Test case 4
#assert_same_evaluation #[(implementation test4_grid), test4_Expected]

-- Test case 5
#assert_same_evaluation #[(implementation test5_grid), test5_Expected]

-- Test case 6
#assert_same_evaluation #[(implementation test6_grid), test6_Expected]

-- Test case 7
#assert_same_evaluation #[(implementation test7_grid), test7_Expected]

-- Test case 8
#assert_same_evaluation #[(implementation test8_grid), test8_Expected]

-- Test case 9
#assert_same_evaluation #[(implementation test9_grid), test9_Expected]
end Assertions

section Pbt
method implementationPbt (grid : Array (Array Int))
  return (result : Nat)
  require precondition grid
  ensures postcondition grid result
  do
  return (implementation grid)

velvet_plausible_test implementationPbt (config := { maxMs := some 20000 })
end Pbt

section Proof
theorem correctness_goal
    (grid : Array (Array Int))
    (h_precond : precondition grid)
    : postcondition grid (implementation grid) := by
    sorry
end Proof
