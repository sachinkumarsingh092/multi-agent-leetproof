import Lean

import Mathlib.Tactic

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

section Proof

-- Unfolding lemma for the recursive go function
theorem go_unfold (grid : Array (Array Int)) (m n i j acc : Nat) :
    implementation.go grid m n i j acc =
    if i < m then
      if j < n then
        if (grid[i]!)[j]! < 0 then
          if i = 0 then acc + (n - j)
          else implementation.go grid m n (i - 1) j (acc + (n - j))
        else implementation.go grid m n i (j + 1) acc
      else acc
    else acc := by
  conv_lhs => unfold implementation.go
  split
  · split
    · split
      · split <;> simp_all
      · simp_all
    · simp_all
  · simp_all

-- Count of negatives in a rectangular region: rows 0..rows-1, cols colStart..n-1
noncomputable def negCountRegion (grid : Array (Array Int)) (rows colStart : Nat) : Nat :=
  let n := numCols grid
  (Finset.range rows).sum (fun i =>
    (Finset.Ico colStart n).sum (fun j => if (grid[i]!)[j]! < 0 then 1 else 0))

/-
PROBLEM
negCountRegion with full range equals negCount

PROVIDED SOLUTION
Unfold negCountRegion and negCount. The only difference is Finset.range n vs Finset.Ico 0 n. Use Finset.Ico_zero_eq_range or similar to show they're equal.
-/
theorem negCountRegion_full (grid : Array (Array Int)) :
    negCountRegion grid grid.size 0 = negCount grid := by
  unfold negCountRegion negCount; aesop;

/-
PROBLEM
If row is non-increasing and grid[i][j] < 0, then grid[i][k] < 0 for all k with j ≤ k < n

PROVIDED SOLUTION
By induction on (k - j). Base case k = j is trivial. For the inductive step, use RowWiseNonIncreasing to get grid[i][k-1] >= grid[i][k], and use the inductive hypothesis that grid[i][k-1] < 0 to conclude grid[i][k] < 0. More precisely, use strong induction: if j ≤ k and grid[i][j] < 0, either k = j (done) or j < k, then by RowWiseNonIncreasing grid[i][k-1] >= grid[i][k], and by IH grid[i][k-1] < 0, so grid[i][k] ≤ grid[i][k-1] < 0.
-/
theorem row_neg_suffix (grid : Array (Array Int))
    (hrow : RowWiseNonIncreasing grid)
    (hi : i < grid.size) (hj : j < numCols grid) (hk : k < numCols grid)
    (hjk : j ≤ k) (hneg : (grid[i]!)[j]! < 0) :
    (grid[i]!)[k]! < 0 := by
  -- By induction on (k - j), we can show that grid[i][k] < 0.
  induction' hjk with k' hk' ih;
  · assumption;
  · exact lt_of_le_of_lt ( hrow i hi k' hk ) ( ih ( Nat.lt_of_succ_lt hk ) )

/-
PROBLEM
If col is non-increasing and grid[i][j] ≥ 0, then grid[r][j] ≥ 0 for all r ≤ i

PROVIDED SOLUTION
By induction on (i - r). Base case r = i is trivial. For the step, use ColWiseNonIncreasing: grid[r][j] >= grid[r+1][j], and by IH grid[r+1][j] >= 0 (since r+1 ≤ i), so grid[r][j] >= grid[r+1][j] >= 0. Use strong/natural induction on (i - r).
-/
theorem col_nonneg_above (grid : Array (Array Int))
    (hcol : ColWiseNonIncreasing grid)
    (hi : i < grid.size) (hj : j < numCols grid)
    (hr : r < grid.size) (hri : r ≤ i)
    (hge : (grid[i]!)[j]! ≥ 0) :
    (grid[r]!)[j]! ≥ 0 := by
  -- By induction on $i - r$, we can show that if $grid[i][j] \geq 0$, then $grid[r][j] \geq 0$ for all $r \leq i$.
  induction' hri with r hr ih;
  · assumption;
  · exact ih ( Nat.lt_of_succ_lt hi ) ( le_trans hge ( hcol _ ( by linarith ) _ ( by linarith ) ) )

/-
PROBLEM
When all entries in a row's suffix are negative, the count for that row is n - colStart

PROVIDED SOLUTION
Every element in Finset.Ico colStart n satisfies grid[i][j] < 0 by hall. So each summand is 1. The sum of 1 over Finset.Ico colStart n equals Finset.card (Finset.Ico colStart n) = n - colStart. Use Finset.sum_const and Finset.card_Ico.
-/
theorem row_all_neg_count (grid : Array (Array Int)) (i colStart n : Nat)
    (hn : n = numCols grid)
    (hcs : colStart < n)
    (hall : ∀ k, colStart ≤ k → k < n → (grid[i]!)[k]! < 0) :
    (Finset.Ico colStart n).sum (fun j => if (grid[i]!)[j]! < 0 then 1 else 0) = n - colStart := by
  rw [ Finset.sum_congr rfl fun x hx => if_pos ( hall x ( Finset.mem_Ico.mp hx |>.1 ) ( Finset.mem_Ico.mp hx |>.2 ) ) ] ; aesop

/-
PROBLEM
When all entries in a column for rows 0..rows-1 are non-negative,
removing that column doesn't change negCountRegion

PROVIDED SOLUTION
Unfold negCountRegion. For each row r < rows, split Finset.Ico colStart n into {colStart} ∪ Finset.Ico (colStart+1) n. The contribution of column colStart is 0 because grid[r][colStart] >= 0 (by hall). So the sum reduces to the sum over Finset.Ico (colStart+1) n. Use Finset.Ico_insert_right or Finset.sum_Ico_eq_add_neg with Finset.Ico_cons or similar splitting lemma.
-/
theorem negCountRegion_col_nonneg (grid : Array (Array Int)) (rows colStart : Nat)
    (hcs : colStart < numCols grid)
    (hall : ∀ r, r < rows → (grid[r]!)[colStart]! ≥ 0) :
    negCountRegion grid rows colStart = negCountRegion grid rows (colStart + 1) := by
  apply Finset.sum_congr rfl (fun i hi => ?_);
  -- Since grid[i][colStart] is non-negative, the sum over the interval starting at colStart can be split into the sum over the interval starting at colStart+1 and the term for colStart, which is zero.
  have h_split : Finset.Ico colStart (numCols grid) = {colStart} ∪ Finset.Ico (colStart + 1) (numCols grid) := by
    grind;
  grind

/-
PROBLEM
Split negCountRegion: last row out

PROVIDED SOLUTION
Unfold negCountRegion and use Finset.sum_range_succ to split the outer sum at the last row.
-/
theorem negCountRegion_split_last (grid : Array (Array Int)) (rows colStart : Nat) :
    negCountRegion grid (rows + 1) colStart =
    negCountRegion grid rows colStart +
    (Finset.Ico colStart (numCols grid)).sum (fun j => if (grid[rows]!)[j]! < 0 then 1 else 0) := by
  unfold negCountRegion;
  rw [ Finset.sum_range_succ ]

/-
PROBLEM
numCols equals (grid[0]!).size when grid is nonempty

PROVIDED SOLUTION
Unfold numCols, use dif_neg hne to simplify the if-then-else.
-/
theorem numCols_eq (grid : Array (Array Int)) (hne : grid.size ≠ 0) :
    numCols grid = (grid[0]!).size := by
  unfold numCols; aesop;

/-
PROBLEM
Main loop invariant: go computes acc + negCountRegion
Under preconditions and the "left region non-negative" condition

PROVIDED SOLUTION
Use well-founded induction on the pair (i, n - j) with lexicographic order, or on the measure (m * n - (m - 1 - i) * n - j) or simply on (i + (n - j)).

After rewriting with go_unfold, split on whether j < n:

Case j ≥ n (j not less than n):
  go returns acc. negCountRegion grid (i+1) j = 0 since Finset.Ico j n is empty when j ≥ n.
  So result = acc + 0 = acc. ✓

Case j < n: split on whether grid[i][j] < 0:

  Subcase grid[i][j] ≥ 0:
    go recurses with (i, j+1, acc).
    By col_nonneg_above, grid[r][j] ≥ 0 for all r ≤ i.
    By negCountRegion_col_nonneg, negCountRegion grid (i+1) j = negCountRegion grid (i+1) (j+1).
    Apply IH with j+1. The hleft condition extends because column j is non-negative for rows ≤ i.

  Subcase grid[i][j] < 0:
    Split on i = 0:

    Sub-subcase i = 0:
      go returns acc + (n - j).
      negCountRegion grid 1 j = sum over row 0 of negatives in cols j..n-1.
      By row_neg_suffix, all entries in row 0 cols j..n-1 are negative.
      By row_all_neg_count, this sum = n - j.
      So result = acc + (n - j). ✓

    Sub-subcase i > 0:
      go recurses with (i-1, j, acc + (n - j)).
      negCountRegion grid (i+1) j = negCountRegion grid i j + row_i_contribution.
      By row_neg_suffix, row i cols j..n-1 are all negative, so contribution = n - j.
      Use negCountRegion_split_last to split: negCountRegion grid (i+1) j = negCountRegion grid i j + (n - j).
      Apply IH with (i-1, j, acc + (n - j)).
      Need i - 1 < m, which follows from i < m.
      hleft for (i-1, j) follows from hleft for (i, j) restricted to r ≤ i-1.
      IH gives: go(i-1, j, acc+(n-j)) = acc + (n-j) + negCountRegion grid i j.
      = acc + negCountRegion grid (i+1) j. ✓
-/
theorem go_spec (grid : Array (Array Int))
    (m n : Nat)
    (hm : m = grid.size) (hn : n = numCols grid)
    (hpre : precondition grid)
    (i j acc : Nat)
    (hi : i < m)
    (hleft : ∀ r c, r ≤ i → c < j → r < m → c < n → (grid[r]!)[c]! ≥ 0) :
    implementation.go grid m n i j acc = acc + negCountRegion grid (i + 1) j := by
  -- By induction on $i + (n - j)$, we can show that the go function correctly computes the number of negative entries in the specified region.
  induction' h : i + (n - j) using Nat.strong_induction_on with k ih generalizing i j acc;
  by_cases hj : j < n;
  · by_cases hneg : (grid[i]!)[j]! < 0;
    · -- By row_neg_suffix, all entries in row i cols j..n-1 are negative.
      have h_row_neg : ∀ k, j ≤ k → k < n → (grid[i]!)[k]! < 0 := by
        exact fun k hk₁ hk₂ => row_neg_suffix grid hpre.2.1 ( by linarith ) ( by linarith ) ( by linarith ) hk₁ hneg;
      by_cases hi0 : i = 0;
      · -- Since i is 0, the row is just the first row. The go function in this case would add (n - j) to the accumulator because all elements from j to n-1 are negative.
        have h_row_zero : negCountRegion grid 1 j = n - j := by
          convert row_all_neg_count grid 0 j n hn hj _;
          · unfold negCountRegion; aesop;
          · grind;
        unfold implementation.go; aesop;
      · -- By the induction hypothesis, we have:
        have h_ind : implementation.go grid m n (i - 1) j (acc + (n - j)) = (acc + (n - j)) + negCountRegion grid i j := by
          convert ih ( i - 1 + ( n - j ) ) _ ( i - 1 ) j ( acc + ( n - j ) ) _ _ _ using 1;
          · rw [ Nat.sub_add_cancel ( Nat.pos_of_ne_zero hi0 ) ];
          · omega;
          · exact lt_of_le_of_lt ( Nat.pred_le _ ) hi;
          · exact fun r c hr hc hr' hc' => hleft r c ( Nat.le_trans hr ( Nat.pred_le _ ) ) hc hr' hc';
          · rfl;
        convert h_ind using 1;
        · rw [ go_unfold ];
          grind;
        · rw [ negCountRegion_split_last ];
          rw [ Finset.sum_congr rfl fun x hx => if_pos <| h_row_neg x ( Finset.mem_Ico.mp hx |>.1 ) ( Finset.mem_Ico.mp hx |>.2 |> fun h => by linarith [ hn ] ) ] ; simp +arith +decide [ hn ];
    · -- If j < n and grid[i][j] ≥ 0, then by col_nonneg_above, all entries in column j for rows ≤ i are non-negative.
      have h_col_nonneg : ∀ r, r ≤ i → (grid[r]!)[j]! ≥ 0 := by
        intros r hr
        apply col_nonneg_above grid hpre.right.right (by linarith) (by linarith) (by linarith) hr (by linarith);
      -- By negCountRegion_col_nonneg, removing column j doesn't change the negCountRegion.
      have h_negCountRegion_col_nonneg : negCountRegion grid (i + 1) j = negCountRegion grid (i + 1) (j + 1) := by
        apply negCountRegion_col_nonneg;
        · linarith;
        · exact fun r hr => h_col_nonneg r ( Nat.le_of_lt_succ hr );
      rw [ go_unfold, if_pos hi, if_pos hj ];
      grind;
  · unfold negCountRegion;
    unfold implementation.go; aesop;

/-
PROVIDED SOLUTION
Unfold postcondition and implementation. Split on whether grid.size = 0.

Case grid.size = 0: contradicts precondition (which requires grid.size > 0).

Case grid.size ≠ 0: The implementation returns `implementation.go grid grid.size n (grid.size - 1) 0 0` where n = (grid[0]!).size.
By numCols_eq, n = numCols grid.
Apply go_spec with i = grid.size - 1, j = 0, acc = 0.
- hi: grid.size - 1 < grid.size (since grid.size > 0)
- hleft: vacuously true since j = 0 means c < 0 is impossible
This gives: implementation.go ... = 0 + negCountRegion grid grid.size 0 = negCount grid (by negCountRegion_full).
-/
theorem correctness_goal (grid : Array (Array Int)) (h_precond : precondition grid) : postcondition grid (implementation grid) := by
    by_cases h : grid.size = 0;
    · cases h_precond ; aesop;
    · unfold postcondition;
      convert go_spec grid grid.size ( numCols grid ) rfl rfl h_precond ( grid.size - 1 ) 0 0 _ _ using 1;
      · unfold implementation;
        unfold numCols; aesop;
      · rw [ Nat.sub_add_cancel ( Nat.pos_of_ne_zero h ), negCountRegion_full ] ; norm_num;
      · exact Nat.pred_lt h;
      · aesop

end Proof