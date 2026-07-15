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
  let m := grid.size
  let n := numCols grid

  -- O(m + n) walk from bottom-left.
  -- Maintain a boundary column j: entries left of j in current row are known negative.
  let mut i : Nat := m
  let mut j : Nat := 0
  let mut cnt : Nat := 0

  while (i > 0 ∧ j < n)
    -- Bounds needed for array indexing and for the remaining-count expression.
    -- Init: i = m, j = 0. Preserved: i only decreases (to i-1), j only increases (to j+1).
    invariant "inv_bounds" (i ≤ m ∧ j ≤ n)
    -- Functional correctness accounting:
    -- Let rem be the number of negatives in the "not-yet-ruled-out" region rows [0,i) and cols [j,n).
    -- Init: rem = negCount grid (since i=m, j=0, rem ranges over the whole matrix).
    -- Step: if v<0 we count exactly the (n-j) negatives in row (i-1) at columns ≥ j and shrink i;
    --       if v≥0 we rule out column j for rows < i and shrink the region by increasing j.
    invariant "inv_accounting"
      (cnt +
        (Finset.range i).sum (fun r =>
          (Finset.range (n - j)).sum (fun t =>
            if (grid[r]!)[j + t]! < 0 then 1 else 0)))
      = negCount grid
    -- Termination: each step strictly decreases i or increases j, so i + (n-j) strictly decreases.
    decreasing i + (n - j)
  do
    let ii : Nat := i - 1
    let v : Int := (grid[ii]!)[j]!
    if v < 0 then
      -- Since row is non-increasing, all entries to the right are ≤ v < 0.
      cnt := cnt + (n - j)
      i := ii
    else
      -- Since column is non-increasing, entries above are ≥ v ≥ 0; move right.
      j := j + 1

  return cnt
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

#assert_same_evaluation #[((CountNegatives test1_grid).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((CountNegatives test2_grid).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((CountNegatives test3_grid).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((CountNegatives test4_grid).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((CountNegatives test5_grid).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((CountNegatives test6_grid).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((CountNegatives test7_grid).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((CountNegatives test8_grid).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((CountNegatives test9_grid).run), DivM.res test9_Expected ]
end Assertions

section Pbt
velvet_plausible_test CountNegatives (config := { maxMs := some 20000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000

theorem goal_0
    (grid : Array (Array ℤ))
    (cnt : ℕ)
    (i : ℕ)
    (j : ℕ)
    (a : i ≤ grid.size)
    (if_pos : (grid[i - OfNat.ofNat 1]!)[j]! < OfNat.ofNat 0)
    (require_1 : (OfNat.ofNat 0 < grid.size ∧ (OfNat.ofNat 0 < if grid = #[] then OfNat.ofNat 0 else grid[OfNat.ofNat 0]!.size) ∧ ∀ i < grid.size, grid[i]!.size = if grid = #[] then OfNat.ofNat 0 else grid[OfNat.ofNat 0]!.size) ∧ (∀ i < grid.size, ∀ (j : ℕ), (j + OfNat.ofNat 1 < if grid = #[] then OfNat.ofNat 0 else grid[OfNat.ofNat 0]!.size) → (grid[i]!)[j + OfNat.ofNat 1]! ≤ (grid[i]!)[j]!) ∧ ∀ (i : ℕ), i + OfNat.ofNat 1 < grid.size → ∀ j < if grid = #[] then OfNat.ofNat 0 else grid[OfNat.ofNat 0]!.size, (grid[i + OfNat.ofNat 1]!)[j]! ≤ (grid[i]!)[j]!)
    (a_1 : j ≤ if grid = #[] then OfNat.ofNat 0 else grid[OfNat.ofNat 0]!.size)
    (invariant_inv_accounting : cnt + ∑ x ∈ Finset.range i, {x_1 ∈ Finset.range ((if grid = #[] then OfNat.ofNat 0 else grid[OfNat.ofNat 0]!.size) - j) | (grid[x]!)[j + x_1]! < OfNat.ofNat 0}.card = ∑ x ∈ Finset.range grid.size, {x_1 ∈ Finset.range (if grid = #[] then OfNat.ofNat 0 else grid[OfNat.ofNat 0]!.size) | (grid[x]!)[x_1]! < OfNat.ofNat 0}.card)
    (a_2 : OfNat.ofNat 0 < i)
    : cnt + ((if grid = #[] then OfNat.ofNat 0 else grid[OfNat.ofNat 0]!.size) - j) + ∑ x ∈ Finset.range (i - OfNat.ofNat 1), {x_1 ∈ Finset.range ((if grid = #[] then OfNat.ofNat 0 else grid[OfNat.ofNat 0]!.size) - j) | (grid[x]!)[j + x_1]! < OfNat.ofNat 0}.card = ∑ x ∈ Finset.range grid.size, {x_1 ∈ Finset.range (if grid = #[] then OfNat.ofNat 0 else grid[OfNat.ofNat 0]!.size) | (grid[x]!)[x_1]! < OfNat.ofNat 0}.card := by
  set n : Nat := (if grid = #[] then 0 else grid[0]!.size)
  have a1' : j ≤ n := by
    simpa [n] using a_1

  let f : Nat → Nat := fun x =>
    {t ∈ Finset.range (n - j) | (grid[x]!)[j + t]! < (0 : ℤ)}.card

  have inv : cnt + ∑ x ∈ Finset.range i, f x
        = ∑ x ∈ Finset.range grid.size, {t ∈ Finset.range n | (grid[x]!)[t]! < (0 : ℤ)}.card := by
    simpa [n, f] using invariant_inv_accounting

  have hRow : ∀ r < grid.size, ∀ c : Nat, c + 1 < n → (grid[r]!)[c + 1]! ≤ (grid[r]!)[c]! := by
    simpa [n] using require_1.2.1

  have hiRow : i - 1 < grid.size := by
    have hi_lt : i - 1 < i := by
      -- `Nat.pred_lt_self` is convenient for `i-1 < i` under `0 < i`.
      simpa using (Nat.pred_lt_self a_2)
    exact lt_of_lt_of_le hi_lt a

  have if_pos' : (grid[i - 1]!)[j]! < (0 : ℤ) := by
    simpa using if_pos

  have hAllNeg : ∀ t < n - j, (grid[i - 1]!)[j + t]! < (0 : ℤ) := by
    intro t ht
    induction t with
    | zero =>
        simpa using if_pos'
    | succ t ih =>
        have ht' : t < n - j := Nat.lt_of_succ_lt ht
        have hprev : (grid[i - 1]!)[j + t]! < (0 : ℤ) := ih ht'
        have hjt1 : j + t + 1 < n := by
          have h := Nat.add_lt_add_left ht j
          -- h : j + (t+1) < j + (n-j)
          simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_sub_of_le a1'] using h
        have hle : (grid[i - 1]!)[j + t + 1]! ≤ (grid[i - 1]!)[j + t]! := by
          simpa [Nat.add_assoc] using (hRow (i - 1) hiRow (j + t) hjt1)
        have : (grid[i - 1]!)[j + t + 1]! < (0 : ℤ) := lt_of_le_of_lt hle hprev
        simpa [Nat.succ_eq_add_one, Nat.add_assoc] using this

  have hallMem : ∀ t ∈ Finset.range (n - j), (grid[i - 1]!)[j + t]! < (0 : ℤ) := by
    intro t ht
    exact hAllNeg t (by simpa using ht)

  have hset : {t ∈ Finset.range (n - j) | (grid[i - 1]!)[j + t]! < (0 : ℤ)}
        = Finset.range (n - j) := by
    simpa using
      (Finset.filter_true_of_mem (s := Finset.range (n - j))
        (p := fun t => (grid[i - 1]!)[j + t]! < (0 : ℤ)) hallMem)

  have hf_last : f (i - 1) = n - j := by
    -- since all entries in that row-suffix are negative, the filtered finset is the whole range
    simp [f, hset]

  have hi1 : i - 1 + 1 = i := Nat.sub_add_cancel (Nat.succ_le_of_lt a_2)

  have inv2 : cnt + ∑ x ∈ Finset.range ((i - 1) + 1), f x
        = ∑ x ∈ Finset.range grid.size, {t ∈ Finset.range n | (grid[x]!)[t]! < (0 : ℤ)}.card := by
    simpa [hi1] using inv

  have inv3 : cnt + ((∑ x ∈ Finset.range (i - 1), f x) + f (i - 1))
        = ∑ x ∈ Finset.range grid.size, {t ∈ Finset.range n | (grid[x]!)[t]! < (0 : ℤ)}.card := by
    simpa [Finset.sum_range_succ, Nat.add_assoc] using inv2

  have main : cnt + (n - j) + ∑ x ∈ Finset.range (i - 1), f x
        = ∑ x ∈ Finset.range grid.size, {t ∈ Finset.range n | (grid[x]!)[t]! < (0 : ℤ)}.card := by
    calc
      cnt + (n - j) + ∑ x ∈ Finset.range (i - 1), f x
          = cnt + ((∑ x ∈ Finset.range (i - 1), f x) + (n - j)) := by
              ac_rfl
      _ = cnt + ((∑ x ∈ Finset.range (i - 1), f x) + f (i - 1)) := by
              simp [hf_last]
      _ = _ := by
              simpa [Nat.add_assoc] using inv3

  -- unfold `n` and `f` back to match the goal statement
  simpa [n, f] using main

theorem goal_1
    (grid : Array (Array ℤ))
    (cnt : ℕ)
    (i : ℕ)
    (j : ℕ)
    (a : i ≤ grid.size)
    (require_1 : (OfNat.ofNat 0 < grid.size ∧ (OfNat.ofNat 0 < if grid = #[] then OfNat.ofNat 0 else grid[OfNat.ofNat 0]!.size) ∧ ∀ i < grid.size, grid[i]!.size = if grid = #[] then OfNat.ofNat 0 else grid[OfNat.ofNat 0]!.size) ∧ (∀ i < grid.size, ∀ (j : ℕ), (j + OfNat.ofNat 1 < if grid = #[] then OfNat.ofNat 0 else grid[OfNat.ofNat 0]!.size) → (grid[i]!)[j + OfNat.ofNat 1]! ≤ (grid[i]!)[j]!) ∧ ∀ (i : ℕ), i + OfNat.ofNat 1 < grid.size → ∀ j < if grid = #[] then OfNat.ofNat 0 else grid[OfNat.ofNat 0]!.size, (grid[i + OfNat.ofNat 1]!)[j]! ≤ (grid[i]!)[j]!)
    (invariant_inv_accounting : cnt + ∑ x ∈ Finset.range i, {x_1 ∈ Finset.range ((if grid = #[] then OfNat.ofNat 0 else grid[OfNat.ofNat 0]!.size) - j) | (grid[x]!)[j + x_1]! < OfNat.ofNat 0}.card = ∑ x ∈ Finset.range grid.size, {x_1 ∈ Finset.range (if grid = #[] then OfNat.ofNat 0 else grid[OfNat.ofNat 0]!.size) | (grid[x]!)[x_1]! < OfNat.ofNat 0}.card)
    (a_2 : OfNat.ofNat 0 < i)
    (a_3 : j < if grid = #[] then OfNat.ofNat 0 else grid[OfNat.ofNat 0]!.size)
    (if_neg : OfNat.ofNat 0 ≤ (grid[i - OfNat.ofNat 1]!)[j]!)
    : cnt + ∑ x ∈ Finset.range i, {x_1 ∈ Finset.range ((if grid = #[] then OfNat.ofNat 0 else grid[OfNat.ofNat 0]!.size) - (j + OfNat.ofNat 1)) | (grid[x]!)[j + OfNat.ofNat 1 + x_1]! < OfNat.ofNat 0}.card = ∑ x ∈ Finset.range grid.size, {x_1 ∈ Finset.range (if grid = #[] then OfNat.ofNat 0 else grid[OfNat.ofNat 0]!.size) | (grid[x]!)[x_1]! < OfNat.ofNat 0}.card := by
  classical

  set n : Nat := (if grid = #[] then 0 else grid[0]!.size)
  have hjlt : j < n := by simpa [n] using a_3

  have hcol : ∀ (r : ℕ), r + 1 < grid.size → ∀ jj < n, (grid[r + 1]!)[jj]! ≤ (grid[r]!)[jj]! := by
    simpa [n] using require_1.2.2

  have hnonneg_aux : ∀ (x d : Nat), i - 1 = x + d → x + d < grid.size → (0 : ℤ) ≤ (grid[x]!)[j]! := by
    intro x d
    induction d generalizing x with
    | zero =>
        intro hEq _
        have hx : x = i - 1 := by
          simpa [Nat.add_zero] using hEq.symm
        simpa [hx] using if_neg
    | succ d ih =>
        intro hEq hlt
        have hx1add : x + Nat.succ d = (x + 1) + d := by
          -- both sides are `Nat.succ (x + d)`
          calc
            x + Nat.succ d = Nat.succ (x + d) := (Nat.add_succ x d)
            _ = (Nat.succ x) + d := (Nat.succ_add x d).symm
            _ = (x + 1) + d := by
              -- rewrite `Nat.succ x` as `x + 1`
              simpa using congrArg (fun t => t + d) (Nat.add_one x).symm
        have hEq' : i - 1 = (x + 1) + d := by
          -- rewrite RHS using hx1add
          exact (hEq.trans hx1add)
        have hlt' : (x + 1) + d < grid.size := by
          -- rewrite RHS using hx1add
          simpa [hx1add] using hlt
        have hx1_nonneg : (0 : ℤ) ≤ (grid[x + 1]!)[j]! := ih (x := x + 1) hEq' hlt'
        have hx1_lt_size : x + 1 < grid.size :=
          lt_of_le_of_lt (Nat.le_add_right (x + 1) d) hlt'
        have hx_mon : (grid[x + 1]!)[j]! ≤ (grid[x]!)[j]! := hcol x hx1_lt_size j hjlt
        exact le_trans hx1_nonneg hx_mon

  have hnonneg : ∀ x < i, (0 : ℤ) ≤ (grid[x]!)[j]! := by
    intro x hx
    have hxle : x ≤ i - 1 := Nat.le_pred_of_lt hx
    obtain ⟨d, hd⟩ : ∃ d, i - 1 = x + d := Nat.exists_eq_add_of_le hxle
    have hipred_lt : i - 1 < i := Nat.pred_lt (Nat.ne_of_gt a_2)
    have hipred_lt_size : i - 1 < grid.size := lt_of_lt_of_le hipred_lt a
    have hlt : x + d < grid.size := by simpa [hd] using hipred_lt_size
    exact hnonneg_aux x d hd hlt

  have hnsub : n - j = (n - (j + 1)) + 1 := by
    have hpos : 0 < n - j := Nat.sub_pos_of_lt hjlt
    have hle : 1 ≤ n - j := Nat.succ_le_of_lt hpos
    have hsub : n - j - 1 = n - (j + 1) := by
      simpa [Nat.succ_eq_add_one] using (Eq.symm (Nat.sub_succ n j))
    calc
      n - j = (n - j - 1) + 1 := by
        symm
        exact Nat.sub_add_cancel hle
      _ = (n - (j + 1)) + 1 := by simpa [hsub]

  have hnsub' : n - j = Nat.succ (n - (j + 1)) := by
    calc
      n - j = (n - (j + 1)) + 1 := hnsub
      _ = Nat.succ (n - (j + 1)) := by
        simpa using (Nat.add_one (n - (j + 1)))

  have hcardRow : ∀ x < i,
      ({t ∈ Finset.range (n - j) | (grid[x]!)[j + t]! < (0 : ℤ)}).card
        =
      ({t ∈ Finset.range (n - (j + 1)) | (grid[x]!)[j + Nat.succ t]! < (0 : ℤ)}).card := by
    intro x hx
    let S_old : Finset Nat := {t ∈ Finset.range (n - j) | (grid[x]!)[j + t]! < (0 : ℤ)}
    let S_new : Finset Nat := {t ∈ Finset.range (n - (j + 1)) | (grid[x]!)[j + Nat.succ t]! < (0 : ℤ)}

    have h0not : (0 : Nat) ∉ S_old := by
      have : ¬ (grid[x]!)[j]! < (0 : ℤ) := not_lt_of_ge (hnonneg x hx)
      simp [S_old, this]

    have hEq : S_old = S_new.image Nat.succ := by
      ext t
      constructor
      · intro ht
        have htne0 : t ≠ 0 := by
          intro htz
          subst htz
          exact h0not ht
        rcases Nat.exists_eq_succ_of_ne_zero htne0 with ⟨u, rfl⟩
        have ht' : Nat.succ u ∈ Finset.range (n - j) ∧ (grid[x]!)[j + Nat.succ u]! < (0 : ℤ) := by
          simpa [S_old] using ht
        have hu_lt : u < n - (j + 1) := by
          have : Nat.succ u < Nat.succ (n - (j + 1)) := by
            simpa [hnsub'] using ht'.1
          exact Nat.succ_lt_succ_iff.mp this
        have hu_mem : u ∈ S_new := by
          simp [S_new, Finset.mem_range, hu_lt, ht'.2]
        exact Finset.mem_image.mpr ⟨u, hu_mem, rfl⟩
      · intro ht
        rcases Finset.mem_image.mp ht with ⟨u, hu, rfl⟩
        have hu' : u ∈ Finset.range (n - (j + 1)) ∧ (grid[x]!)[j + Nat.succ u]! < (0 : ℤ) := by
          simpa [S_new] using hu
        have hu_lt : u < n - (j + 1) := Finset.mem_range.mp hu'.1
        have hsucc_lt : Nat.succ u < n - j := by
          have : Nat.succ u < Nat.succ (n - (j + 1)) := Nat.succ_lt_succ hu_lt
          simpa [hnsub'] using this
        simp [S_old, Finset.mem_range, hsucc_lt, hu'.2]

    have hcard_image : (S_new.image Nat.succ).card = S_new.card := by
      simpa using
        (Finset.card_image_of_injective (s := S_new) (f := Nat.succ) Nat.succ_injective)

    calc
      S_old.card = (S_new.image Nat.succ).card := by simpa [S_old, hEq]
      _ = S_new.card := by simpa [hcard_image]

  have hsum :
      (∑ x ∈ Finset.range i,
          ({t ∈ Finset.range (n - (j + 1)) | (grid[x]!)[j + Nat.succ t]! < (0 : ℤ)}).card)
        =
      (∑ x ∈ Finset.range i,
          ({t ∈ Finset.range (n - j) | (grid[x]!)[j + t]! < (0 : ℤ)}).card) := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    have hxlt : x < i := Finset.mem_range.mp hx
    simpa [n] using (hcardRow x hxlt).symm

  have hsum' :
      cnt + (∑ x ∈ Finset.range i,
          ({t ∈ Finset.range (n - (j + 1)) | (grid[x]!)[j + Nat.succ t]! < (0 : ℤ)}).card)
        =
      cnt + (∑ x ∈ Finset.range i,
          ({t ∈ Finset.range (n - j) | (grid[x]!)[j + t]! < (0 : ℤ)}).card) :=
    congrArg (fun t => cnt + t) hsum

  have hsum'' :
      cnt + (∑ x ∈ Finset.range i,
          ({t ∈ Finset.range (n - (j + 1)) | (grid[x]!)[j + 1 + t]! < (0 : ℤ)}).card)
        =
      cnt + (∑ x ∈ Finset.range i,
          ({t ∈ Finset.range (n - j) | (grid[x]!)[j + t]! < (0 : ℤ)}).card) := by
    simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hsum'

  simpa [n, Nat.add_assoc] using (hsum''.trans invariant_inv_accounting)

theorem goal_2
    (grid : Array (Array ℤ))
    (i_1 : ℕ)
    (i_2 : ℕ)
    (j_1 : ℕ)
    (a : i_2 ≤ grid.size)
    (require_1 : (OfNat.ofNat 0 < grid.size ∧ (OfNat.ofNat 0 < if grid = #[] then OfNat.ofNat 0 else grid[OfNat.ofNat 0]!.size) ∧ ∀ i < grid.size, grid[i]!.size = if grid = #[] then OfNat.ofNat 0 else grid[OfNat.ofNat 0]!.size) ∧ (∀ i < grid.size, ∀ (j : ℕ), (j + OfNat.ofNat 1 < if grid = #[] then OfNat.ofNat 0 else grid[OfNat.ofNat 0]!.size) → (grid[i]!)[j + OfNat.ofNat 1]! ≤ (grid[i]!)[j]!) ∧ ∀ (i : ℕ), i + OfNat.ofNat 1 < grid.size → ∀ j < if grid = #[] then OfNat.ofNat 0 else grid[OfNat.ofNat 0]!.size, (grid[i + OfNat.ofNat 1]!)[j]! ≤ (grid[i]!)[j]!)
    (a_1 : j_1 ≤ if grid = #[] then OfNat.ofNat 0 else grid[OfNat.ofNat 0]!.size)
    (done_1 : OfNat.ofNat 0 < i_2 → (if grid = #[] then OfNat.ofNat 0 else grid[OfNat.ofNat 0]!.size) ≤ j_1)
    (invariant_inv_accounting : i_1 + ∑ x ∈ Finset.range i_2, {x_1 ∈ Finset.range ((if grid = #[] then OfNat.ofNat 0 else grid[OfNat.ofNat 0]!.size) - j_1) | (grid[x]!)[j_1 + x_1]! < OfNat.ofNat 0}.card = ∑ x ∈ Finset.range grid.size, {x_1 ∈ Finset.range (if grid = #[] then OfNat.ofNat 0 else grid[OfNat.ofNat 0]!.size) | (grid[x]!)[x_1]! < OfNat.ofNat 0}.card)
    : postcondition grid i_1 := by
  classical

  -- Abbreviation for the number of columns used in the invariant.
  set n0 : Nat := (if grid = #[] then 0 else grid[0]!.size) with hn0

  -- Relate `numCols` to the invariant's `if grid = #[]`-based definition.
  have hnum : numCols grid = n0 := by
    by_cases he : grid = (#[] : Array (Array ℤ))
    · subst he
      simp [numCols, n0]
    · have hs : grid.size ≠ 0 := by
        intro hs0
        have : grid = (#[] : Array (Array ℤ)) := (Array.size_eq_zero_iff.mp hs0)
        exact he this
      simp [numCols, n0, he, hs]

  -- The "remaining rectangle" count is zero at loop exit.
  have hrem0 :
      (∑ x ∈ Finset.range i_2,
          {x_1 ∈ Finset.range (n0 - j_1) | (grid[x]!)[j_1 + x_1]! < 0}.card) = 0 := by
    by_cases hpos : 0 < i_2
    · have hle : n0 ≤ j_1 := by
        -- `done_1` is stated with the `if grid = #[]` expression.
        simpa [hn0] using done_1 hpos
      have hsub : n0 - j_1 = 0 := Nat.sub_eq_zero_of_le hle
      simp [hsub]
    · have hi2 : i_2 = 0 := Nat.eq_zero_of_not_pos hpos
      simp [hi2]

  -- Rewrite the accounting invariant in terms of `n0`.
  have inv' :
      i_1 +
            ∑ x ∈ Finset.range i_2,
              {x_1 ∈ Finset.range (n0 - j_1) | (grid[x]!)[j_1 + x_1]! < 0}.card
          =
          ∑ x ∈ Finset.range grid.size,
            {x_1 ∈ Finset.range n0 | (grid[x]!)[x_1]! < 0}.card := by
    -- rewrite the `if grid = #[]` column count as `n0`
    simpa [n0] using invariant_inv_accounting

  have hi1_eq_total :
      i_1 =
        ∑ x ∈ Finset.range grid.size,
          {x_1 ∈ Finset.range n0 | (grid[x]!)[x_1]! < 0}.card := by
    -- eliminate the remaining term using `hrem0`
    simpa [hrem0] using inv'

  -- Convert the "sum of cards" form into the `negCount` definition.
  have htotal_eq_negCount :
      (∑ x ∈ Finset.range grid.size,
          {x_1 ∈ Finset.range n0 | (grid[x]!)[x_1]! < 0}.card) = negCount grid := by
    -- First rewrite each row's card as a sum of indicator functions.
    have hcard_as_sum :
        (∑ x ∈ Finset.range grid.size,
            {x_1 ∈ Finset.range n0 | (grid[x]!)[x_1]! < 0}.card)
          =
          (Finset.range grid.size).sum (fun i =>
            (Finset.range n0).sum (fun j => if (grid[i]!)[j]! < 0 then 1 else 0)) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      -- `Finset.card_filter` is exactly the needed bridge.
      simpa using
        (Finset.card_filter (p := fun j : Nat => (grid[i]!)[j]! < 0) (s := Finset.range n0))

    -- Then unfold `negCount` and rewrite `numCols` to `n0`.
    have hnegCount_unfold :
        negCount grid =
          (Finset.range grid.size).sum (fun i =>
            (Finset.range n0).sum (fun j => if (grid[i]!)[j]! < 0 then 1 else 0)) := by
      simp [negCount, hnum, hn0]

    -- Combine the two rewrites.
    calc
      (∑ x ∈ Finset.range grid.size,
          {x_1 ∈ Finset.range n0 | (grid[x]!)[x_1]! < 0}.card)
          = (Finset.range grid.size).sum (fun i =>
              (Finset.range n0).sum (fun j => if (grid[i]!)[j]! < 0 then 1 else 0)) := by
              exact hcard_as_sum
      _ = negCount grid := by
          simpa using hnegCount_unfold.symm

  -- Finish.
  unfold postcondition
  exact hi1_eq_total.trans htotal_eq_negCount


prove_correct CountNegatives by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at * <;> expose_names); try (conv => congr <;> simp) ; try rfl; try expose_names)
  exact (goal_0 grid cnt i j a if_pos require_1 a_1 invariant_inv_accounting a_2)
  exact (goal_1 grid cnt i j a require_1 invariant_inv_accounting a_2 a_3 if_neg)
  exact (goal_2 grid i_1 i_2 j_1 a require_1 a_1 done_1 invariant_inv_accounting)
end Proof
