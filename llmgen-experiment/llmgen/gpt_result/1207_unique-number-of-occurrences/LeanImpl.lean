import Lean
import Mathlib.Tactic
import Velvet.Std

set_option maxHeartbeats 10000000

section Specs
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false

/- Problem Description
    1207. Unique Number of Occurrences: decide whether all element-frequency counts in an integer array are pairwise distinct.
    **Important: complexity should be O(n + R²) time and O(R) space**, where R = 2001 is the range of values.
    Natural language breakdown:
    1. Input is an array of integers.
    2. For each integer value v that appears in the array, define occ(v) as the number of indices i with arr[i] = v.
    3. The output is true exactly when for any two distinct values x and y that both appear in the array, occ(x) ≠ occ(y).
    4. Values that do not appear in the array are irrelevant to the uniqueness condition.
    5. The given constraints restrict each element to the range [-1000, 1000].
-/

-- Helper predicate for the stated input-range constraint.
def inProblemRange (x : Int) : Prop :=
  (-1000 ≤ x) ∧ (x ≤ 1000)

-- The core semantic property: occurrence counts are unique among values that appear.
def countsAreUnique (arr : Array Int) : Prop :=
  ∀ (x : Int) (y : Int), x ≠ y → x ∈ arr → y ∈ arr → arr.count x ≠ arr.count y

-- Preconditions
-- We adopt the problem's stated range constraint as an explicit precondition.
def precondition (arr : Array Int) : Prop :=
  ∀ (i : Nat), i < arr.size → inProblemRange (arr[i]!)

-- Postconditions
-- result is true iff the array has unique occurrence counts among all values that appear.
def postcondition (arr : Array Int) (result : Bool) : Prop :=
  (result = true ↔ countsAreUnique arr)
end Specs

section Impl
def implementation (arr : Array Int) : Bool :=
  -- Range size R = 2001 for values in [-1000, 1000].
  let R : Nat := 2001
  let offset : Int := 1000
  let idxOf (x : Int) : Nat := Int.toNat (x + offset)

  -- Update frequency table for one element.
  let updateFreq (freq : Array Nat) (x : Int) : Array Nat :=
    let i := idxOf x
    if h : i < freq.size then
      let c := freq[i] -- safe under `h`
      freq.set! i (c + 1)
    else
      freq

  let initFreq : Array Nat := Array.mkArray R 0
  let freq : Array Nat := arr.foldl updateFreq initFreq

  -- `seen[c] = true` means some value has occurred exactly `c` times.
  let seenSize : Nat := arr.size + 1

  let rec checkCounts (i : Nat) (seen : Array Bool) : Bool :=
    if h : i < freq.size then
      let c : Nat := freq[i]
      if c = 0 then
        checkCounts (i + 1) seen
      else
        -- Use `get!`/`set!` to avoid proof obligations (counts are always ≤ arr.size).
        if seen.get! c then
          false
        else
          checkCounts (i + 1) (seen.set! c true)
    else
      true

  checkCounts 0 (Array.mkArray seenSize false)
end Impl

section TestCases
-- Test case 1: Example 1
-- arr = [1,2,2,1,1,3] has counts: 1↦3, 2↦2, 3↦1 (all distinct)
def test1_arr : Array Int := #[1, 2, 2, 1, 1, 3]
def test1_Expected : Bool := true

-- Test case 2: Example 2
-- arr = [1,2] has counts 1↦1, 2↦1 (not unique)
def test2_arr : Array Int := #[1, 2]
def test2_Expected : Bool := false

-- Test case 3: Example 3
-- arr = [-3,0,1,-3,1,1,1,-3,10,0] has counts -3↦3, 0↦2, 1↦4, 10↦1 (all distinct)
def test3_arr : Array Int := #[-3, 0, 1, -3, 1, 1, 1, -3, 10, 0]
def test3_Expected : Bool := true

-- Test case 4: Empty array (vacuously unique)
def test4_arr : Array Int := #[]
def test4_Expected : Bool := true

-- Test case 5: Singleton array (vacuously unique)
def test5_arr : Array Int := #[0]
def test5_Expected : Bool := true

-- Test case 6: All same value (only one distinct value, so unique)
def test6_arr : Array Int := #[7, 7, 7, 7]
def test6_Expected : Bool := true

-- Test case 7: Two distinct values with the same count
-- counts: 1↦2, 2↦2
def test7_arr : Array Int := #[1, 1, 2, 2]
def test7_Expected : Bool := false

-- Test case 8: Three values where two share the same count
-- counts: 1↦2, 2↦1, 3↦2
def test8_arr : Array Int := #[1, 3, 1, 2, 3]
def test8_Expected : Bool := false

-- Test case 9: Boundary values within allowed range
-- counts: -1000↦1, 1000↦2, 0↦3 (all distinct)
def test9_arr : Array Int := #[-1000, 1000, 1000, 0, 0, 0]
def test9_Expected : Bool := true

-- Recommend to validate: test1_arr, test3_arr, test9_arr
end TestCases

section Assertions
-- Test case 1
#assert_same_evaluation #[(implementation test1_arr), test1_Expected]

-- Test case 2
#assert_same_evaluation #[(implementation test2_arr), test2_Expected]

-- Test case 3
#assert_same_evaluation #[(implementation test3_arr), test3_Expected]

-- Test case 4
#assert_same_evaluation #[(implementation test4_arr), test4_Expected]

-- Test case 5
#assert_same_evaluation #[(implementation test5_arr), test5_Expected]

-- Test case 6
#assert_same_evaluation #[(implementation test6_arr), test6_Expected]

-- Test case 7
#assert_same_evaluation #[(implementation test7_arr), test7_Expected]

-- Test case 8
#assert_same_evaluation #[(implementation test8_arr), test8_Expected]

-- Test case 9
#assert_same_evaluation #[(implementation test9_arr), test9_Expected]
end Assertions

section Proof
theorem correctness_goal_0_0
    (arr : Array ℤ)
    (h_precond : precondition arr)
    : implementation.checkCounts
      (Array.foldl
        (fun freq x =>
          if h : (x + 1000).toNat < freq.size then freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
          else freq)
        (mkArray 2001 0) arr)
      0 (mkArray (arr.size + 1) false) =
    true ↔
  ∀ (i j : ℕ),
    i <
        (Array.foldl
            (fun freq x =>
              if h : (x + 1000).toNat < freq.size then freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
              else freq)
            (mkArray 2001 0) arr).size →
      j <
          (Array.foldl
              (fun freq x =>
                if h : (x + 1000).toNat < freq.size then
                  freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
                else freq)
              (mkArray 2001 0) arr).size →
        i ≠ j →
          (Array.foldl
                    (fun freq x =>
                      if h : (x + 1000).toNat < freq.size then
                        freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
                      else freq)
                    (mkArray 2001 0) arr).get!
                i ≠
              0 →
            (Array.foldl
                      (fun freq x =>
                        if h : (x + 1000).toNat < freq.size then
                          freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
                        else freq)
                      (mkArray 2001 0) arr).get!
                  j ≠
                0 →
              (Array.foldl
                      (fun freq x =>
                        if h : (x + 1000).toNat < freq.size then
                          freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
                        else freq)
                      (mkArray 2001 0) arr).get!
                  i ≠
                (Array.foldl
                      (fun freq x =>
                        if h : (x + 1000).toNat < freq.size then
                          freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
                        else freq)
                      (mkArray 2001 0) arr).get!
                  j := by
    sorry

theorem precond_getElem (arr : Array Int) (h_precond : precondition arr)
    {i : Nat} (hi : i < arr.size) : inProblemRange (arr[i]'hi) := by
  -- start from the precondition on `get!`
  have h0 : inProblemRange (arr[i]!) := h_precond i hi
  -- rewrite `get!` to `getElem` under `hi`
  have hEq : arr[i]! = arr[i]'hi := by
    -- `get!` is `getD` with default; in bounds, it is the same as `getElem`
    simp [Array.get!_eq_getD, Array.getD, Array.get?_eq_getElem?, hi]
  simpa [hEq] using h0


theorem correctness_goal_0_1
    (arr : Array ℤ)
    (h_precond : precondition arr)
    (h_checkCounts_spec : implementation.checkCounts
      (Array.foldl
        (fun freq x =>
          if h : (x + 1000).toNat < freq.size then freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
          else freq)
        (mkArray 2001 0) arr)
      0 (mkArray (arr.size + 1) false) =
    true ↔
  ∀ (i j : ℕ),
    i <
        (Array.foldl
            (fun freq x =>
              if h : (x + 1000).toNat < freq.size then freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
              else freq)
            (mkArray 2001 0) arr).size →
      j <
          (Array.foldl
              (fun freq x =>
                if h : (x + 1000).toNat < freq.size then
                  freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
                else freq)
              (mkArray 2001 0) arr).size →
        i ≠ j →
          (Array.foldl
                    (fun freq x =>
                      if h : (x + 1000).toNat < freq.size then
                        freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
                      else freq)
                    (mkArray 2001 0) arr).get!
                i ≠
              0 →
            (Array.foldl
                      (fun freq x =>
                        if h : (x + 1000).toNat < freq.size then
                          freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
                        else freq)
                      (mkArray 2001 0) arr).get!
                  j ≠
                0 →
              (Array.foldl
                      (fun freq x =>
                        if h : (x + 1000).toNat < freq.size then
                          freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
                        else freq)
                      (mkArray 2001 0) arr).get!
                  i ≠
                (Array.foldl
                      (fun freq x =>
                        if h : (x + 1000).toNat < freq.size then
                          freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
                        else freq)
                      (mkArray 2001 0) arr).get!
                  j)
    : (∀ (i j : ℕ),
    i <
        (Array.foldl
            (fun freq x =>
              if h : (x + 1000).toNat < freq.size then freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
              else freq)
            (mkArray 2001 0) arr).size →
      j <
          (Array.foldl
              (fun freq x =>
                if h : (x + 1000).toNat < freq.size then
                  freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
                else freq)
              (mkArray 2001 0) arr).size →
        i ≠ j →
          (Array.foldl
                    (fun freq x =>
                      if h : (x + 1000).toNat < freq.size then
                        freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
                      else freq)
                    (mkArray 2001 0) arr).get!
                i ≠
              0 →
            (Array.foldl
                      (fun freq x =>
                        if h : (x + 1000).toNat < freq.size then
                          freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
                        else freq)
                      (mkArray 2001 0) arr).get!
                  j ≠
                0 →
              (Array.foldl
                      (fun freq x =>
                        if h : (x + 1000).toNat < freq.size then
                          freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
                        else freq)
                      (mkArray 2001 0) arr).get!
                  i ≠
                (Array.foldl
                      (fun freq x =>
                        if h : (x + 1000).toNat < freq.size then
                          freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
                        else freq)
                      (mkArray 2001 0) arr).get!
                  j) ↔
  countsAreUnique arr := by
    sorry

theorem correctness_goal_0
    (arr : Array ℤ)
    (h_precond : precondition arr)
    : implementation arr = true ↔ countsAreUnique arr := by
  classical

  -- Abbreviation: the frequency table produced by the fold.
  have h_checkCounts_spec :
      implementation.checkCounts
          (Array.foldl
            (fun freq x =>
              if h : (x + 1000).toNat < freq.size then
                freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
              else
                freq)
            (Array.mkArray 2001 0) arr)
          0 (Array.mkArray (arr.size + 1) false)
        = true
        ↔
      (∀ i j : Nat,
        i <
            (Array.foldl
              (fun freq x =>
                if h : (x + 1000).toNat < freq.size then
                  freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
                else
                  freq)
              (Array.mkArray 2001 0) arr).size →
          j <
              (Array.foldl
                (fun freq x =>
                  if h : (x + 1000).toNat < freq.size then
                    freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
                  else
                    freq)
                (Array.mkArray 2001 0) arr).size →
          i ≠ j →
          (Array.foldl
                (fun freq x =>
                  if h : (x + 1000).toNat < freq.size then
                    freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
                  else
                    freq)
                (Array.mkArray 2001 0) arr).get! i ≠ 0 →
          (Array.foldl
                (fun freq x =>
                  if h : (x + 1000).toNat < freq.size then
                    freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
                  else
                    freq)
                (Array.mkArray 2001 0) arr).get! j ≠ 0 →
          (Array.foldl
                (fun freq x =>
                  if h : (x + 1000).toNat < freq.size then
                    freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
                  else
                    freq)
                (Array.mkArray 2001 0) arr).get! i ≠
            (Array.foldl
                (fun freq x =>
                  if h : (x + 1000).toNat < freq.size then
                    freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
                  else
                    freq)
                (Array.mkArray 2001 0) arr).get! j) := by
    expose_names; exact (correctness_goal_0_0 arr h_precond)

  have h_bridge :
      (∀ i j : Nat,
        i <
            (Array.foldl
              (fun freq x =>
                if h : (x + 1000).toNat < freq.size then
                  freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
                else
                  freq)
              (Array.mkArray 2001 0) arr).size →
          j <
              (Array.foldl
                (fun freq x =>
                  if h : (x + 1000).toNat < freq.size then
                    freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
                  else
                    freq)
                (Array.mkArray 2001 0) arr).size →
          i ≠ j →
          (Array.foldl
                (fun freq x =>
                  if h : (x + 1000).toNat < freq.size then
                    freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
                  else
                    freq)
                (Array.mkArray 2001 0) arr).get! i ≠ 0 →
          (Array.foldl
                (fun freq x =>
                  if h : (x + 1000).toNat < freq.size then
                    freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
                  else
                    freq)
                (Array.mkArray 2001 0) arr).get! j ≠ 0 →
          (Array.foldl
                (fun freq x =>
                  if h : (x + 1000).toNat < freq.size then
                    freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
                  else
                    freq)
                (Array.mkArray 2001 0) arr).get! i ≠
            (Array.foldl
                (fun freq x =>
                  if h : (x + 1000).toNat < freq.size then
                    freq.setIfInBounds (x + 1000).toNat (freq[(x + 1000).toNat] + 1)
                  else
                    freq)
                (Array.mkArray 2001 0) arr).get! j)
        ↔ countsAreUnique arr := by
    expose_names; exact (correctness_goal_0_1 arr h_precond h_checkCounts_spec)

  -- Unfold `implementation` and rewrite using the two key lemmas.
  simp [implementation, h_checkCounts_spec, h_bridge]

theorem correctness_goal
    (arr : Array Int)
    (h_precond : precondition arr)
    : postcondition arr (implementation arr) := by
  have h_main : implementation arr = true ↔ countsAreUnique arr := by
    expose_names; exact (correctness_goal_0 arr h_precond)
  simpa [postcondition] using h_main
end Proof
