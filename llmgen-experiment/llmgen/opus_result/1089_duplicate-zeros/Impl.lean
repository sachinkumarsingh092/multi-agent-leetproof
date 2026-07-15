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
    1089. Duplicate Zeros: duplicate each occurrence of 0 in a fixed-length integer array, shifting right and truncating.
    Natural language breakdown:
    1. Input is an array of integers with a fixed length n.
    2. We define a conceptual output stream obtained by scanning the input left-to-right.
    3. Each nonzero input element contributes exactly one output element equal to itself.
    4. Each zero input element contributes exactly two consecutive output elements, both equal to 0.
    5. The actual returned array is the first n elements of this conceptual output stream (truncate to length n).
    6. Because the original problem updates in-place and returns nothing, we model the modified array as a returned array.
    7. Therefore the result must have the same size as the input.
    8. Every output index j (0 ≤ j < n) is produced by a unique input index i, determined by how many output elements are produced by prefixes of the input.
    Your algorithm should run in **O(n)** time and **O(1)** extra space.
-/

section Specs
-- Helper: producedLen arr k = number of conceptual output elements produced by the first k input elements.
-- Each nonzero produces 1; each zero produces 2.
-- We use foldl over a prefix (arr.take k) to avoid recursion.
-- Note: we use Int = 0 propositionally; this is fine (not Float).
def producedLen (arr : Array Int) (k : Nat) : Nat :=
  (arr.take k).foldl (fun (acc : Nat) (x : Int) => if x = 0 then acc + 2 else acc + 1) 0

-- Precondition: none.
def precondition (arr : Array Int) : Prop :=
  True

-- Postcondition: result is the length-preserving truncation of duplicating zeros.
-- We characterize the mapping index-wise using the prefix produced lengths.
-- For each output index j, there is a unique input index i < n such that
-- producedLen arr i ≤ j < producedLen arr (i+1). The output value equals arr[i], but if arr[i]=0 then it is 0.
def postcondition (arr : Array Int) (result : Array Int) : Prop :=
  result.size = arr.size ∧
  (∀ (j : Nat), j < arr.size →
    ∃! (i : Nat),
      i < arr.size ∧
      producedLen arr i ≤ j ∧
      j < producedLen arr (i + 1) ∧
      result[j]! = (if arr[i]! = 0 then (0 : Int) else arr[i]!))
end Specs

section Impl
method DuplicateZeros (arr : Array Int)
  return (result : Array Int)
  require precondition arr
  ensures postcondition arr result
  do
  let n := arr.size
  if n = 0 then
    return arr
  else
    -- First pass: find how many input elements map into the output
    let mut possibleDups : Nat := 0
    let mut length_ : Nat := 0
    let mut i : Nat := 0
    while i < n
      -- possibleDups = i: both start at 0 and increment together (only when no break)
      -- Init: 0 = 0. Pres: both increment by 1. Suff: relates possibleDups to loop counter.
      invariant "poss_eq_i" possibleDups = i
      -- length_ tracks producedLen arr i: the cumulative output positions for first i elements
      -- Init: producedLen arr 0 = foldl ... (take 0) = foldl ... #[] = 0 = length_.
      -- Pres: body adds 2 if arr[i]=0, else 1, matching producedLen definition.
      -- Suff: after loop, relates length_ to producedLen for postcondition.
      invariant "length_eq" length_ = producedLen arr i
      -- i bounded by n
      invariant "i_bound" i ≤ n
      -- frame: n = arr.size throughout
      invariant "n_is_size" n = arr.size
      -- n > 0 from else branch
      invariant "n_pos" n > 0
      -- length_ ≥ i: each element contributes at least 1
      -- Init: 0 ≥ 0. Pres: length_ increases by ≥1, i increases by 1. Suff: at normal exit i≥n ⟹ length_≥n.
      invariant "length_ge_i" length_ ≥ i
      -- done_with: on break, length_ ≥ n; on normal exit (i≥n), length_ ≥ i ≥ n
      done_with length_ ≥ n
      decreasing n - i
    do
      if arr[i]! = 0 then
        length_ := length_ + 2
      else
        length_ := length_ + 1
      if length_ >= n then
        break
      possibleDups := possibleDups + 1
      i := i + 1
    let lastIdx : Nat := possibleDups

    -- Second pass: write from right to left
    let mut result := Array.replicate n (0 : Int)
    let mut j : Nat := n - 1
    let mut k : Nat := lastIdx

    -- Handle edge case: if length_ > n, the last element is a zero that only partially fits
    let mut edgeCase : Bool := false
    if length_ > n then
      result := result.set! j (0 : Int)
      if j > 0 then
        j := j - 1
      else
        return result
      if k > 0 then
        k := k - 1
      else
        return result
      edgeCase := true

    if edgeCase = false then
      pure ()

    -- Now fill from position k down to 0
    let mut done : Bool := false
    while done = false
      -- result.size = n: Array.replicate gives size n, set! preserves size
      invariant "result_size" result.size = n
      -- frame invariants
      invariant "n_is_size2" n = arr.size
      invariant "n_pos2" n > 0
      -- j < n when loop still running: initially j = n-1 (possibly adjusted), only decreases
      invariant "j_bound" done = false → j < n
      -- k bounded by lastIdx which ≤ i ≤ n
      invariant "k_bound" k ≤ n
      -- Decreasing: each iteration decreases k or sets done=true
      decreasing k + (if done = false then 1 else 0)
    do
      if arr[k]! = 0 then
        result := result.set! j (0 : Int)
        if j > 0 then
          j := j - 1
          result := result.set! j (0 : Int)
        else
          pure ()
      else
        result := result.set! j arr[k]!

      if k = 0 then
        done := true
      else
        k := k - 1
        if j > 0 then
          j := j - 1
        else
          done := true

    return result
end Impl

section TestCases
-- Test case 1: Example 1
-- Input: [1,0,2,3,0,4,5,0]
-- Output: [1,0,0,2,3,0,0,4]
def test1_arr : Array Int := #[1, 0, 2, 3, 0, 4, 5, 0]
def test1_Expected : Array Int := #[1, 0, 0, 2, 3, 0, 0, 4]

-- Test case 2: Example 2 (no zeros)
def test2_arr : Array Int := #[1, 2, 3]
def test2_Expected : Array Int := #[1, 2, 3]

-- Test case 3: empty array
def test3_arr : Array Int := #[]
def test3_Expected : Array Int := #[]

-- Test case 4: single element zero
def test4_arr : Array Int := #[0]
def test4_Expected : Array Int := #[0]

-- Test case 5: single element nonzero
def test5_arr : Array Int := #[7]
def test5_Expected : Array Int := #[7]

-- Test case 6: all zeros (truncation preserves all zeros)
def test6_arr : Array Int := #[0, 0, 0]
def test6_Expected : Array Int := #[0, 0, 0]

-- Test case 7: zeros causing truncation of later elements
-- [1,0,0,2] -> conceptual: 1,0,0,0,0,2 -> take 4 => [1,0,0,0]
def test7_arr : Array Int := #[1, 0, 0, 2]
def test7_Expected : Array Int := #[1, 0, 0, 0]

-- Test case 8: negative values with zeros
-- [0,-1,0,2] -> conceptual: 0,0,-1,0,0,2 -> take 4 => [0,0,-1,0]
def test8_arr : Array Int := #[0, -1, 0, 2]
def test8_Expected : Array Int := #[0, 0, -1, 0]

-- Test case 9: trailing zero does not create a visible extra element after truncation
-- [1,2,0] -> conceptual: 1,2,0,0 -> take 3 => [1,2,0]
def test9_arr : Array Int := #[1, 2, 0]
def test9_Expected : Array Int := #[1, 2, 0]

-- Recommend to validate: boundary sizes (0/1), multiple zeros, truncation at end
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((DuplicateZeros test1_arr).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((DuplicateZeros test2_arr).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((DuplicateZeros test3_arr).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((DuplicateZeros test4_arr).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((DuplicateZeros test5_arr).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((DuplicateZeros test6_arr).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((DuplicateZeros test7_arr).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((DuplicateZeros test8_arr).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((DuplicateZeros test9_arr).run), DivM.res test9_Expected ]
end Assertions

section Pbt
velvet_plausible_test DuplicateZeros (config := { maxMs := some 20000 })
end Pbt
