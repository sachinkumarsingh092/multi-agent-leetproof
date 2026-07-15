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
    2149. Rearrange Array Elements by Sign: Rearrange an even-length integer array with equal numbers of positive and negative elements so that signs alternate starting with a positive, while preserving relative order within each sign.
    **Important: complexity should be O(n) time and O(n) space**
    Natural language breakdown:
    1. The input is a 0-indexed array of integers of even length.
    2. Every element is either strictly positive or strictly negative (no zeros).
    3. The number of positive elements equals the number of negative elements.
    4. The output is an array of the same length that is a rearrangement (permutation) of the input.
    5. The output starts with a positive element when the array is nonempty.
    6. Consecutive elements in the output have opposite signs (equivalently, indices with even parity are positive and odd parity are negative).
    7. Among all positives (respectively negatives), their relative order in the output is the same as in the input (stable with respect to sign).
-/

section Specs
-- Helper predicates as Bool for use with Array.filter/countP.
def isPosB (x : Int) : Bool := decide (x > 0)
def isNegB (x : Int) : Bool := decide (x < 0)

def countPos (nums : Array Int) : Nat := nums.countP isPosB

def countNeg (nums : Array Int) : Nat := nums.countP isNegB

def allNonZero (nums : Array Int) : Prop :=
  ∀ (i : Nat), i < nums.size → nums[i]! ≠ 0

-- Parity-based sign pattern for the desired result.
def alternatesStartingPos (arr : Array Int) : Prop :=
  ∀ (i : Nat), i < arr.size →
    ((i % 2 = 0) → arr[i]! > 0) ∧
    ((i % 2 = 1) → arr[i]! < 0)

-- Stable order within sign can be characterized by equality of the sign-filtered subsequences.
def stableBySign (nums : Array Int) (result : Array Int) : Prop :=
  result.filter isPosB = nums.filter isPosB ∧
  result.filter isNegB = nums.filter isNegB

-- Preconditions: even length, no zeros, equal number of positives and negatives.
def precondition (nums : Array Int) : Prop :=
  nums.size % 2 = 0 ∧
  allNonZero nums ∧
  countPos nums = nums.size / 2 ∧
  countNeg nums = nums.size / 2

-- Postconditions: permutation, correct alternating sign pattern, starts with positive if nonempty,
-- and stability of relative order within each sign.
def postcondition (nums : Array Int) (result : Array Int) : Prop :=
  result.size = nums.size ∧
  result.Perm nums ∧
  alternatesStartingPos result ∧
  (result.size > 0 → result[0]! > 0) ∧
  stableBySign nums result
end Specs

section Impl
method RearrangeArrayElementsBySign (nums : Array Int)
  return (result : Array Int)
  require precondition nums
  ensures postcondition nums result
  do
  -- Collect positives and negatives in stable order
  let mut pos : Array Int := Array.empty
  let mut neg : Array Int := Array.empty

  let mut i : Nat := 0
  while i < nums.size
    -- i tracks how much of nums has been processed
    invariant "collect_bounds" i ≤ nums.size
    -- pos/neg are exactly the stable sign-filtered subsequences of the processed prefix
    invariant "collect_pos" pos = (nums.extract 0 i).filter isPosB
    invariant "collect_neg" neg = (nums.extract 0 i).filter isNegB
    decreasing nums.size - i
  do
    let x := nums[i]!
    if x > 0 then
      pos := pos.push x
    else
      -- By precondition, x is nonzero, so x < 0 here.
      neg := neg.push x
    i := i + 1

  -- Interleave starting with positive.
  let mut res : Array Int := Array.replicate nums.size 0
  let mut j : Nat := 0
  while j < nums.size
    -- j is the output prefix length already filled
    invariant "interleave_bounds" j ≤ nums.size
    invariant "interleave_res_size" res.size = nums.size
    -- pos/neg are the full stable sign-filtered subsequences of nums
    invariant "interleave_pos_def" pos = nums.filter isPosB
    invariant "interleave_neg_def" neg = nums.filter isNegB
    -- sizes match precondition (needed for safe indexing into pos/neg)
    invariant "interleave_pos_size" pos.size = nums.size / 2
    invariant "interleave_neg_size" neg.size = nums.size / 2
    -- already-filled positions satisfy the intended interleaving mapping
    invariant "interleave_prefix" ∀ k : Nat, k < j →
        ((k % 2 = 0) → res[k]! = pos[k / 2]!) ∧
        ((k % 2 = 1) → res[k]! = neg[k / 2]!)
    decreasing nums.size - j
  do
    if j % 2 = 0 then
      res := res.set! j (pos[j / 2]!)
    else
      res := res.set! j (neg[j / 2]!)
    j := j + 1

  return res
end Impl

section TestCases
-- Test case 1: Example 1
-- Input: [3,1,-2,-5,2,-4]
-- Output: [3,-2,1,-5,2,-4]
def test1_nums : Array Int := #[3, 1, -2, -5, 2, -4]
def test1_Expected : Array Int := #[3, -2, 1, -5, 2, -4]

-- Test case 2: Example 2 (starts with a negative in input)
def test2_nums : Array Int := #[-1, 1]
def test2_Expected : Array Int := #[1, -1]

-- Test case 3: Empty array (degenerate but satisfies even length and equal counts)
def test3_nums : Array Int := #[]
def test3_Expected : Array Int := #[]

-- Test case 4: Smallest nontrivial already-correct alternating order
def test4_nums : Array Int := #[1, -1]
def test4_Expected : Array Int := #[1, -1]

-- Test case 5: Larger array where positives/negatives are grouped
-- Positives: [1,2,3], Negatives: [-1,-2,-3]
def test5_nums : Array Int := #[1, 2, 3, -1, -2, -3]
def test5_Expected : Array Int := #[1, -1, 2, -2, 3, -3]

-- Test case 6: Alternating input but begins with negative; must start with positive in output
-- Positives: [5,6], Negatives: [-5,-6]
def test6_nums : Array Int := #[-5, 5, -6, 6]
def test6_Expected : Array Int := #[5, -5, 6, -6]

-- Test case 7: Mixed order; checks stability within each sign
-- Positives in input: [2,4,6,8], Negatives: [-1,-3,-5,-7]
def test7_nums : Array Int := #[2, -1, 4, -3, 6, -5, 8, -7]
def test7_Expected : Array Int := #[2, -1, 4, -3, 6, -5, 8, -7]

-- Test case 8: All positives first but with different magnitudes; confirms stable order
-- Positives: [10,1,7], Negatives: [-2,-9,-3]
def test8_nums : Array Int := #[10, 1, 7, -2, -9, -3]
def test8_Expected : Array Int := #[10, -2, 1, -9, 7, -3]
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((RearrangeArrayElementsBySign test1_nums).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((RearrangeArrayElementsBySign test2_nums).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((RearrangeArrayElementsBySign test3_nums).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((RearrangeArrayElementsBySign test4_nums).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((RearrangeArrayElementsBySign test5_nums).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((RearrangeArrayElementsBySign test6_nums).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((RearrangeArrayElementsBySign test7_nums).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((RearrangeArrayElementsBySign test8_nums).run), DivM.res test8_Expected ]
end Assertions

section Pbt
velvet_plausible_test RearrangeArrayElementsBySign (config := { maxMs := some 20000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000

theorem goal_0
    (nums : Array ℤ)
    (i : ℕ)
    (invariant_collect_bounds : i ≤ nums.size)
    (if_pos : i < nums.size)
    (if_pos_1 : OfNat.ofNat 0 < nums[i]!)
    : (Array.filter isPosB (nums.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0) (min i nums.size)).push nums[i]! = Array.filter isPosB (nums.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) (OfNat.ofNat 0) (min (i + OfNat.ofNat 1) nums.size) := by
  have hmin_i : min i nums.size = i := by
    exact Nat.min_eq_left invariant_collect_bounds
  have hmin_succ : min (i + 1) nums.size = i + 1 := by
    exact Nat.min_eq_left (Nat.succ_le_of_lt if_pos)

  have hget : nums[i]! = nums[i] := by
    simp [Array.getElem!_eq_getD, Array.getD, Array.getElem?_eq_getElem, if_pos]

  have hpos : isPosB nums[i] = true := by
    have hi : (0 : ℤ) < nums[i] := by
      simpa [hget] using if_pos_1
    have hi' : nums[i] > 0 := by
      simpa using hi
    simpa [isPosB] using (decide_eq_true hi')

  have hextract : (nums.extract 0 i).push nums[i] = nums.extract 0 (i + 1) := by
    simpa using (@Array.push_extract_getElem ℤ nums 0 i if_pos)

  have hsize : (nums.extract 0 i).size = i := by
    simpa using (@Array.size_extract_of_le ℤ nums 0 i invariant_collect_bounds)

  have hw : i + 1 = (nums.extract 0 i).size + 1 := by
    simpa [hsize]

  -- simplify the goal (remove the `min` and `!` index)
  simp [hmin_i, hmin_succ, hget]

  -- update rule for filtering a pushed array, using that the pushed element is positive
  simpa [hextract, hsize] using
    (Array.filter_push_of_pos (p := isPosB) (xs := nums.extract 0 i) (a := nums[i])
      (stop := i + 1) hpos hw).symm

theorem goal_1
    (nums : Array ℤ)
    (i : ℕ)
    (if_pos : i < nums.size)
    (if_pos_1 : OfNat.ofNat 0 < nums[i]!)
    : Array.filter isNegB (nums.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0) (min i nums.size) = Array.filter isNegB (nums.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) (OfNat.ofNat 0) (min (i + OfNat.ofNat 1) nums.size) := by
  have hmin_i : min i nums.size = i := by
    exact Nat.min_eq_left (Nat.le_of_lt if_pos)
  have hmin_succ : min (i + 1) nums.size = i + 1 := by
    exact Nat.min_eq_left (Nat.succ_le_of_lt if_pos)

  have hget! : nums[i]! = nums[i] := by
    simp [Array.get!_eq_getD, Array.getD, if_pos]

  have hnotlt : ¬ nums[i] < 0 := by
    have : (0 : ℤ) < nums[i] := by
      simpa [hget!] using if_pos_1
    exact not_lt_of_ge (le_of_lt this)
  have hneg : ¬ isNegB nums[i] := by
    simp [isNegB, hnotlt]

  have hextract : nums.extract 0 (i + 1) = (nums.extract 0 i).push nums[i] := by
    simpa using (@Array.push_extract_getElem ℤ nums 0 i if_pos)

  have hsize : (nums.extract 0 i).size = i := by
    simp [Array.size_extract, hmin_i]

  have hfilter : Array.filter isNegB (nums.extract 0 (i + 1)) 0 (i + 1) = (nums.extract 0 i).filter isNegB := by
    have w : (i + 1) = (nums.extract 0 i).size + 1 := by
      simpa [hsize]
    -- rewrite the longer extract as a push and apply the library lemma
    rw [hextract]
    -- now it matches `filter_push_of_neg`
    exact (Array.filter_push_of_neg (p := isNegB) (xs := nums.extract 0 i) (a := nums[i]) (stop := i + 1) hneg w)

  calc
    Array.filter isNegB (nums.extract 0 i) 0 (min i nums.size)
        = Array.filter isNegB (nums.extract 0 i) 0 i := by
            simp [hmin_i]
    _ = (nums.extract 0 i).filter isNegB := by
            simpa [hsize]
    _ = Array.filter isNegB (nums.extract 0 (i + 1)) 0 (i + 1) := by
            simpa using (Eq.symm hfilter)
    _ = Array.filter isNegB (nums.extract 0 (i + 1)) 0 (min (i + 1) nums.size) := by
            simp [hmin_succ]

theorem goal_2
    (nums : Array ℤ)
    (i : ℕ)
    (invariant_collect_bounds : i ≤ nums.size)
    (if_pos : i < nums.size)
    (if_neg : nums[i]! ≤ OfNat.ofNat 0)
    : Array.filter isPosB (nums.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0) (min i nums.size) = Array.filter isPosB (nums.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) (OfNat.ofNat 0) (min (i + OfNat.ofNat 1) nums.size) := by
  have hi_le : i ≤ nums.size := Nat.le_of_lt if_pos
  have hi1_le : i + 1 ≤ nums.size := Nat.succ_le_of_lt if_pos
  -- simplify mins
  simp [Nat.min_eq_left hi_le, Nat.min_eq_left hi1_le]

  -- size of the prefix extract
  have hsize : (nums.extract 0 i).size = i := by
    simpa using (@Array.size_extract_of_le Int nums 0 i invariant_collect_bounds)

  -- `extract 0 (i+1)` is `extract 0 i` with the next element pushed
  have hx : nums.extract 0 (i + 1) = (nums.extract 0 i).push (nums[i]'if_pos) := by
    simpa using (@Array.extract_succ_right Int nums 0 i (Nat.succ_pos i) if_pos)

  -- the pushed element is not positive
  have hnotgt : ¬ (nums[i]'if_pos > (0 : Int)) := by
    have hle : nums[i]'if_pos ≤ (0 : Int) := by
      simpa [getElem!_pos (c := nums) (i := i) if_pos] using if_neg
    exact not_lt_of_ge hle

  have hpfalse : isPosB (nums[i]'if_pos) = false := by
    dsimp [isPosB]
    exact Bool.decide_false hnotgt

  have hneg : ¬ isPosB (nums[i]'if_pos) := by
    intro h
    have h' : isPosB (nums[i]'if_pos) = true := by
      simpa using h
    -- rewrite by `hpfalse` to get `false = true`
    rw [hpfalse] at h'
    cases h'

  -- filtering after pushing a non-positive element does not change the positive-filtered prefix
  have hpush :
      Array.filter isPosB ((nums.extract 0 i).push (nums[i]'if_pos)) 0 (i + 1) =
        Array.filter isPosB (nums.extract 0 i) 0 i := by
    have h :=
      (Array.filter_push_of_neg (p := isPosB) (xs := nums.extract 0 i) (a := nums[i]'if_pos)
        (stop := i + 1) hneg (by simpa [hsize]))
    simpa [hsize] using h

  -- finish
  rw [hx]
  exact hpush.symm

theorem goal_3
    (nums : Array ℤ)
    (require_1 : nums.size % OfNat.ofNat 2 = OfNat.ofNat 0 ∧ (∀ i < nums.size, ¬nums[i]! = OfNat.ofNat 0) ∧ Array.countP isPosB nums = nums.size / OfNat.ofNat 2 ∧ Array.countP isNegB nums = nums.size / OfNat.ofNat 2)
    (i : ℕ)
    (invariant_collect_bounds : i ≤ nums.size)
    (if_pos : i < nums.size)
    (if_neg : nums[i]! ≤ OfNat.ofNat 0)
    : (Array.filter isNegB (nums.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0) (min i nums.size)).push nums[i]! =
        Array.filter isNegB (nums.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) (OfNat.ofNat 0)
          (min (i + OfNat.ofNat 1) nums.size) := by
  rcases require_1 with ⟨_, hnonzero, _, _⟩

  have hne0 : nums[i]! ≠ (0 : ℤ) := by
    have h := hnonzero i if_pos
    simpa using h

  have hlt0 : nums[i]! < (0 : ℤ) := by
    exact lt_of_le_of_ne if_neg hne0

  have hpred : isNegB nums[i]! := by
    simp [isNegB, hlt0]

  have hmin_i : min i nums.size = i := by
    exact Nat.min_eq_left invariant_collect_bounds

  have hle_succ : i + 1 ≤ nums.size := by
    exact Nat.succ_le_of_lt if_pos

  have hmin_succ : min (i + 1) nums.size = i + 1 := by
    exact Nat.min_eq_left hle_succ

  -- Under the bound, `getElem!` is the same as the bounded `getElem`.
  have hget : nums[i]! = nums[i] := by
    -- `nums[i]` uses the implicit proof `if_pos`.
    simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getD_getElem?, if_pos]

  have hsize_prefix : (nums.extract 0 i).size = i := by
    simp [Array.size_extract, hmin_i]

  have hstop : i + 1 = (nums.extract 0 i).size + 1 := by
    simpa [hsize_prefix]

  -- `extract 0 (i+1)` is the previous extract with the next element pushed.
  have hextract : nums.extract 0 (i + 1) = (nums.extract 0 i).push nums[i]! := by
    have hex : (nums.extract 0 i).push nums[i] = nums.extract 0 (i + 1) := by
      -- Use the library lemma and simplify `min 0 i`.
      simpa [Nat.zero_min] using (@Array.push_extract_getElem ℤ nums 0 i if_pos)
    have hget' : nums[i] = nums[i]! := by
      simpa using hget.symm
    calc
      nums.extract 0 (i + 1) = (nums.extract 0 i).push nums[i] := by
        simpa using hex.symm
      _ = (nums.extract 0 i).push nums[i]! := by
        simpa [hget']

  -- Rewrite the goal using the computed mins and the extract-as-push fact.
  -- Then it is exactly `filter_push_of_pos`.
  calc
    (Array.filter isNegB (nums.extract 0 i) 0 (min i nums.size)).push nums[i]!
        = (Array.filter isNegB (nums.extract 0 i) 0 i).push nums[i]! := by
            simpa [hmin_i]
    _ = ((nums.extract 0 i).filter isNegB).push nums[i]! := by
            -- stop = size for the extracted prefix
            simpa [hsize_prefix]
    _ = Array.filter isNegB ((nums.extract 0 i).push nums[i]!) 0 (i + 1) := by
            -- apply `filter_push_of_pos` and flip the equality
            symm
            simpa [hstop] using
              (Array.filter_push_of_pos (p := isNegB) (a := nums[i]!) (xs := nums.extract 0 i) hpred hstop)
    _ = Array.filter isNegB (nums.extract 0 (i + 1)) 0 (min (i + 1) nums.size) := by
            simpa [hextract, hmin_succ]

theorem goal_4
    (nums : Array ℤ)
    (i_1 : ℕ)
    (invariant_collect_bounds : i_1 ≤ nums.size)
    (done_1 : nums.size ≤ i_1)
    : Array.filter isPosB (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) (min i_1 nums.size) = Array.filter isPosB nums := by
    have hi : i_1 = nums.size := Nat.le_antisymm invariant_collect_bounds done_1
    subst hi
    simp [Array.extract_size]

theorem goal_5
    (nums : Array ℤ)
    (i_1 : ℕ)
    (invariant_collect_bounds : i_1 ≤ nums.size)
    (done_1 : nums.size ≤ i_1)
    : Array.filter isNegB (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) (min i_1 nums.size) = Array.filter isNegB nums := by
    have hi : i_1 = nums.size := Nat.le_antisymm invariant_collect_bounds done_1
    subst hi
    simp [Array.extract_size]

theorem goal_6
    (nums : Array ℤ)
    (require_1 : nums.size % OfNat.ofNat 2 = OfNat.ofNat 0 ∧ (∀ i < nums.size, ¬nums[i]! = OfNat.ofNat 0) ∧ Array.countP isPosB nums = nums.size / OfNat.ofNat 2 ∧ Array.countP isNegB nums = nums.size / OfNat.ofNat 2)
    (i_1 : ℕ)
    (invariant_collect_bounds : i_1 ≤ nums.size)
    (done_1 : nums.size ≤ i_1)
    : (Array.filter isPosB (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) (min i_1 nums.size)).size = nums.size / OfNat.ofNat 2 := by
    rcases require_1 with ⟨_hEven, _hNonZero, hPos, _hNeg⟩

    have hFilterSize : (Array.filter isPosB nums).size = nums.size / OfNat.ofNat 2 := by
      calc
        (Array.filter isPosB nums).size = Array.countP isPosB nums := by
          simpa using (Array.countP_eq_size_filter (p := isPosB) (xs := nums)).symm
        _ = nums.size / OfNat.ofNat 2 := hPos

    -- replace the filtered extracted prefix by filtering the whole array
    simpa [goal_4 (nums := nums) (i_1 := i_1)
            (invariant_collect_bounds := invariant_collect_bounds)
            (done_1 := done_1)] using hFilterSize

theorem goal_7
    (nums : Array ℤ)
    (require_1 : nums.size % OfNat.ofNat 2 = OfNat.ofNat 0 ∧ (∀ i < nums.size, ¬nums[i]! = OfNat.ofNat 0) ∧ Array.countP isPosB nums = nums.size / OfNat.ofNat 2 ∧ Array.countP isNegB nums = nums.size / OfNat.ofNat 2)
    (i_1 : ℕ)
    (invariant_collect_bounds : i_1 ≤ nums.size)
    (done_1 : nums.size ≤ i_1)
    : (Array.filter isNegB (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) (min i_1 nums.size)).size = nums.size / OfNat.ofNat 2 := by
    have hcountNeg : Array.countP isNegB nums = nums.size / OfNat.ofNat 2 := require_1.2.2.2
    have hfilter :
        Array.filter isNegB (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) (min i_1 nums.size)
          = Array.filter isNegB nums :=
      goal_5 nums i_1 invariant_collect_bounds done_1
    have hsize :
        (Array.filter isNegB (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) (min i_1 nums.size)).size
          = (Array.filter isNegB nums).size :=
      congrArg Array.size hfilter
    calc
      (Array.filter isNegB (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) (min i_1 nums.size)).size
          = (Array.filter isNegB nums).size := hsize
      _ = Array.countP isNegB nums := by
          simpa using (Array.countP_eq_size_filter (p := isNegB) (xs := nums)).symm
      _ = nums.size / OfNat.ofNat 2 := hcountNeg

namespace List

/-- Elements at even indices: 0,2,4,... -/
def evens : List α → List α
  | [] => []
  | a :: [] => [a]
  | a :: _b :: t => a :: evens t

@[simp] theorem evens_nil (α) : (evens ([] : List α)) = [] := rfl

end List

open List

def AltList (l : List ℤ) : Prop :=
  ∀ i (hi : i < l.length),
    ((i % 2 = 0) → l[i]'hi > 0) ∧ ((i % 2 = 1) → l[i]'hi < 0)

theorem List.filter_isPosB_eq_evens_of_AltList (l : List ℤ) (h : AltList l) :
    l.filter isPosB = l.evens := by
  have H : ∀ n, ∀ l : List ℤ, l.length = n → AltList l → l.filter isPosB = l.evens := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih l hlen halt
    cases l with
    | nil =>
        simp at hlen
        subst hlen
        simp
    | cons a tl =>
        cases tl with
        | nil =>
            have ha_pos : a > 0 := by
              have h0 := halt 0 (by simp)
              simpa using (h0.1 (by simp))
            simp [List.filter, List.evens, isPosB, ha_pos]
        | cons b t =>
            have ha_pos : a > 0 := by
              have h0 := halt 0 (by simp)
              simpa using (h0.1 (by simp))
            have hb_neg : b < 0 := by
              have h1 := halt 1 (by simp)
              simpa using (h1.2 (by simp))
            have hb0 : ¬ (0 : ℤ) < b := by
              exact not_lt_of_ge (le_of_lt hb_neg)
            have halt_t : AltList t := by
              intro i hi
              have hi' : i + 2 < (a :: b :: t).length := by
                simpa using (Nat.add_lt_add_right hi 2)
              have h' := halt (i + 2) hi'
              have hmod : (i + 2) % 2 = i % 2 := by simp [Nat.add_mod]
              constructor
              · intro hEven
                have : (i + 2) % 2 = 0 := by simpa [hmod] using hEven
                simpa using (h'.1 this)
              · intro hOdd
                have : (i + 2) % 2 = 1 := by simpa [hmod] using hOdd
                simpa using (h'.2 this)
            have ht : t.filter isPosB = t.evens := by
              have ht_lt : t.length < n := by
                have : n = t.length + 2 := by
                  -- unfold length of a::b::t
                  simpa using hlen.symm
                omega
              exact ih t.length ht_lt t rfl halt_t
            simp [List.filter, List.evens, isPosB, ha_pos, hb0, hb_neg, ht]
  exact H l.length l rfl h


theorem goal_8_0_0
    (nums : Array ℤ)
    (require_1 : nums.size % OfNat.ofNat 2 = OfNat.ofNat 0 ∧
  (∀ i < nums.size, ¬nums[i]! = OfNat.ofNat 0) ∧
    Array.countP isPosB nums = nums.size / OfNat.ofNat 2 ∧ Array.countP isNegB nums = nums.size / OfNat.ofNat 2)
    (i_1 : ℕ)
    (i_4 : ℕ)
    (res_1 : Array ℤ)
    (invariant_collect_bounds : i_1 ≤ nums.size)
    (invariant_interleave_neg_size : (Array.filter isNegB nums).size = nums.size / OfNat.ofNat 2)
    (invariant_interleave_pos_size : (Array.filter isPosB nums).size = nums.size / OfNat.ofNat 2)
    (invariant_interleave_bounds : i_4 ≤ nums.size)
    (invariant_interleave_res_size : res_1.size = nums.size)
    (invariant_interleave_prefix : ∀ k < i_4,
  (k % OfNat.ofNat 2 = OfNat.ofNat 0 → res_1[k]! = (Array.filter isPosB nums)[k / OfNat.ofNat 2]!) ∧
    (k % OfNat.ofNat 2 = OfNat.ofNat 1 → res_1[k]! = (Array.filter isNegB nums)[k / OfNat.ofNat 2]!))
    (done_1 : nums.size ≤ i_1)
    (invariant_collect_neg : Array.filter isNegB nums = Array.filter isNegB (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) (min i_1 nums.size))
    (invariant_collect_pos : Array.filter isPosB nums = Array.filter isPosB (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) (min i_1 nums.size))
    (done_2 : nums.size ≤ i_4)
    (hi4 : i_4 = nums.size)
    (h_alt : alternatesStartingPos res_1)
    (h_start : res_1.size > 0 → res_1[0]! > 0)
    : Array.filter isPosB res_1 = Array.filter isPosB nums := by
    sorry

lemma evens_sanity : (([] : List Nat).evens) = [] := by
  simp

lemma List.get?_evens (l : List α) (n : Nat) : l.evens.get? n = l.get? (2*n) := by
  induction n generalizing l with
  | zero =>
      cases l with
      | nil => simp [List.evens]
      | cons a t =>
          cases t with
          | nil => simp [List.evens]
          | cons b t' => simp [List.evens]
  | succ n ih =>
      cases l with
      | nil =>
          simp [List.evens]
      | cons a t =>
          cases t with
          | nil =>
              -- l = [a]
              simp [List.evens, Nat.mul_succ, Nat.succ_mul]
          | cons b t' =>
              -- l = a :: b :: t'
              simpa [List.evens, Nat.mul_succ, Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using (ih (l := t'))


theorem goal_8_0_1
    (nums : Array ℤ)
    (require_1 : nums.size % OfNat.ofNat 2 = OfNat.ofNat 0 ∧
  (∀ i < nums.size, ¬nums[i]! = OfNat.ofNat 0) ∧
    Array.countP isPosB nums = nums.size / OfNat.ofNat 2 ∧ Array.countP isNegB nums = nums.size / OfNat.ofNat 2)
    (i_1 : ℕ)
    (i_4 : ℕ)
    (res_1 : Array ℤ)
    (invariant_collect_bounds : i_1 ≤ nums.size)
    (invariant_interleave_neg_size : (Array.filter isNegB nums).size = nums.size / OfNat.ofNat 2)
    (invariant_interleave_pos_size : (Array.filter isPosB nums).size = nums.size / OfNat.ofNat 2)
    (invariant_interleave_bounds : i_4 ≤ nums.size)
    (invariant_interleave_res_size : res_1.size = nums.size)
    (invariant_interleave_prefix : ∀ k < i_4,
  (k % OfNat.ofNat 2 = OfNat.ofNat 0 → res_1[k]! = (Array.filter isPosB nums)[k / OfNat.ofNat 2]!) ∧
    (k % OfNat.ofNat 2 = OfNat.ofNat 1 → res_1[k]! = (Array.filter isNegB nums)[k / OfNat.ofNat 2]!))
    (done_1 : nums.size ≤ i_1)
    (invariant_collect_neg : Array.filter isNegB nums = Array.filter isNegB (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) (min i_1 nums.size))
    (invariant_collect_pos : Array.filter isPosB nums = Array.filter isPosB (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) (min i_1 nums.size))
    (done_2 : nums.size ≤ i_4)
    (hi4 : i_4 = nums.size)
    (h_alt : alternatesStartingPos res_1)
    (h_start : res_1.size > 0 → res_1[0]! > 0)
    (hpos : Array.filter isPosB res_1 = Array.filter isPosB nums)
    : Array.filter isNegB res_1 = Array.filter isNegB nums := by
    sorry

theorem goal_8_0
    (nums : Array ℤ)
    (require_1 : nums.size % OfNat.ofNat 2 = OfNat.ofNat 0 ∧
  (∀ i < nums.size, ¬nums[i]! = OfNat.ofNat 0) ∧
    Array.countP isPosB nums = nums.size / OfNat.ofNat 2 ∧ Array.countP isNegB nums = nums.size / OfNat.ofNat 2)
    (i_1 : ℕ)
    (i_4 : ℕ)
    (res_1 : Array ℤ)
    (invariant_collect_bounds : i_1 ≤ nums.size)
    (invariant_interleave_neg_size : (Array.filter isNegB nums).size = nums.size / OfNat.ofNat 2)
    (invariant_interleave_pos_size : (Array.filter isPosB nums).size = nums.size / OfNat.ofNat 2)
    (invariant_interleave_bounds : i_4 ≤ nums.size)
    (invariant_interleave_res_size : res_1.size = nums.size)
    (invariant_interleave_prefix : ∀ k < i_4,
  (k % OfNat.ofNat 2 = OfNat.ofNat 0 → res_1[k]! = (Array.filter isPosB nums)[k / OfNat.ofNat 2]!) ∧
    (k % OfNat.ofNat 2 = OfNat.ofNat 1 → res_1[k]! = (Array.filter isNegB nums)[k / OfNat.ofNat 2]!))
    (done_1 : nums.size ≤ i_1)
    (invariant_collect_neg : Array.filter isNegB nums = Array.filter isNegB (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) (min i_1 nums.size))
    (invariant_collect_pos : Array.filter isPosB nums = Array.filter isPosB (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) (min i_1 nums.size))
    (done_2 : nums.size ≤ i_4)
    (hi4 : i_4 = nums.size)
    (h_alt : alternatesStartingPos res_1)
    (h_start : res_1.size > 0 → res_1[0]! > 0)
    : stableBySign nums res_1 := by
    unfold stableBySign
    have hpos : res_1.filter isPosB = nums.filter isPosB := by
      expose_names; exact (goal_8_0_0 nums require_1 i_1 i_4 res_1 invariant_collect_bounds invariant_interleave_neg_size invariant_interleave_pos_size invariant_interleave_bounds invariant_interleave_res_size invariant_interleave_prefix done_1 invariant_collect_neg invariant_collect_pos done_2 hi4 h_alt h_start)
    have hneg : res_1.filter isNegB = nums.filter isNegB := by
      expose_names; exact (goal_8_0_1 nums require_1 i_1 i_4 res_1 invariant_collect_bounds invariant_interleave_neg_size invariant_interleave_pos_size invariant_interleave_bounds invariant_interleave_res_size invariant_interleave_prefix done_1 invariant_collect_neg invariant_collect_pos done_2 hi4 h_alt h_start hpos)
    exact And.intro hpos hneg

theorem goal_8_1
    (nums : Array ℤ)
    (require_1 : nums.size % OfNat.ofNat 2 = OfNat.ofNat 0 ∧
  (∀ i < nums.size, ¬nums[i]! = OfNat.ofNat 0) ∧
    Array.countP isPosB nums = nums.size / OfNat.ofNat 2 ∧ Array.countP isNegB nums = nums.size / OfNat.ofNat 2)
    (i_1 : ℕ)
    (i_4 : ℕ)
    (res_1 : Array ℤ)
    (invariant_collect_bounds : i_1 ≤ nums.size)
    (invariant_interleave_neg_size : (Array.filter isNegB nums).size = nums.size / OfNat.ofNat 2)
    (invariant_interleave_pos_size : (Array.filter isPosB nums).size = nums.size / OfNat.ofNat 2)
    (invariant_interleave_bounds : i_4 ≤ nums.size)
    (invariant_interleave_res_size : res_1.size = nums.size)
    (invariant_interleave_prefix : ∀ k < i_4,
  (k % OfNat.ofNat 2 = OfNat.ofNat 0 → res_1[k]! = (Array.filter isPosB nums)[k / OfNat.ofNat 2]!) ∧
    (k % OfNat.ofNat 2 = OfNat.ofNat 1 → res_1[k]! = (Array.filter isNegB nums)[k / OfNat.ofNat 2]!))
    (done_1 : nums.size ≤ i_1)
    (invariant_collect_neg : Array.filter isNegB nums = Array.filter isNegB (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) (min i_1 nums.size))
    (invariant_collect_pos : Array.filter isPosB nums = Array.filter isPosB (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) (min i_1 nums.size))
    (done_2 : nums.size ≤ i_4)
    (hi4 : i_4 = nums.size)
    (h_alt : alternatesStartingPos res_1)
    (h_start : res_1.size > 0 → res_1[0]! > 0)
    (h_stable : stableBySign nums res_1)
    : res_1.Perm nums := by
    sorry


theorem goal_8
    (nums : Array ℤ)
    (require_1 : nums.size % OfNat.ofNat 2 = OfNat.ofNat 0 ∧ (∀ i < nums.size, ¬nums[i]! = OfNat.ofNat 0) ∧ Array.countP isPosB nums = nums.size / OfNat.ofNat 2 ∧ Array.countP isNegB nums = nums.size / OfNat.ofNat 2)
    (i_1 : ℕ)
    (i_4 : ℕ)
    (res_1 : Array ℤ)
    (invariant_collect_bounds : i_1 ≤ nums.size)
    (invariant_interleave_neg_size : (Array.filter isNegB nums).size = nums.size / OfNat.ofNat 2)
    (invariant_interleave_pos_size : (Array.filter isPosB nums).size = nums.size / OfNat.ofNat 2)
    (invariant_interleave_bounds : i_4 ≤ nums.size)
    (invariant_interleave_res_size : res_1.size = nums.size)
    (invariant_interleave_prefix : ∀ k < i_4, (k % OfNat.ofNat 2 = OfNat.ofNat 0 → res_1[k]! = (Array.filter isPosB nums)[k / OfNat.ofNat 2]!) ∧ (k % OfNat.ofNat 2 = OfNat.ofNat 1 → res_1[k]! = (Array.filter isNegB nums)[k / OfNat.ofNat 2]!))
    (done_1 : nums.size ≤ i_1)
    (invariant_collect_neg : Array.filter isNegB nums = Array.filter isNegB (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) (min i_1 nums.size))
    (invariant_collect_pos : Array.filter isPosB nums = Array.filter isPosB (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) (min i_1 nums.size))
    (done_2 : nums.size ≤ i_4)
    : postcondition nums res_1 := by
  classical
  have hi4 : i_4 = nums.size := by
    exact le_antisymm invariant_interleave_bounds done_2

  have h_alt : alternatesStartingPos res_1 := by
    expose_names; intros; expose_names; try simp_all; try grind

  have h_start : (res_1.size > 0 → res_1[0]! > 0) := by
    expose_names; intros; expose_names; try simp_all; try grind

  have h_stable : stableBySign nums res_1 := by
    expose_names; exact (goal_8_0 nums require_1 i_1 i_4 res_1 invariant_collect_bounds invariant_interleave_neg_size invariant_interleave_pos_size invariant_interleave_bounds invariant_interleave_res_size invariant_interleave_prefix done_1 invariant_collect_neg invariant_collect_pos done_2 hi4 h_alt h_start)

  have h_perm : res_1.Perm nums := by
    expose_names; exact (goal_8_1 nums require_1 i_1 i_4 res_1 invariant_collect_bounds invariant_interleave_neg_size invariant_interleave_pos_size invariant_interleave_bounds invariant_interleave_res_size invariant_interleave_prefix done_1 invariant_collect_neg invariant_collect_pos done_2 hi4 h_alt h_start h_stable)

  refine And.intro invariant_interleave_res_size ?_
  refine And.intro h_perm ?_
  refine And.intro h_alt ?_
  refine And.intro h_start ?_
  exact h_stable


prove_correct RearrangeArrayElementsBySign by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at * <;> expose_names); try (conv => congr <;> simp) ; try rfl; try expose_names)
  exact (goal_0 nums i invariant_collect_bounds if_pos if_pos_1)
  exact (goal_1 nums i if_pos if_pos_1)
  exact (goal_2 nums i invariant_collect_bounds if_pos if_neg)
  exact (goal_3 nums require_1 i invariant_collect_bounds if_pos if_neg)
  exact (goal_4 nums i_1 invariant_collect_bounds done_1)
  exact (goal_5 nums i_1 invariant_collect_bounds done_1)
  exact (goal_6 nums require_1 i_1 invariant_collect_bounds done_1)
  exact (goal_7 nums require_1 i_1 invariant_collect_bounds done_1)
  exact (goal_8 nums require_1 i_1 i_4 res_1 invariant_collect_bounds invariant_interleave_neg_size invariant_interleave_pos_size invariant_interleave_bounds invariant_interleave_res_size invariant_interleave_prefix done_1 invariant_collect_neg invariant_collect_pos done_2)
end Proof
