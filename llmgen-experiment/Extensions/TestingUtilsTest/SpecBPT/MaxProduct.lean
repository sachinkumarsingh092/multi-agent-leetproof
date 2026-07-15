import Velvet.Std
import CaseStudies.TestingUtil
import Extensions.SpecDSL
import Extensions.Testing
import Extensions.VelvetPBT

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    maxProduct: find a pair with the highest product from a given array of integers.
    Natural language breakdown:
    1. Input is an array of integers.
    2. We must return two integers x and y that are elements of the input array.
    3. The array must have at least two elements so that a pair exists.
    4. The returned pair (x, y) must achieve a product x*y that is maximal among products of any two distinct indices.
    5. Indices used for the chosen pair must be within bounds and distinct.
    6. If multiple pairs achieve the same maximal product, any such pair is acceptable.
    7. Negative values and zero are allowed; two negatives may yield the maximal (positive) product.
-/

section Specs
-- Helper: an element occurs in an array
def InArray (arr : Array Int) (v : Int) : Prop :=
  ∃ i : Nat, i < arr.size ∧ arr[i]! = v

-- Helper: x and y occur at two distinct indices in the array
def PairFromDistinctIndices (arr : Array Int) (x : Int) (y : Int) : Prop :=
  ∃ i : Nat, ∃ j : Nat,
    i < arr.size ∧ j < arr.size ∧ i ≠ j ∧ arr[i]! = x ∧ arr[j]! = y

-- Precondition: at least 2 elements
def precondition (arr : Array Int) : Prop :=
  2 ≤ arr.size

-- Postcondition: x,y are from distinct indices and their product is maximal
def postcondition (arr : Array Int) (result : Int × Int) : Prop :=
  let x := result.1
  let y := result.2
  PairFromDistinctIndices arr x y ∧
  (∀ i : Nat, ∀ j : Nat,
      i < arr.size → j < arr.size → i ≠ j →
      arr[i]! * arr[j]! ≤ x * y)
end Specs

section Impl
method maxProduct (arr : Array Int)
  return (result : Int × Int)
  require precondition arr
  ensures postcondition arr result
  do
    -- Brute-force all distinct index pairs, tracking the best product.
    -- Tie-breaker to match provided tests:
    -- 1) prefer larger product
    -- 2) if tie, prefer larger first component
    -- 3) if tie, prefer larger second component

    let mut bestX : Int := arr[0]!
    let mut bestY : Int := arr[1]!
    let mut bestProd : Int := bestX * bestY

    let mut i : Nat := 0
    while i < arr.size
      invariant true = true
    do
      let mut j : Nat := i + 1
      while j < arr.size
        invariant true = true
      do
        let x : Int := arr[i]!
        let y : Int := arr[j]!
        let prod : Int := x * y

        let mut take : Bool := false
        if prod > bestProd then
          take := true
        else
          if prod = bestProd then
            -- Compare the pair as-ordered (no sorting), lexicographically, preferring larger.
            if x > bestX then
              take := true
            else
              if x = bestX then
                if y > bestY then
                  take := true

        if take then
          bestX := x
          bestY := y
          bestProd := prod

        j := j + 1
      i := i + 1

    return (bestX, bestY)
end Impl

section TestCases
-- Test case 1: example with positives and zero
def test1_arr : Array Int := #[1, 2, 3, 4, 7, 0, 8, 4]
def test1_Expected : Int × Int := (7, 8)

-- Test case 2: example where two negatives give max product
def test2_arr : Array Int := #[0, -1, -2, -4, 5, 0, -6]
def test2_Expected : Int × Int := (-4, -6)

-- Test case 3: small increasing array
def test3_arr : Array Int := #[1, 2, 3]
def test3_Expected : Int × Int := (2, 3)

-- Test case 4: exactly two elements
def test4_arr : Array Int := #[9, -10]
def test4_Expected : Int × Int := (9, -10)

-- Test case 5: all zeros (many optimal pairs)
def test5_arr : Array Int := #[0, 0, 0]
def test5_Expected : Int × Int := (0, 0)

-- Test case 6: all negative numbers (max product from two most negative)
def test6_arr : Array Int := #[-1, -2, -3, -4]
def test6_Expected : Int × Int := (-4, -3)

-- Test case 7: mix with duplicates, max from two largest positives
def test7_arr : Array Int := #[5, 5, 1, 2]
def test7_Expected : Int × Int := (5, 5)

-- Test case 8: includes Int extremes-ish within small range; max from positives
def test8_arr : Array Int := #[-100, 50, 2, -60]
def test8_Expected : Int × Int := (50, 2)

-- Recommend to validate: 1, 2, 6
end TestCases

set_option maxHeartbeats 1000000

def uniqueness_test (result : Int × Int) :
  result ≠ test6_Expected →
  ¬ postcondition test6_arr result := by
  -- unfold postcondition test6_arr test6_Expected PairFromDistinctIndices
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  plausible'_mut (seeds := #[test6_Expected]) (config := { numInst := 500000})
