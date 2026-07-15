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
    IntervalListIntersections: Intersect two sorted, pairwise-disjoint lists of closed integer intervals.
    Natural language breakdown:
    1. Each interval is a pair (start, end) representing the closed set of integers {x | start ≤ x ∧ x ≤ end}.
    2. Each input list is sorted by start ascending.
    3. Intervals in the same list are pairwise disjoint (non-overlapping); because they are closed, disjointness means the end of one is strictly less than the start of the next.
    4. The output is the list of all non-empty intersections between an interval from the first list and an interval from the second list.
    5. Each intersection of two closed intervals is either empty or a closed interval [max starts, min ends].
    6. The output list should be sorted and pairwise disjoint.
    7. Semantically, the union of the output intervals equals the set intersection of the unions of the input interval sets.
    Your algorithm should run in **O(m+n)** time and **O(1)** extra space, where m and n are the sizes of the two input lists.
-/

-- An interval is represented as a pair (start, end).
abbrev Interval := Int × Int

-- Convert an interval to the set of integers it denotes.
def intervalSet (iv : Interval) : Set Int :=
  Set.Icc iv.1 iv.2

-- The interval is well-formed.
def isValidInterval (iv : Interval) : Prop :=
  iv.1 ≤ iv.2

-- Array is sorted by starts (nondecreasing).
def sortedByStart (a : Array Interval) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < a.size → a[i]!.1 ≤ a[j]!.1

-- Array is pairwise disjoint in the strong closed-interval sense.
-- This implies that whenever i < j, the i-th interval ends strictly before the j-th interval begins.
def pairwiseDisjointClosed (a : Array Interval) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < a.size → a[i]!.2 < a[j]!.1

-- The union of all interval sets represented by an array.
def unionIntervalSets (a : Array Interval) : Set Int :=
  {x : Int | ∃ (i : Nat), i < a.size ∧ x ∈ intervalSet a[i]!}

-- Precondition: both lists contain only valid intervals and are sorted/disjoint.
def precondition (firstList : Array Interval) (secondList : Array Interval) : Prop :=
  (∀ (i : Nat), i < firstList.size → isValidInterval firstList[i]!) ∧
  (∀ (i : Nat), i < secondList.size → isValidInterval secondList[i]!) ∧
  sortedByStart firstList ∧
  sortedByStart secondList ∧
  pairwiseDisjointClosed firstList ∧
  pairwiseDisjointClosed secondList

-- Postcondition: output is a valid sorted/disjoint interval list whose union equals the set intersection
-- of the unions of input lists.
def postcondition (firstList : Array Interval) (secondList : Array Interval)
  (result : Array Interval) : Prop :=
  (∀ (k : Nat), k < result.size → isValidInterval result[k]!) ∧
  sortedByStart result ∧
  pairwiseDisjointClosed result ∧
  unionIntervalSets result = (unionIntervalSets firstList ∩ unionIntervalSets secondList)
end Specs

section Impl
def implementation (firstList : Array Interval) (secondList : Array Interval) : Array Interval :=
  let rec go (i j : Nat) (acc : Array Interval) : Array Interval :=
    if i < firstList.size then
      if j < secondList.size then
        let a := firstList[i]!
        let b := secondList[j]!
        let s : Int := max a.1 b.1
        let e : Int := min a.2 b.2
        let acc := if s ≤ e then acc.push (s, e) else acc
        if a.2 < b.2 then
          go (i + 1) j acc
        else if b.2 < a.2 then
          go i (j + 1) acc
        else
          go (i + 1) (j + 1) acc
      else
        acc
    else
      acc
  go 0 0 #[]
end Impl

section TestCases
-- Test case 1: Example 1 from the prompt
-- firstList = [[0,2],[5,10],[13,23],[24,25]]
-- secondList = [[1,5],[8,12],[15,24],[25,26]]
-- expected = [[1,2],[5,5],[8,10],[15,23],[24,24],[25,25]]
def test1_firstList : Array Interval := #[(0,2),(5,10),(13,23),(24,25)]
def test1_secondList : Array Interval := #[(1,5),(8,12),(15,24),(25,26)]
def test1_Expected : Array Interval := #[(1,2),(5,5),(8,10),(15,23),(24,24),(25,25)]

-- Test case 2: Example 2 from the prompt (second list empty)
def test2_firstList : Array Interval := #[(1,3),(5,9)]
def test2_secondList : Array Interval := #[]
def test2_Expected : Array Interval := #[]

-- Test case 3: first list empty

def test3_firstList : Array Interval := #[]
def test3_secondList : Array Interval := #[(1,2)]
def test3_Expected : Array Interval := #[]

-- Test case 4: both lists empty

def test4_firstList : Array Interval := #[]
def test4_secondList : Array Interval := #[]
def test4_Expected : Array Interval := #[]

-- Test case 5: single interval overlaps producing a non-degenerate intersection

def test5_firstList : Array Interval := #[(1,5)]
def test5_secondList : Array Interval := #[(2,3)]
def test5_Expected : Array Interval := #[(2,3)]

-- Test case 6: single interval intersection is a point

def test6_firstList : Array Interval := #[(1,2)]
def test6_secondList : Array Interval := #[(2,4)]
def test6_Expected : Array Interval := #[(2,2)]

-- Test case 7: no overlaps at all

def test7_firstList : Array Interval := #[(1,2)]
def test7_secondList : Array Interval := #[(3,4)]
def test7_Expected : Array Interval := #[]

-- Test case 8: negative numbers and multiple intersections

def test8_firstList : Array Interval := #[(-5,-3),(-1,2),(4,4)]
def test8_secondList : Array Interval := #[(-4,-2),(0,0),(3,5)]
def test8_Expected : Array Interval := #[(-4,-3),(0,0),(4,4)]

-- Test case 9: intersections where one interval from second overlaps two from first (due to disjointness, this can happen)

def test9_firstList : Array Interval := #[(0,1),(3,5),(7,9)]
def test9_secondList : Array Interval := #[(1,7)]
def test9_Expected : Array Interval := #[(1,1),(3,5),(7,7)]
end TestCases

section Assertions
-- Test case 1
#assert_same_evaluation #[(implementation test1_firstList test1_secondList), test1_Expected]

-- Test case 2
#assert_same_evaluation #[(implementation test2_firstList test2_secondList), test2_Expected]

-- Test case 3
#assert_same_evaluation #[(implementation test3_firstList test3_secondList), test3_Expected]

-- Test case 4
#assert_same_evaluation #[(implementation test4_firstList test4_secondList), test4_Expected]

-- Test case 5
#assert_same_evaluation #[(implementation test5_firstList test5_secondList), test5_Expected]

-- Test case 6
#assert_same_evaluation #[(implementation test6_firstList test6_secondList), test6_Expected]

-- Test case 7
#assert_same_evaluation #[(implementation test7_firstList test7_secondList), test7_Expected]

-- Test case 8
#assert_same_evaluation #[(implementation test8_firstList test8_secondList), test8_Expected]

-- Test case 9
#assert_same_evaluation #[(implementation test9_firstList test9_secondList), test9_Expected]
end Assertions

section Pbt
method implementationPbt (firstList : Array Interval) (secondList : Array Interval)
  return (result : Array Interval)
  require precondition firstList secondList
  ensures postcondition firstList secondList result
  do
  return (implementation firstList secondList)

velvet_plausible_test implementationPbt (config := { maxMs := some 20000 })
end Pbt

section Proof

theorem correctness_goal
    (firstList : Array Interval)
    (secondList : Array Interval)
    (h_precond : precondition firstList secondList)
    : postcondition firstList secondList (implementation firstList secondList) := by
    sorry
end Proof
