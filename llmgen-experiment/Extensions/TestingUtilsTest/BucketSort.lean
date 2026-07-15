import Velvet.Std
import CaseStudies.TestingUtil
import Extensions.SpecDSL
import Extensions.Testing
import Extensions.VelvetPBT

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    BucketSort: Sort an array of non-negative integers using bucket sort
    **Important: complexity should be O(A.length + M)**
    Natural language breakdown:
    1. Given an array A of non-negative integers where all elements are in range [0, M-1]
    2. Return a new array B that is sorted in non-decreasing order
    3. B must contain exactly the same elements as A with the same multiplicities
    4. The result must be a permutation of the input (same multiset)
    5. The result must be sorted in non-decreasing order
    6. Edge cases:
       - Empty array: return empty array
       - Single element: return the same array
       - All same elements: return array of same elements
       - Already sorted: return same sequence
-/

section Specs
-- Helper to check if array is sorted in non-decreasing order
def isSortedNonDecreasing (arr : Array Nat) : Prop :=
  ∀ i j : Nat, i < j → j < arr.size → arr[i]! ≤ arr[j]!

-- Helper to check if all elements are within bound [0, M-1]
def allInRange (arr : Array Nat) (M : Nat) : Prop :=
  ∀ i : Nat, i < arr.size → arr[i]! < M

-- Helper to count occurrences of an element in an array
def countOccurrences (arr : Array Nat) (x : Nat) : Nat :=
  (arr.toList.filter (· == x)).length

-- Helper to check if two arrays have same elements with same multiplicities
def sameMultiset (arr1 arr2 : Array Nat) : Prop :=
  ∀ x : Nat, countOccurrences arr1 x = countOccurrences arr2 x

-- Precondition: M > 0 and all elements in A are in range [0, M-1]
def precondition (A : Array Nat) (M : Nat) : Prop :=
  M > 0 ∧ allInRange A M

-- Postcondition: result has same elements as input and is sorted
def postcondition (A : Array Nat) (M : Nat) (result : Array Nat) : Prop :=
  sameMultiset A result ∧
  isSortedNonDecreasing result ∧
  result.size = A.size
end Specs

section Impl
method BucketSort (A : Array Nat) (M : Nat)
  return (result : Array Nat)
  require precondition A M
  ensures postcondition A M result
  do
  -- Handle empty array case
  if A.size = 0 then
    return #[]
  else
    -- Step 1: Create count array of size M, initialized to 0
    let mut counts := Array.replicate M 0

    -- Step 2: Count occurrences of each element in A
    let mut i := 0
    while i < A.size
      -- i is bounded by A.size
      invariant "i_lower" 0 ≤ i
      invariant "i_upper" i ≤ A.size
      -- counts array maintains its size
      invariant "counts_size" counts.size = M
      -- counts[x] equals the number of occurrences of x in A[0..i]
      invariant "counts_correct" ∀ x : Nat, x < M → counts[x]! = countOccurrences (A.extract 0 i) x
      done_with i = A.size
    do
      let elem := A[i]!
      counts := counts.set! elem (counts[elem]! + 1)
      i := i + 1

    -- Step 3: Build result array from counts
    let mut result : Array Nat := #[]
    let mut j := 0
    while j < M
      -- j is bounded by M
      invariant "j_lower" 0 ≤ j
      invariant "j_upper" j ≤ M
      -- counts array size preserved
      invariant "counts_size_outer" counts.size = M
      -- counts still reflects the full array A
      invariant "counts_full" ∀ x : Nat, x < M → counts[x]! = countOccurrences A x
      -- result contains elements < j, each with correct count
      invariant "result_multiset" ∀ x : Nat, x < j → countOccurrences result x = countOccurrences A x
      -- result contains no elements >= j
      invariant "result_no_larger" ∀ x : Nat, x ≥ j → countOccurrences result x = 0
      -- result is sorted (all elements so far are < j, so sorted)
      invariant "result_sorted" isSortedNonDecreasing result
      -- Size tracking: result.size equals count of elements in A that are < j
      invariant "result_size" result.size = (A.toList.filter (· < j)).length
      done_with j = M
    do
      let mut k := 0
      while k < counts[j]!
        -- k is bounded
        invariant "k_lower" 0 ≤ k
        invariant "k_upper" k ≤ counts[j]!
        -- j still in bounds
        invariant "j_bound_inner" j < M
        -- counts unchanged
        invariant "counts_size_inner" counts.size = M
        invariant "counts_inner" ∀ x : Nat, x < M → counts[x]! = countOccurrences A x
        -- result has correct counts for elements < j
        invariant "result_less_j" ∀ x : Nat, x < j → countOccurrences result x = countOccurrences A x
        -- result has k copies of j so far
        invariant "result_at_j" countOccurrences result j = k
        -- result has no elements > j
        invariant "result_greater_j" ∀ x : Nat, x > j → countOccurrences result x = 0
        -- result is still sorted
        invariant "result_sorted_inner" isSortedNonDecreasing result
        -- Inner size tracking: result.size = elements < j plus k copies of j
        invariant "result_size_inner" result.size = (A.toList.filter (· < j)).length + k
        done_with k = counts[j]!
      do
        result := result.push j
        k := k + 1
      j := j + 1

    return result
end Impl

velvet_plausible_test BucketSort (config := { maxMs := some 5000 })
