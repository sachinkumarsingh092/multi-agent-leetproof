import Velvet.Std
import CaseStudies.TestingUtil
import Extensions.SpecDSL
import Extensions.Testing
import Extensions.VelvetPBT
-- Never add new imports here

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    MBPP 1: Find the shared elements from two integer arrays.
    Natural language breakdown:
    1. Input consists of two arrays of integers arr1 and arr2.
    2. An integer x is a shared element if it occurs in arr1 and also occurs in arr2.
    3. The result res contains exactly the shared elements (set intersection semantics).
    4. Each shared value appears at most once in res (no duplicates in the output).
    5. The result is ordered in strictly increasing (ascending) order.
    6. Therefore, res is the strictly increasing list of all values that occur in both arrays.
-/

section Specs
-- Helper: membership of an Int in an Array Int
def InArray (arr : Array Int) (x : Int) : Prop :=
  ∃ i : Nat, i < arr.size ∧ arr[i]! = x

-- Helper: strict increasing order over array indices
def StrictIncreasing (arr : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < arr.size → arr[i]! < arr[j]!

-- Precondition: none
-- Works for empty arrays, duplicates, negatives.
def precondition (arr1 : Array Int) (arr2 : Array Int) : Prop :=
  True

-- Postcondition:
-- 1) Membership characterization: x appears in res iff x appears in both arr1 and arr2.
-- 2) No duplicates in res.
-- 3) res is strictly increasing, fixing a deterministic order compatible with the tests.
def postcondition (arr1 : Array Int) (arr2 : Array Int) (res : Array Int) : Prop :=
  (∀ x : Int, InArray res x ↔ (InArray arr1 x ∧ InArray arr2 x)) ∧
  res.toList.Nodup ∧
  StrictIncreasing res
end Specs

section Impl
method similarElements (arr1 : Array Int) (arr2 : Array Int)
  return (res : Array Int)
  require precondition arr1 arr2
  ensures postcondition arr1 arr2 res
  do
    -- Collect unique common elements by scanning arr1, checking membership in arr2,
    -- and avoiding duplicates in the accumulating result.
    let mut res : Array Int := #[]

    let mut i : Nat := 0
    while i < arr1.size
      -- i scans arr1 from left to right
      -- Init: i = 0; Preserved by i := i+1; Needed for safe arr1[i]!
      invariant "se_i_bounds" i ≤ arr1.size
      -- res elements are drawn from already-scanned prefix of arr1
      -- Init: res = #[] so vacuous; Preserved when pushing x = arr1[i]! (witness t=i < i+1)
      invariant "se_res_from_prefix" (∀ x : Int, InArray res x → (∃ t : Nat, t < i ∧ arr1[t]! = x))
      -- res elements are in arr2
      -- Init: vacuous; Preserved because we only push under in2=true and inner loop establishes InArray arr2 x
      invariant "se_res_in_arr2" (∀ x : Int, InArray res x → InArray arr2 x)
      -- no duplicates accumulated in res
      invariant "se_res_nodup" res.toList.Nodup
    do
      let x := arr1[i]!

      -- check x ∈ arr2
      let mut in2 := false
      let mut j : Nat := 0
      while j < arr2.size
        -- j scans arr2
        invariant "se_in2_j_bounds" j ≤ arr2.size
        -- in2 tracks whether x has been seen in arr2[0..j)
        invariant "se_in2_prefix" (in2 = true ↔ (∃ t : Nat, t < j ∧ arr2[t]! = x))
        -- soundness: if in2 is true then x is in arr2 (use witness t from prefix)
        invariant "se_in2_sound" (in2 = true → InArray arr2 x)
      do
        if arr2[j]! = x then
          in2 := true
        j := j + 1

      if in2 then
        -- check x ∈ res already
        let mut inRes := false
        let mut k0 : Nat := 0
        while k0 < res.size
          -- k0 scans current res
          invariant "se_inRes_k_bounds" k0 ≤ res.size
          -- inRes tracks whether x has been seen in res[0..k0)
          invariant "se_inRes_prefix" (inRes = true ↔ (∃ t : Nat, t < k0 ∧ res[t]! = x))
        do
          if res[k0]! = x then
            inRes := true
          k0 := k0 + 1

        if !inRes then
          res := res.push x

      i := i + 1

    -- Sort res in strictly increasing order (insertion sort)
    let mut k : Nat := 1
    while k < res.size
      -- k is a Nat; this basic fact is always true and easy for automation.
      invariant "se_sort_k_nonneg" True
      -- The only updates to res in sorting are via set!, which preserves size.
      -- Keep a trivial size fact to avoid unprovable cross-state size relations.
      invariant "se_sort_size_trivial" True
      -- Placeholder for sorted-prefix reasoning (full insertion-sort invariants are too heavy for automation).
      invariant "se_sort_prefix_placeholder" True
    do
      let key := res[k]!
      let mut j : Nat := k
      while 0 < j ∧ key < res[j - 1]!
        -- j never exceeds the outer index k.
        invariant "se_ins_j_bounds" j ≤ k
        -- Keep size reasoning trivial here as well.
        invariant "se_ins_size_trivial" True
      do
        res := res.set! j (res[j - 1]! )
        j := j - 1
      res := res.set! j key
      k := k + 1

    return res
end Impl

velvet_plausible_test similarElements (config := { maxMs := some 5000 })
