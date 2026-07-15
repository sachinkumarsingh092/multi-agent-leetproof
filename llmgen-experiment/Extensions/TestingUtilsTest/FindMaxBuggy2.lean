import Velvet.Std
import CaseStudies.TestingUtil
import Extensions.SpecDSL
import Extensions.Testing
import Extensions.VelvetPBT
-- Never add new imports here

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    FindMax: Find the maximum element in a non-empty integer array.
    Natural language breakdown:
    1. Input is a non-empty array A of integers.
    2. The result res must equal some element A[k]! (witness).
    3. Every element A[k]! must be ≤ res (upper bound).
-/

section Specs

def precondition (a : Array Int) : Prop :=
  0 < a.size

def postcondition (a : Array Int) (res : Int) : Prop :=
  (∃ k : Nat, k < a.size ∧ a[k]! = res) ∧
  (∀ k : Nat, k < a.size → a[k]! ≤ res)

end Specs

-- ============================================================
-- Correct implementation — Expected: PASS
-- ============================================================

method findMax (a : Array Int)
  return (res : Int)
  require precondition a
  ensures postcondition a res
  do
    let mut m := a[0]!
    let mut i : Nat := 1
    while i < a.size
      -- i stays within the scanned prefix
      invariant "bounds" i ≤ a.size
      -- every element in the scanned prefix is ≤ the current maximum
      invariant "upper" ∀ k : Nat, k < i → a[k]! ≤ m
      -- the current maximum is witnessed by some element in the scanned prefix
      invariant "witness" ∃ k : Nat, k < i ∧ a[k]! = m
      do
        if a[i]! > m then
          m := a[i]!
        i := i + 1
    return m

velvet_plausible_test findMax

-- ============================================================
-- Bug 1: Comparison flipped — accumulates minimum instead of maximum.
-- The "upper" invariant breaks as soon as m drops below a previously seen element.
-- Expected: FAIL (invariant "upper" violated)
-- ============================================================

method findMaxFlipped (a : Array Int)
  return (res : Int)
  require precondition a
  ensures postcondition a res
  do
    let mut m := a[0]!
    let mut i : Nat := 1
    while i < a.size
      invariant "flipped_bounds" i ≤ a.size
      invariant "flipped_upper" ∀ k : Nat, k < i → a[k]! ≤ m
      invariant "flipped_witness" ∃ k : Nat, k < i ∧ a[k]! = m
      do
        if a[i]! < m then   -- BUG: should be >; this finds the minimum
          m := a[i]!
        i := i + 1
    return m

velvet_plausible_test findMaxFlipped

-- ============================================================
-- Bug 2: Strict upper-bound invariant — claims a[k]! < m (strict)
-- rather than a[k]! ≤ m (non-strict).
-- Immediately violated by any array with two equal elements, e.g. [3, 3].
-- Expected: FAIL (invariant "strict_upper" violated)
-- ============================================================

method findMaxStrictInv (a : Array Int)
  return (res : Int)
  require precondition a
  ensures postcondition a res
  do
    let mut m := a[0]!
    let mut i : Nat := 1
    while i < a.size
      invariant "strict_bounds" i ≤ a.size
      invariant "strict_upper" ∀ k : Nat, k < i → a[k]! < m  -- BUG: should be ≤
      invariant "strict_witness" ∃ k : Nat, k < i ∧ a[k]! = m
      do
        if a[i]! > m then
          m := a[i]!
        i := i + 1
    return m

velvet_plausible_test findMaxStrictInv

-- ============================================================
-- Bug 3: Loop starts at i = 2, skipping index 1.
-- If a[1]! is the unique maximum the result is wrong.
-- No invariant covers a[1]!, so postcondition fails instead.
-- Expected: FAIL (postcondition violated)
-- ============================================================

method findMaxSkipOne (a : Array Int)
  return (res : Int)
  require precondition a
  ensures postcondition a res
  do
    let mut m := a[0]!
    let mut i : Nat := 2   -- BUG: skips index 1 entirely
    while i < a.size
      invariant "skip_bounds" i ≤ a.size
      invariant "skip_upper" ∀ k : Nat, k < i → (k = 1 ∨ a[k]! ≤ m)
      invariant "skip_witness" ∃ k : Nat, k < i ∧ a[k]! = m
      do
        if a[i]! > m then
          m := a[i]!
        i := i + 1
    return m

velvet_plausible_test findMaxSkipOne

method findMaxWrongtInitValue (a : Array Int)
  return (res : Int)
  require precondition a
  ensures postcondition a res
  do
    let mut m := -13
    let mut i : Nat := 1   -- BUG: skips index 1 entirely
    while i < a.size
      invariant "wrong_init_bounds" i ≤ a.size
      invariant "wrong_init_upper" ∀ k : Nat, k < i → (k = 1 ∨ a[k]! ≤ m)
      invariant "wrong_init_witness" ∃ k : Nat, k < i ∧ a[k]! = m
      do
        if a[i]! > m then
          m := a[i]!
        i := i + 1
    return m

velvet_plausible_test findMaxWrongtInitValue
