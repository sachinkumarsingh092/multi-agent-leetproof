import Velvet.Std
import CaseStudies.TestingUtil
import Extensions.SpecDSL
import Extensions.Testing
import Extensions.VelvetPBT
-- Never add new imports here

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
   Exercises three nesting patterns of `match` and `while`:
     A. match INSIDE while        →  zigzagSum       (alternating +/minus)
     B. while INSIDE match        →  branchSum       (mode-selected accumulation)
     C. match ⊃ while ⊃ match    →  absOrParitySum  (abs vs parity-weighted sum)

   Each family has a correct implementation (Expected: PASS) and one or more
   intentionally buggy variants (Expected: FAIL).
-/

-- ============================================================
-- Reference / spec helpers
-- ============================================================

/-- Zigzag sum: add a[0], subtract a[1], add a[2], subtract a[3], … -/
def zigzagRef (a : Array Int) : Int :=
  (Array.range a.size).foldl (fun acc i =>
    if i % 2 = 0 then acc + a[i]! else acc - a[i]!) 0

/-- Partial zigzag sum over a[0..n) -/
def zigzagPartial (a : Array Int) (n : Nat) : Int :=
  (Array.range n).foldl (fun acc i =>
    if i % 2 = 0 then acc + a[i]! else acc - a[i]!) 0

/-- Sum of strictly positive elements only -/
def posSum (a : Array Int) : Int :=
  (Array.range a.size).foldl (fun (acc : Int) i =>
    if a[i]! > (0 : Int) then acc + a[i]! else acc) 0

/-- Unconditional sum of all elements -/
def totalSum (a : Array Int) : Int :=
  (Array.range a.size).foldl (fun (acc : Int) i => acc + a[i]!) 0

/-- Sum of absolute values: Σ |a[i]| -/
def absSum (a : Array Int) : Int :=
  (Array.range a.size).foldl (fun (acc : Int) i =>
    match compare a[i]! (0 : Int) with
    | .lt => acc - a[i]!
    | _   => acc + a[i]!) 0

/-- Parity-weighted sum: add even-valued elements, subtract odd-valued elements -/
def parityWeightedSum (a : Array Int) : Int :=
  (Array.range a.size).foldl (fun (acc : Int) i =>
    if a[i]! % (2 : Int) = 0 then acc + a[i]! else acc - a[i]!) 0

-- ============================================================
-- A. match INSIDE while
-- Problem: compute the zigzag sum of an integer array.
--   res = a[0] - a[1] + a[2] - a[3] + …
-- A match inside the loop body selects + or − based on the
-- parity of the current index.
-- ============================================================

@[loomAbstractionSimp]
def preconditionZZ (_ : Array Int) : Prop := True

@[loomAbstractionSimp]
def postconditionZZ (a : Array Int) (res : Int) : Prop :=
  res = zigzagRef a

-- Correct implementation — Expected: PASS
method zigzagSum (a : Array Int)
  return (res : Int)
  require preconditionZZ a
  ensures postconditionZZ a res
  do
    let mut s : Int := 0
    let mut i : Nat := 0
    while i < a.size
      invariant "zzs_bounds"  i ≤ a.size
      invariant "zzs_partial" s = zigzagPartial a i
    do
      match i % 2 with
      | 0 => s := s + a[i]!
      | _ => s := s - a[i]!
      i := i + 1
    return s

velvet_plausible_test zigzagSum

-- Bug A-1: match arms swapped — subtracts even-indexed, adds odd-indexed.
-- Expected: FAIL (postcondition violated for any non-zero array element)
method zigzagSumArmsSwapped (a : Array Int)
  return (res : Int)
  require preconditionZZ a
  ensures postconditionZZ a res
  do
    let mut s : Int := 0
    let mut i : Nat := 0
    while i < a.size
      invariant "zzsa_bounds" i ≤ a.size
    do
      match i % 2 with
      | 0 => s := s - a[i]!   -- BUG: should be +
      | _ => s := s + a[i]!   -- BUG: should be -
      i := i + 1
    return s

velvet_plausible_test zigzagSumArmsSwapped

-- Bug A-2: wrong invariant — claims the partial sum is one step ahead.
-- Violated immediately: at i=0, s=0 but zigzagPartial a 1 = a[0], which
-- is non-zero for any array whose first element is non-zero.
-- Expected: FAIL (invariant "zzsi_partial" violated)
method zigzagSumWrongInv (a : Array Int)
  return (res : Int)
  require 0 < a.size
  ensures postconditionZZ a res
  do
    let mut s : Int := 0
    let mut i : Nat := 0
    while i < a.size
      invariant "zzsi_bounds"  i ≤ a.size
      invariant "zzsi_partial" s = zigzagPartial a (i + 1)  -- BUG: off-by-one
    do
      match i % 2 with
      | 0 => s := s + a[i]!
      | _ => s := s - a[i]!
      i := i + 1
    return s

velvet_plausible_test zigzagSumWrongInv

-- ============================================================
-- B. while INSIDE match
-- Problem: branchSum — `mode` selects which accumulation strategy to use:
--   true  → sum only strictly positive elements
--   false → sum all elements
-- Each match arm runs its own independent while loop.
-- ============================================================

@[loomAbstractionSimp]
def postconditionBS (a : Array Int) (mode : Bool) (res : Int) : Prop :=
  res = if mode then posSum a else totalSum a

-- Correct implementation — Expected: PASS
method branchSum (a : Array Int) (mode : Bool)
  return (res : Int)
  require True
  ensures postconditionBS a mode res
  do
    let mut s : Int := 0
    match mode with
    | true =>
      let mut i : Nat := 0
      while i < a.size
        invariant "bs_t_bounds"  i ≤ a.size
        invariant "bs_t_partial" s = (Array.range i).foldl (fun acc k =>
          if a[k]! > (0: Int) then acc + a[k]! else acc) 0
      do
        if a[i]! > 0 then s := s + a[i]!
        i := i + 1
    | false =>
      let mut i : Nat := 0
      while i < a.size
        invariant "bs_f_bounds"  i ≤ a.size
        invariant "bs_f_partial" s = (Array.range i).foldl (fun acc k =>
          acc + a[k]!) 0
      do
        s := s + a[i]!
        i := i + 1
    return s

velvet_plausible_test branchSum

-- Bug B-1: true branch omits the positivity guard — sums all elements.
-- Expected: FAIL (postcondition violated for arrays with non-positive elements
--           when mode = true)
method branchSumMissingFilter (a : Array Int) (mode : Bool)
  return (res : Int)
  require True
  ensures postconditionBS a mode res
  do
    let mut s : Int := 0
    match mode with
    | true =>
      let mut i : Nat := 0
      while i < a.size
        invariant "bsmf_t_bounds" i ≤ a.size
      do
        s := s + a[i]!   -- BUG: should only add when a[i]! > 0
        i := i + 1
    | false =>
      let mut i : Nat := 0
      while i < a.size
        invariant "bsmf_f_bounds" i ≤ a.size
      do
        s := s + a[i]!
        i := i + 1
    return s

velvet_plausible_test branchSumMissingFilter

-- Bug B-2: match branches swapped — true arm sums all, false arm filters.
-- Expected: FAIL (postcondition violated whenever array has non-positive elements
--           and mode = true, or mode = false with a non-all-positive array)
method branchSumBranchesSwapped (a : Array Int) (mode : Bool)
  return (res : Int)
  require True
  ensures postconditionBS a mode res
  do
    let mut s : Int := 0
    match mode with
    | true =>                       -- BUG: this should be the filtered (posSum) branch
      let mut i : Nat := 0
      while i < a.size
        invariant "bsbs_t_bounds" i ≤ a.size
      do
        s := s + a[i]!
        i := i + 1
    | false =>                      -- BUG: this should be the all-sum (totalSum) branch
      let mut i : Nat := 0
      while i < a.size
        invariant "bsbs_f_bounds" i ≤ a.size
      do
        if a[i]! > 0 then s := s + a[i]!
        i := i + 1
    return s

velvet_plausible_test branchSumBranchesSwapped

-- ============================================================
-- C. match ⊃ while ⊃ match  (two levels of nesting)
-- Problem: absOrParitySum — `mode` selects the per-element aggregation rule:
--   true  → abs sum:     Σ |a[i]|             (sign  match inside while)
--   false → parity sum:  Σ (even→+, odd→−)    (parity match inside while)
-- The outer match dispatches to a branch; each branch holds a while loop
-- whose body contains a second match that classifies the current element.
-- ============================================================


@[loomAbstractionSimp]
def postconditionAP (a : Array Int) (mode : Bool) (res : Int) : Prop :=
  res = if mode then absSum a else parityWeightedSum a

-- Correct implementation — Expected: PASS
method absOrParitySum (a : Array Int) (mode : Bool)
  return (res : Int)
  require True
  ensures postconditionAP a mode res
  do
    let mut s : Int := 0
    match mode with
    | true =>
      -- abs-sum branch: inner match dispatches on sign
      let mut i : Nat := 0
      while i < a.size
        invariant "aops_t_bounds"  i ≤ a.size
        invariant "aops_t_partial" s = (Array.range i).foldl (fun acc k =>
          match compare a[k]! 0 with | .lt => acc - a[k]! | _ => acc + a[k]!) 0
      do
        match compare a[i]! 0 with
        | .lt => s := s - a[i]!   -- negative: |a[i]!| = -a[i]!
        | _   => s := s + a[i]!   -- zero or positive: a[i]! unchanged
        i := i + 1
    | false =>
      -- parity-sum branch: inner match dispatches on value parity
      let mut i : Nat := 0
      while i < a.size
        invariant "aops_f_bounds"  i ≤ a.size
        invariant "aops_f_partial" s = (Array.range i).foldl (fun acc k =>
          if a[k]! % 2 = (0: Int) then acc + a[k]! else acc - a[k]!) 0
      do
        match a[i]! % 2 with
        | 0 => s := s + a[i]!
        | _ => s := s - a[i]!
        i := i + 1
    return s

velvet_plausible_test absOrParitySum

-- Bug C-1: abs-sum branch adds negative elements as-is instead of negating them.
-- Expected: FAIL (postcondition violated for any array with negative elements
--           when mode = true)
method absOrParitySumSignBug (a : Array Int) (mode : Bool)
  return (res : Int)
  require True
  ensures postconditionAP a mode res
  do
    let mut s : Int := 0
    match mode with
    | true =>
      let mut i : Nat := 0
      while i < a.size
        invariant "aopsb_t_bounds" i ≤ a.size
      do
        match compare a[i]! 0 with
        | .lt => s := s + a[i]!   -- BUG: should be - a[i]! to obtain |a[i]!|
        | _   => s := s + a[i]!
        i := i + 1
    | false =>
      let mut i : Nat := 0
      while i < a.size
        invariant "aopsb_f_bounds" i ≤ a.size
      do
        match a[i]! % 2 with
        | 0 => s := s + a[i]!
        | _ => s := s - a[i]!
        i := i + 1
    return s

velvet_plausible_test absOrParitySumSignBug

-- Bug C-2: parity-sum branch has inner match arms swapped —
-- subtracts even-valued elements and adds odd-valued elements.
-- Expected: FAIL (postcondition violated for any array with even-valued elements
--           when mode = false)
method absOrParityParityBug (a : Array Int) (mode : Bool)
  return (res : Int)
  require True
  ensures postconditionAP a mode res
  do
    let mut s : Int := 0
    match mode with
    | true =>
      let mut i : Nat := 0
      while i < a.size
        invariant "aopspb_t_bounds" i ≤ a.size
      do
        match compare a[i]! 0 with
        | .lt => s := s - a[i]!
        | _   => s := s + a[i]!
        i := i + 1
    | false =>
      let mut i : Nat := 0
      while i < a.size
        invariant "aopspb_f_bounds" i ≤ a.size
      do
        match a[i]! % 2 with
        | 0 => s := s - a[i]!   -- BUG: should be + (even-valued elements should be added)
        | _ => s := s + a[i]!   -- BUG: should be - (odd-valued elements should be subtracted)
        i := i + 1
    return s

velvet_plausible_test absOrParityParityBug
