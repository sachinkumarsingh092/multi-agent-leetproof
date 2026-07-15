import Velvet.Std
import CaseStudies.TestingUtil
import Extensions.SpecDSL
import Extensions.Testing
import Extensions.VelvetPBT

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- ============================================================
-- Correct methods (expected: PASS)
-- ============================================================

-- Ex 1: addition via loop (two invariants + postcondition)
method add (x : Nat) (y : Nat)
  return (ans : Nat)
  ensures ans = x + y
  do
    let mut x' := x
    let mut y' := y
    while (x' > 0)
    invariant x' + y' = x + y
    invariant x >= 0
    invariant y >= 0
    do
      x' := x' - 1
      y' := y' + 1
    return y'

velvet_plausible_test add

-- Ex 2: count down to zero (single inequality invariant)
method countdown (n : Nat)
  return (ans : Nat)
  ensures ans = 0
  do
    let mut i := n
    while (i > 0)
    invariant i <= n
    do
      i := i - 1
    return i

velvet_plausible_test countdown

-- Ex 3: multiplication via repeated addition (multiplicative invariant)
method mul (x : Nat) (y : Nat)
  return (ans : Nat)
  ensures ans = x * y
  do
    let mut result := 0
    let mut cnt := x
    while (cnt > 0)
    invariant result + cnt * y = x * y
    do
      result := result + y
      cnt := cnt - 1
    return result

velvet_plausible_test mul

-- Ex 4: trivial identity (no loop, no invariants — degenerate case)
method identity (x : Nat)
  return (ans : Nat)
  ensures ans = x
  do
    return x

velvet_plausible_test identity

-- Ex 5: early exit via break (loop has two exits: guard + break)
method sumUntilLimit (n : Nat) (limit : Nat)
  return (ans : Nat)
  ensures ans <= limit
  do
    let mut s := 0
    let mut i := 0
    while (i < n)
    invariant s <= limit
    do
      if s + 1 > limit then
        break
      s := s + 1
      i := i + 1
    return s

velvet_plausible_test sumUntilLimit

-- Ex 6: search with early break
method findFirst (n : Nat) (target : Nat)
  return (ans : Nat)
  ensures True
  do
    let mut i := 0
    while (i < n)
    invariant i <= n
    do
      if i = target then
        break
      i := i + 1
    return i

velvet_plausible_test findFirst

-- Ex 7: match expression inside while loop body
method tripleCount (n : Nat)
  return (ans : Nat)
  ensures True
  do
    let mut cnt := 0
    let mut i := 0
    while (i < n)
    invariant i <= n
    do
      match i % 3 with
      | 0 => cnt := cnt + 3
      | 1 => cnt := cnt + 1
      | _ => cnt := cnt + 2
      i := i + 1
    return cnt

velvet_plausible_test tripleCount

-- Ex 8: nested while loops with invariants at each level
method nestedLoop (n : Nat)
  return (ans : Nat)
  ensures ans = n * n
  do
    let mut total := 0
    let mut i := 0
    while (i < n)
    invariant total = i * n
    invariant i <= n
    do
      let mut j := 0
      while (j < n)
      invariant j <= n
      do
        total := total + 1
        j := j + 1
      i := i + 1
    return total

velvet_plausible_test nestedLoop

-- Ex 9: match selects initial value before loop
method conditionalCount (n : Nat) (fromHalf : Bool)
  return (ans : Nat)
  ensures True
  do
    let mut i := match fromHalf with
                 | true  => n / 2
                 | false => 0
    let start := i
    while (i < n)
    invariant i <= n
    do
      i := i + 1
    return i - start

velvet_plausible_test conditionalCount

-- Ex 10: match ⊃ loop ⊃ match ⊃ loop (deep nesting)
method deepNested (n : Nat) (flag : Bool)
  return (ans : Nat)
  ensures True
  do
    let mut total := 0
    match flag with
    | true =>
      let mut i := 0
      while (i < n)
      invariant i <= n
      do
        match i % 2 with
        | 0 =>
          let mut j := 0
          while (j < i)
          invariant j <= i
          do
            total := total + 1
            j := j + 1
        | _ => total := total + i
        i := i + 1
    | false => total := n * 2
    return total

velvet_plausible_test deepNested

-- ============================================================
-- Intentionally buggy methods — verifying that velvet_plausible_test
-- can detect errors (all expected: FAIL)
-- ============================================================

-- Bug 1: wrong postcondition (program returns x+y, spec claims x+y+1)
-- Expected: FAIL (postcondition check fails)
method addWrongPost (x : Nat) (y : Nat)
  return (ans : Nat)
  ensures ans = x + y + 1   -- BUG: should be ans = x + y
  do
    let mut x' := x
    let mut y' := y
    while (x' > 0)
    invariant x' + y' = x + y
    do
      x' := x' - 1
      y' := y' + 1
    return y'

velvet_plausible_test addWrongPost

-- Bug 2: wrong invariant (violated from the very first check)
-- Invariant x'+y' = x+y+1 fails immediately since x'=x, y'=y → x+y ≠ x+y+1
-- Expected: FAIL (invariant violation → DivM.div)
method addWrongInv (x : Nat) (y : Nat)
  return (ans : Nat)
  ensures ans = x + y
  do
    let mut x' := x
    let mut y' := y
    while (x' > 0)
    invariant "test" x' + y' = x + y + 1  -- BUG: off by 1
    do
      x' := x' - 1
      y' := y' + 1
    return y'

velvet_plausible_test addWrongInv

-- Bug 3: loop body bug (y' incremented by 2 instead of 1)
-- Invariant x'+y' = x+y breaks from the second iteration onward
-- Expected: FAIL (invariant violation → DivM.div)
method addBodyBug (x : Nat) (y : Nat)
  return (ans : Nat)
  ensures ans = x + y
  do
    let mut x' := x
    let mut y' := y
    while (x' > 0)
    invariant "sum_unchange" x' + y' = x + y
    do
      x' := x' - 1
      y' := y' + 2  -- BUG: should be + 1
    return y'

velvet_plausible_test addBodyBug

-- Bug 4: multiplication invariant missing the factor y
-- Correct invariant: result + cnt * y = x * y
-- Written as:       result + cnt     = x * y  (wrong for most inputs)
-- Expected: FAIL (invariant violation → DivM.div)
method mulWrongInv (x : Nat) (y : Nat)
  return (ans : Nat)
  ensures ans = x * y
  do
    let mut result := 0
    let mut cnt := x
    while (cnt > 0)
    invariant result + cnt = x * y  -- BUG: missing * y
    do
      result := result + y
      cnt := cnt - 1
    return result

velvet_plausible_test mulWrongInv

-- ============================================================
-- Mid-loop bugs — invariant holds for the first few iterations,
-- then breaks partway through
-- ============================================================

-- Mid-1: bug fires only at iteration where x'=2 (adds 2 instead of 1)
-- Iterations 1,2: invariant holds.  Iteration 3 (x'=2): y'+=2 (BUG).
-- Iteration 4 (x'=1): check x'+y' = x+y → fails.
-- Requires x >= 4 to expose (x=3 is caught by postcondition instead).
-- Expected: FAIL
method addBugAt2 (x : Nat) (y : Nat)
  return (ans : Nat)
  ensures ans = x + y
  do
    let mut x' := x
    let mut y' := y
    while (x' > 0)
    invariant x' + y' = x + y
    do
      if x' = 2 then
        y' := y' + 2  -- BUG: should be + 1
      else
        y' := y' + 1
      x' := x' - 1
    return y'

velvet_plausible_test addBugAt2

-- Mid-2: multiplication, bug fires at the midpoint step (cnt = x/2+1)
-- First (x - x/2 - 1) iterations are correct; one step adds 1 extra.
-- For x=4, y=2: iterations 1,2 pass; iteration 3 (cnt=3=4/2+1) fails.
-- Expected: FAIL
method mulMidpointBug (x : Nat) (y : Nat)
  return (ans : Nat)
  ensures ans = x * y
  do
    let mut result := 0
    let mut cnt := x
    while (cnt > 0)
    invariant result + cnt * y = x * y
    do
      if cnt = x / 2 + 1 then
        result := result + y + 1  -- BUG: adds 1 extra at the midpoint step
      else
        result := result + y
      cnt := cnt - 1
    return result

velvet_plausible_test mulMidpointBug

-- Mid-3: sum 1+2+...+n with a bug on even steps
-- Invariant: 2*s = i*(i+1)   (i.e. s = sum of 1..i)
-- Odd steps: s += i (correct).  Even steps: s += i+1 (BUG).
-- Iteration 1 (i=1, odd):  s=1,  2*1=1*2  ✓
-- Iteration 2 (i=2, even, BUG): s=1+(2+1)=4, 2*4=8 ≠ 2*3=6  ✗ FAIL
-- Expected: FAIL for n >= 2
method sumEvenBug (n : Nat)
  return (ans : Nat)
  ensures False
  do
    let mut s := 0
    let mut i := 0
    while (i < n)
    invariant "test2" 2 * s = i * (i + 1)
    do
      i := i + 1
      if i % 2 = 0 then
        s := s + i + 1  -- BUG: should add i, not i+1, on even steps
      else
        s := s + i
    return s

velvet_plausible_test sumEvenBug

-- ============================================================
-- Decreasing-measure runtime checks
-- ============================================================

-- Test D1: correct countdown with decreasing measure — Expected: PASS
-- Measure i strictly decreases each iteration.
set_option loom.linter.warnings false in
method countdownDecr (n : Nat)
  return (ans : Nat)
  ensures ans = 0
  do
    let mut i := n
    while (i > 0)
    invariant i <= n
    decreasing i
    do
      i := i - 1
    return i

set_option loom.linter.warnings false in
velvet_plausible_test countdownDecr

-- Test D2: measure increases each iteration (BUG) — Expected: FAIL
-- i goes n, n+1, n+2, ...; velvetCheckDecreasingM detects non-decrease → DivM.div
set_option loom.linter.warnings false in
method countupBug (n : Nat)
  return (ans : Nat)
  ensures False
  do
    let mut i := n
    while (i > 0)
    invariant True
    decreasing i
    do
      i := i + 1   -- BUG: should be i - 1; measure strictly increases
    return i

set_option loom.linter.warnings false in
velvet_plausible_test countupBug

-- ============================================================
-- done_with runtime checks
-- ============================================================

-- DW 1: correct done_with — count-up loop exits precisely at i = n (PASS)
-- Guard ¬(i < n) + invariant i ≤ n  →  i = n at exit.
method countDone (n : Nat)
  return (ans : Nat)
  ensures ans = n
  do
    let mut i := 0
    while i < n
    invariant i ≤ n
    done_with i = n
    do
      i := i + 1
    return i

velvet_plausible_test countDone

-- DW 2: correct done_with — countdown exits at cnt = 0 (PASS)
-- Guard ¬(cnt > 0) for Nat means cnt = 0.
method mulDoneCorrect (x : Nat) (y : Nat)
  return (ans : Nat)
  ensures ans = x * y
  do
    let mut result := 0
    let mut cnt := x
    while cnt > 0
    invariant result + cnt * y = x * y
    done_with cnt = 0
    do
      result := result + y
      cnt := cnt - 1
    return result

velvet_plausible_test mulDoneCorrect

-- DW 3: correct done_with with break — disjunction covers both exits (PASS)
-- done_with is only evaluated on guard-false exit (i = a.size).
-- On break (found = true, i < a.size) the check is skipped entirely.
-- The left disjunct i = a.size makes the guard-exit case trivially true.
method findTargetDone (a : Array Nat) (target : Nat)
  return (ans : Bool)
  ensures True
  do
    let mut found := false
    let mut i := 0
    while i < a.size
    invariant i ≤ a.size
    done_with i = a.size ∨ found = true
    do
      if a[i]! = target then
        found := true
        break
      i := i + 1
    return found

velvet_plausible_test findTargetDone

-- DW 4: wrong done_with — claims i = 0 at exit, but loop exits at i = n (FAIL)
-- For any n > 0 the guard becomes false at i = n, and the check i = 0 fails.
-- Expected: FAIL
method countDoneWrong (n : Nat)
  return (ans : Nat)
  ensures True
  do
    let mut i := 0
    while i < n
    invariant i ≤ n
    done_with i = 0   -- BUG: should be i = n
    do
      i := i + 1
    return i

velvet_plausible_test countDoneWrong

-- DW 5: wrong done_with — restates the loop guard, which is always false at exit (FAIL)
-- A while loop exits precisely when its guard is false, so done_with <guard>
-- is always violated on normal termination.
-- Expected: FAIL (for x = 0 the guard is false immediately; for x > 0 the loop
--           runs to x' = 0; in both cases x' > 0 is false at the done_with check)
method addDoneGuard (x : Nat) (y : Nat)
  return (ans : Nat)
  ensures True
  do
    let mut x' := x
    let mut y' := y
    while x' > 0
    invariant x' + y' = x + y
    done_with x' > 0   -- BUG: loop exits when x' = 0, so x' > 0 is always false here
    do
      x' := x' - 1
      y' := y' + 1
    return y'

velvet_plausible_test addDoneGuard

-- DW 6: wrong done_with for break loop — claims found = true on guard-exit (FAIL)
-- done_with is only checked when the loop guard becomes false (i = a.size).
-- We use target = a.size + 1, which cannot appear as an array element when all
-- elements are generated in range [0, size], so the loop always exits via the
-- guard (not break), guaranteeing the done_with check fires.
-- When it fires, found = false, so done_with found = true fails.
-- Expected: FAIL
method findTargetWrongDone (a : Array Nat)
  return (ans : Bool)
  ensures True
  do
    -- target is one past the last valid index — guaranteed absent from the array
    -- when Plausible generates elements bounded by the array size.
    let target := a.size + 1
    let mut found := false
    let mut i := 0
    while i < a.size
    invariant i ≤ a.size
    done_with found = true   -- BUG: loop always exits via guard with found = false
    do
      if a[i]! = target then
        found := true
        break
      i := i + 1
    return found

velvet_plausible_test findTargetWrongDone
