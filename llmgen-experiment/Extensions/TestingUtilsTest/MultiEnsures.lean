import Velvet.Std
import Extensions.Testing
import Extensions.VelvetPBT
import Extensions.SpecDSL
-- Never add new imports here

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/-
  Tests for per-conjunct postcondition checking in velvet_plausible_test.

  Two scenarios:

  A. Multiple `ensures` clauses — velvet_plausible_test tests each clause
     independently so one uncheckable clause does not silence the others.

  B. A single `ensures` whose postcondition `def` unfolds (via whnf) to a
     conjunction — velvet_plausible_test splits the def into conjuncts and
     tests each one independently.

  Each section has a correct (Expected: PASS) and buggy (Expected: FAIL) variant.
-/

-- ============================================================
-- A. Multiple `ensures` clauses
-- ============================================================

-- ME-A1: both clauses correct — Expected: PASS
-- Clause 1: ans = x + y  (exact value)
-- Clause 2: ans ≥ x      (lower-bound property)
method addMultiEns (x : Nat) (y : Nat)
  return (ans : Nat)
  ensures ans = x + y
  ensures ans ≥ x
  do
    return x + y

velvet_plausible_test addMultiEns

-- ME-A2: second clause has wrong sign — Expected: FAIL (postcondition (2 of 2))
-- Clause 1 holds, Clause 2 claims ans ≤ x which fails when y > 0.
method addMultiEnsBugSecond (x : Nat) (y : Nat)
  return (ans : Nat)
  ensures ans = x + y
  ensures ans ≤ x    -- BUG: should be ≥
  do
    return x + y

velvet_plausible_test addMultiEnsBugSecond

-- ME-A3: first clause has wrong value — Expected: FAIL (postcondition (1 of 2))
-- The second clause (ans ≥ x) would pass on its own, but the first fails.
method addMultiEnsBugFirst (x : Nat) (y : Nat)
  return (ans : Nat)
  ensures ans = x + y + 1    -- BUG: off by one
  ensures ans ≥ x
  do
    return x + y

velvet_plausible_test addMultiEnsBugFirst

-- ME-A4: three clauses, middle one buggy — Expected: FAIL (postcondition (2 of 3))
method mulTripleEns (x : Nat) (y : Nat)
  return (ans : Nat)
  ensures ans = x * y
  ensures ans ≥ x + y        -- BUG: fails for small values (e.g. x=1, y=1: 1 ≥ 2 is false)
  ensures ans % 1 = 0        -- trivially true
  do
    return x * y

velvet_plausible_test mulTripleEns

-- ============================================================
-- B. Single `ensures` whose postcondition def unfolds to a conjunction
-- ============================================================

-- Postcondition defs — plain `def` (semireducible), unfolded by whnf inside splitAndConjuncts.

def addConjPost (x y ans : Nat) : Prop :=
  ans = x + y ∧ ans ≥ x

def mulConjPost (x y ans : Nat) : Prop :=
  ans = x * y ∧ (x = 0 → ans = 0) ∧ (y = 0 → ans = 0)

-- ME-B1: correct implementation, def unfolds to 2-conjunction — Expected: PASS
method addDefEns (x : Nat) (y : Nat)
  return (ans : Nat)
  ensures addConjPost x y ans
  do
    return x + y

velvet_plausible_test addDefEns

-- ME-B2: implementation returns x + y + 1, first conjunct fails — Expected: FAIL
method addDefEnsBug (x : Nat) (y : Nat)
  return (ans : Nat)
  ensures addConjPost x y ans
  do
    return x + y + 1    -- BUG

velvet_plausible_test addDefEnsBug

-- ME-B3: correct multiplication, def unfolds to 3-conjunction — Expected: PASS
method mulDefEns (x : Nat) (y : Nat)
  return (ans : Nat)
  ensures mulConjPost x y ans
  do
    return x * y

velvet_plausible_test mulDefEns

-- ME-B4: returns x * y + 1, all conjuncts fail except the trivial tautologies — Expected: FAIL
method mulDefEnsBug (x : Nat) (y : Nat)
  return (ans : Nat)
  ensures mulConjPost x y ans
  do
    return x * y + 1    -- BUG

velvet_plausible_test mulDefEnsBug

-- ============================================================
-- C. Mixed: multiple `ensures` where one is a def-conjunction
-- ============================================================

-- ME-C1: one bare clause + one def-conjunction clause — Expected: PASS
-- After splitting: [ans ≥ 0, ans = x + y, ans ≥ x]
-- (ans ≥ 0 is trivially true for Nat; addConjPost splits to 2 more)
method addMixed (x : Nat) (y : Nat)
  return (ans : Nat)
  ensures ans ≥ 0              -- always true for Nat
  ensures addConjPost x y ans  -- unfolds to 2 conjuncts
  do
    return x + y

velvet_plausible_test addMixed

-- ME-C2: second ensures is buggy def — Expected: FAIL
def addConjPostBuggy (x y ans : Nat) : Prop :=
  ans = x + y ∧ ans = x * y   -- second conjunct wrong (only holds when y = 1 or x = 0)

method addMixedBug (x : Nat) (y : Nat)
  return (ans : Nat)
  ensures ans ≥ 0
  ensures addConjPostBuggy x y ans
  do
    return x + y

velvet_plausible_test addMixedBug
