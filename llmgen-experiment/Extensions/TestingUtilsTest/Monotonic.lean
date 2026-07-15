import Velvet.Std
import Extensions.Testing
import Extensions.VelvetPBT
import Extensions.SpecDSL
-- Never add new imports here

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    mbpp_id_68: Check whether a given integer array is monotonic.
    Natural language breakdown:
    1. Input is an array A of integers.
    2. The array is monotonic if it is nondecreasing (never goes down) or nonincreasing (never goes up).
    3. Nondecreasing means: for every adjacent pair i,i+1 in bounds, A[i] ≤ A[i+1].
    4. Nonincreasing means: for every adjacent pair i,i+1 in bounds, A[i] ≥ A[i+1].
    5. Arrays of length 0 or 1 are monotonic (vacuously satisfy both adjacent conditions).
    6. The method returns a boolean indicating whether A is monotonic.
-/

section Specs
-- Helper predicates describing monotonicity via adjacent comparisons.
-- Using adjacent comparisons avoids needing more complex quantification over all i < j.
def isNondecreasing (A : Array Int) : Prop :=
  ∀ (i : Nat), i + 1 < A.size → A[i]! ≤ A[i + 1]!

def isNonincreasing (A : Array Int) : Prop :=
  ∀ (i : Nat), i + 1 < A.size → A[i]! ≥ A[i + 1]!

-- No preconditions: any integer array is allowed.
def precondition (A : Array Int) : Prop :=
  True

-- The result is true iff A is nondecreasing or nonincreasing (adjacent-wise).
def postcondition (A : Array Int) (res : Bool) : Prop :=
  res = true ↔ (isNondecreasing A ∨ isNonincreasing A)
end Specs

section Impl
method isMonotonic (A : Array Int)
  return (res : Bool)
  require precondition A
  ensures postcondition A res
  do
    -- Arrays of size 0 or 1 are monotone.
    if A.size ≤ 1 then
      return true
    else
      let mut nondec := true
      let mut noninc := true
      let mut i : Nat := 0
      while i + 1 < A.size
        -- Bounds on the loop index.
        -- Init: i = 0 and A.size > 1 in this branch, so i ≤ A.size - 1.
        -- Preserved: i increases by 1 while guard ensures i+1 < A.size.
        invariant "inv_bounds" i ≤ A.size - 1
        -- Characterize the flags by exactly what has been checked so far.
        -- Init: for i = 0, the quantified range j < 0 is empty, so both sides are true.
        -- Preserved: each step updates the flag precisely according to the new comparison at index i.
        -- Suffices: at exit we have A.size ≤ i+1, so all adjacent pairs are covered.
        invariant "inv_nondec_iff_checked" (nondec = true ↔ ∀ j : Nat, j < i → A[j]! ≤ A[j + 1]!)
        invariant "inv_noninc_iff_checked" (noninc = true ↔ ∀ j : Nat, j < i → A[j]! ≥ A[j + 1]!)
      do
        if A[i]! > A[i + 1]! then
          nondec := false
        if A[i]! < A[i + 1]! then
          noninc := false
        i := i + 1
      return (nondec || noninc)
end Impl

velvet_plausible_test isMonotonic (config := { maxMs := some 5000 })
