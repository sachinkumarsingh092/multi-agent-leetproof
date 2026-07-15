import Mathlib.Tactic

namespace VerinaSpec


def nthUglyNumber_precond (n : Nat) : Prop :=
  n > 0

def nextUgly (seq : List Nat) (c2 c3 c5 : Nat) : (Nat × Nat × Nat × Nat) :=
  let i2 := seq[c2]! * 2
  let i3 := seq[c3]! * 3
  let i5 := seq[c5]! * 5
  let next := min i2 (min i3 i5)
  let c2' := if next = i2 then c2 + 1 else c2
  let c3' := if next = i3 then c3 + 1 else c3
  let c5' := if next = i5 then c5 + 1 else c5
  (next, c2', c3', c5')

def divideOut : Nat → Nat → Nat
  | n, p =>
    if h : p > 1 ∧ n > 0 ∧ n % p = 0 then
      have : n / p < n := by
        apply Nat.div_lt_self
        · exact h.2.1  -- n > 0
        · exact Nat.lt_of_succ_le (Nat.succ_le_of_lt h.1)  -- 1 < p, so 2 ≤ p
      divideOut (n / p) p
    else n
termination_by n p => n

def isUgly (x : Nat) : Bool :=
  if x = 0 then
    false
  else
    let n1 := divideOut x 2
    let n2 := divideOut n1 3
    let n3 := divideOut n2 5
    n3 = 1

def nthUglyNumber_postcond (n : Nat) (result: Nat) : Prop :=
  isUgly result = true ∧
  ((List.range (result)).filter (fun i => isUgly i)).length = n - 1

end VerinaSpec

namespace LLMSpec

-- An ugly number is positive and has no prime divisors other than 2, 3, or 5.
-- This is purely relational (no factorization API required).
def IsUgly (x : Nat) : Prop :=
  x > 0 ∧
  ∀ (p : Nat), Nat.Prime p → p ∣ x → (p = 2 ∨ p = 3 ∨ p = 5)

-- Count ugly numbers in the bounded range [0, r].
-- We use Classical decidability to be able to filter by the Prop predicate `IsUgly`.
noncomputable def countUglyUpTo (r : Nat) : Nat :=
  by
    classical
    exact ((Finset.range (r + 1)).filter IsUgly).card

-- Input is a 1-based index into the increasing sequence of ugly numbers.
def precondition (n : Nat) : Prop :=
  n ≥ 1

-- Postcondition: result is the n-th ugly number.
-- Characterization via counting within a bounded range ensures the set is finite in Lean.
-- The pair of equalities pins down the unique n-th ugly number:
-- - there are exactly n ugly numbers ≤ result
-- - there are exactly n-1 ugly numbers ≤ result-1 (so result is the next ugly number)
def postcondition (n : Nat) (result : Nat) : Prop :=
  IsUgly result ∧
  countUglyUpTo result = n ∧
  countUglyUpTo (result - 1) = (n - 1)

end LLMSpec

section Proof

theorem precondition_equiv (n : Nat) :
  VerinaSpec.nthUglyNumber_precond n ↔ LLMSpec.precondition n := by
  sorry

theorem postcondition_equiv (n : Nat) (result: Nat) :
  LLMSpec.precondition n →
  (VerinaSpec.nthUglyNumber_postcond n result ↔ LLMSpec.postcondition n result) := by
  sorry

end Proof
