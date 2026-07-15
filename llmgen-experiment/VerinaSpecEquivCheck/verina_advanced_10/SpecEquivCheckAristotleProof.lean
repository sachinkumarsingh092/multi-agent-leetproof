/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: dcf88fc4-b7c3-4086-8aa3-1964b0969a0c

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was negated by Aristotle:

- theorem precondition_equiv (n : Nat) (primes : List Nat) : VerinaSpec.findExponents_precond n primes ↔ LLMSpec.precondition n primes

- theorem postcondition_equiv (n : Nat) (primes : List Nat) (result : List (Nat × Nat)) : LLMSpec.precondition n primes →
  (VerinaSpec.findExponents_postcond n primes result ↔ LLMSpec.postcondition n primes result)

Here is the code for the `negate_state` tactic, used within these negations:

```lean
import Mathlib
open Lean Meta Elab Tactic in
elab "revert_all" : tactic => do
  let goals ← getGoals
  let mut newGoals : List MVarId := []
  for mvarId in goals do
    newGoals := newGoals.append [(← mvarId.revertAll)]
  setGoals newGoals

open Lean.Elab.Tactic in
macro "negate_state" : tactic => `(tactic|
  (
    guard_goal_nums 1
    revert_all
    refine @(((by admit) : ∀ {p : Prop}, ¬p → p) ?_)
    try (push_neg; guard_goal_nums 1)
  )
)
```
-/

import Mathlib.Tactic

import Mathlib.Data.Nat.Prime.Defs


namespace VerinaSpec

def findExponents_precond (n : Nat) (primes : List Nat) : Prop :=
  n > 0 ∧
  primes.length > 0 ∧
  primes.all (fun p => Nat.Prime p) ∧
  List.Nodup primes

def findExponents_postcond (n : Nat) (primes : List Nat) (result: List (Nat × Nat)) : Prop :=
  (n = result.foldl (fun acc (p, e) => acc * p ^ e) 1) ∧
  result.all (fun (p, _) => p ∈ primes) ∧
  primes.all (fun p => result.any (fun pair => pair.1 = p))

end VerinaSpec

namespace LLMSpec

-- Helper: multiply all prime powers described by a list of pairs.
-- (p,e) contributes p^e.
def primePowerProduct (l : List (Nat × Nat)) : Nat :=
  (l.map (fun pe : Nat × Nat => pe.1 ^ pe.2)).prod

-- Helper: semantic characterization of the exponent of p in n.
-- e is the unique exponent such that p^e ∣ n but p^(e+1) ∤ n.
def isPrimeExponentOf (n : Nat) (p : Nat) (e : Nat) : Prop :=
  (p ^ e ∣ n) ∧ ¬ (p ^ (e + 1) ∣ n)

def precondition (n : Nat) (primes : List Nat) : Prop :=
  n > 0 ∧
  primes ≠ [] ∧
  primes.Nodup ∧
  (∀ p : Nat, p ∈ primes → Nat.Prime p) ∧
  -- Coverage: if a prime divides n, it must be listed.
  (∀ p : Nat, Nat.Prime p → p ∣ n → p ∈ primes)

def postcondition (n : Nat) (primes : List Nat) (result : List (Nat × Nat)) : Prop :=
  -- One output pair per input prime, and positional alignment to make the result unique.
  result.length = primes.length ∧
  (∀ i : Nat, i < primes.length →
    let p := primes.get! i
    let pe := result.get! i
    pe.1 = p ∧
    Nat.Prime p ∧
    isPrimeExponentOf n p pe.2) ∧
  -- Reconstruction: multiplying all returned prime powers yields n.
  n = primePowerProduct result

end LLMSpec

section Proof

/- Aristotle found this block to be false. Here is a proof of the negation:

noncomputable section AristotleLemmas

/-
There exist n and primes such that VerinaSpec's precondition holds but LLMSpec's precondition does not.
-/
theorem counterexample_exists : ∃ n primes, VerinaSpec.findExponents_precond n primes ∧ ¬ LLMSpec.precondition n primes := by
  use 6, [ 2 ];
  unfold VerinaSpec.findExponents_precond LLMSpec.precondition; norm_num;
  exists 3

end AristotleLemmas

theorem precondition_equiv (n : Nat) (primes : List Nat) : VerinaSpec.findExponents_precond n primes ↔ LLMSpec.precondition n primes := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- By definition of `counterexample_exists`, there exist `n` and `primes` such that `VerinaSpec.findExponents_precond n primes` holds but `LLMSpec.precondition n primes` does not.
  apply counterexample_exists.elim; intro n hn; apply hn.elim; intro primes hprimes; use n, primes; aesop;

-/
theorem precondition_equiv (n : Nat) (primes : List Nat) : VerinaSpec.findExponents_precond n primes ↔ LLMSpec.precondition n primes := by
  sorry

/- Aristotle found this block to be false. Here is a proof of the negation:



theorem postcondition_equiv (n : Nat) (primes : List Nat) (result : List (Nat × Nat)) : LLMSpec.precondition n primes →
  (VerinaSpec.findExponents_postcond n primes result ↔ LLMSpec.postcondition n primes result) := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Let's choose n = 24 and primes = [2, 3].
  use 24, [2, 3];
  -- Let's choose the result list [(3, 1), (2, 3)].
  use [(3, 1), (2, 3)];
  -- Let's verify the conditions for the chosen result.
  simp [LLMSpec.precondition, VerinaSpec.findExponents_postcond, LLMSpec.postcondition];
  -- Let's simplify the goal.
  simp +decide [LLMSpec.isPrimeExponentOf, LLMSpec.primePowerProduct] at *;
  intro p pp dp; have := Nat.le_of_dvd ( by decide ) dp; interval_cases p <;> trivial;

-/
theorem postcondition_equiv (n : Nat) (primes : List Nat) (result : List (Nat × Nat)) : LLMSpec.precondition n primes →
  (VerinaSpec.findExponents_postcond n primes result ↔ LLMSpec.postcondition n primes result) := by
  sorry

end Proof