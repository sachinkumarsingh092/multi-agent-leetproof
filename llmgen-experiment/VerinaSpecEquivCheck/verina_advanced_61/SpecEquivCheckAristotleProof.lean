/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 3a8c73bb-da94-4f28-958c-a277ca51907e

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (nums : List Int) : VerinaSpec.productExceptSelf_precond nums ↔ LLMSpec.precondition nums

- theorem postcondition_equiv (nums : List Int) (result : List Int) : LLMSpec.precondition nums →
  (VerinaSpec.productExceptSelf_postcond nums result ↔ LLMSpec.postcondition nums result)
-/

import Mathlib.Tactic


def List.myprod : List Int → Int
  | [] => 1
  | x :: xs => x * xs.myprod

namespace VerinaSpec

def productExceptSelf_precond (nums : List Int) : Prop :=
  True

def computepref (nums : List Int) : List Int :=
  nums.foldl (fun acc x => acc ++ [acc.getLast! * x]) [1]

def computeSuffix (nums : List Int) : List Int :=
  let revSuffix := nums.reverse.foldl (fun acc x => acc ++ [acc.getLast! * x]) [1]
  revSuffix.reverse

def productExceptSelf_postcond (nums : List Int) (result: List Int) : Prop :=
  nums.length = result.length ∧
  (List.range nums.length |>.all (fun i =>
    result[i]! = some (((List.take i nums).myprod) * ((List.drop (i+1) nums).myprod))))

end VerinaSpec

namespace LLMSpec

-- Helper: product of a list of Int, with empty product = 1.
-- We use foldl to define the mathematical product.
def listProd (xs : List Int) : Int :=
  xs.foldl (fun acc x => acc * x) 1

-- No additional input restrictions are required for mathematical correctness in Int.
-- (The problem statement mentions 32-bit bounds, but Int is unbounded in Lean.)
def precondition (nums : List Int) : Prop :=
  True

-- The result has the same length, and each element is the product of all elements except itself.
-- This is specified via prefix/suffix products using take/drop.
def postcondition (nums : List Int) (result : List Int) : Prop :=
  result.length = nums.length ∧
  ∀ (i : Nat), i < nums.length →
    result[i]! = (listProd (nums.take i)) * (listProd (nums.drop (i + 1)))

end LLMSpec

section Proof

theorem precondition_equiv (nums : List Int) : VerinaSpec.productExceptSelf_precond nums ↔ LLMSpec.precondition nums := by
  -- Since both preconditions are True, their equivalence is trivial.
  simp [VerinaSpec.productExceptSelf_precond, LLMSpec.precondition]

theorem postcondition_equiv (nums : List Int) (result : List Int) : LLMSpec.precondition nums →
  (VerinaSpec.productExceptSelf_postcond nums result ↔ LLMSpec.postcondition nums result) := by
  -- By definition of `productExceptSelf_postcond` and `postcondition`, we know that they are equivalent under the given preconditions.
  simp [VerinaSpec.productExceptSelf_postcond, LLMSpec.postcondition];
  -- By definition of `List.myprod`, we know that it is equal to `List.prod`.
  have h_prod_eq : ∀ (l : List ℤ), List.myprod l = List.prod l := by
    intro l; induction l <;> simp +decide [ *, List.prod_cons ] ;
    exact?;
  simp [h_prod_eq, LLMSpec.listProd];
  simp +decide [ eq_comm, List.prod_eq_foldl ]

end Proof