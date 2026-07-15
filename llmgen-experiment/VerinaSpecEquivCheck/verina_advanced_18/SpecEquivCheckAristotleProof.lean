/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 8e372d4a-f705-42db-b352-42034ff92499

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (n : Nat) : VerinaSpec.isArmstrong_precond n ↔ LLMSpec.precondition n

- theorem postcondition_equiv (n : Nat) (result : Bool) : LLMSpec.precondition n →
  (VerinaSpec.isArmstrong_postcond n result ↔ LLMSpec.postcondition n result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def countDigits (n : Nat) : Nat :=
  let rec go (n acc : Nat) : Nat :=
    if n = 0 then acc
    else go (n / 10) (acc + 1)
  go n (if n = 0 then 1 else 0)

def isArmstrong_precond (n : Nat) : Prop :=
  True

def sumPowers (n : Nat) (k : Nat) : Nat :=
  let rec go (n acc : Nat) : Nat :=
    if n = 0 then acc
    else
      let digit := n % 10
      go (n / 10) (acc + digit ^ k)
  go n 0

def isArmstrong_postcond (n : Nat) (result: Bool) : Prop :=
  let n' := List.foldl (fun acc d => acc + d ^ countDigits n) 0 (List.map (fun c => c.toNat - '0'.toNat) (toString n).toList)
  (result → (n = n')) ∧
  (¬ result → (n ≠ n'))

end VerinaSpec

namespace LLMSpec

-- Helper: decimal digits of `n` in base 10, little-endian (Mathlib `Nat.digits` convention).
-- Note: Mathlib defines `Nat.digits 10 0 = []`.
-- This still makes `0` Armstrong since the empty sum is `0`.
def decDigits (n : Nat) : List Nat :=
  Nat.digits 10 n

-- Helper: number of decimal digits according to `Nat.digits`.
def numDecDigits (n : Nat) : Nat :=
  (decDigits n).length

-- Helper: sum of digit^k, where k is the number of digits.
def armstrongSum (n : Nat) : Nat :=
  let k : Nat := numDecDigits n
  (decDigits n).foldl (fun (acc : Nat) (d : Nat) => acc + d ^ k) 0

-- Armstrong predicate in base 10.
def isArmstrong (n : Nat) : Prop :=
  armstrongSum n = n

-- No input restrictions.
def precondition (n : Nat) : Prop :=
  True

def postcondition (n : Nat) (result : Bool) : Prop :=
  (result = true ↔ isArmstrong n)

end LLMSpec

section Proof

theorem precondition_equiv (n : Nat) : VerinaSpec.isArmstrong_precond n ↔ LLMSpec.precondition n := by
  -- Since both preconditions are True, their equivalence is trivial.
  simp [VerinaSpec.isArmstrong_precond, LLMSpec.precondition]

noncomputable section AristotleLemmas

theorem VerinaSpec_countDigits_eq (n : Nat) :
  VerinaSpec.countDigits n = if n = 0 then 1 else (Nat.digits 10 n).length := by
    unfold VerinaSpec.countDigits;
    -- By definition of `countDigits.go`, we have `countDigits.go n 1 = 1 + (Nat.digits 10 n).length`.
    have h_go : ∀ n acc, VerinaSpec.countDigits.go n acc = acc + (Nat.digits 10 n).length := by
      intro n acc; induction' n using Nat.strong_induction_on with n ih generalizing acc; rcases n with ( _ | _ | n ) <;> simp_all +arith +decide;
      · unfold VerinaSpec.countDigits.go; aesop;
      · unfold VerinaSpec.countDigits.go; aesop;
      · unfold VerinaSpec.countDigits.go; simp +arith +decide [ ih ] ;
        grind +ring;
    aesop

theorem VerinaSpec_sumPowers_eq (n k : Nat) :
  VerinaSpec.sumPowers n k = (Nat.digits 10 n).foldl (fun acc d => acc + d ^ k) 0 := by
    -- By definition of `go`, we can rewrite the left-hand side of the equation.
    have h_go : ∀ m acc, VerinaSpec.sumPowers.go k m acc = List.foldl (fun acc d => acc + d ^ k) acc (Nat.digits 10 m) := by
      intro m acc; induction' m using Nat.strong_induction_on with m ih generalizing acc; rcases m with ( _ | m ) <;> simp_all +decide [ Nat.digits_add ] ;
      · unfold VerinaSpec.sumPowers.go; aesop;
      · unfold VerinaSpec.sumPowers.go; simp +decide [ * ] ;
        exact ih _ ( Nat.div_lt_of_lt_mul <| by linarith ) _;
    exact h_go n 0

theorem digit_char_to_nat_inv (d : Nat) (h : d < 10) :
  (Nat.digitChar d).toNat - '0'.toNat = d := by
    native_decide +revert

theorem toDigitsCore_eq (f n : Nat) (acc : List Char) (h : n < f) (hn : 0 < n) :
  Nat.toDigitsCore 10 f n acc = (Nat.digits 10 n).reverse.map Nat.digitChar ++ acc := by
    -- We'll use induction on `n`.
    induction' n using Nat.strong_induction_on with n ih generalizing f acc;
    by_cases h₂ : n < 10;
    · interval_cases n <;> simp +decide [ Nat.toDigitsCore ];
      all_goals rcases f with ( _ | _ | f ) <;> simp +arith +decide [ Nat.toDigitsCore ] at *;
    · unfold Nat.toDigitsCore;
      rcases f with ( _ | _ | f ) <;> simp_all +decide [ Nat.div_eq_of_lt ];
      grind

theorem toDigits_eq_digits_reverse (n : Nat) (h : n ≠ 0) :
  Nat.toDigits 10 n = (Nat.digits 10 n).reverse.map Nat.digitChar := by
    rw [ Nat.toDigits ];
    rw [ toDigitsCore_eq ];
    · norm_num +zetaDelta at *;
    · grind;
    · exact Nat.pos_of_ne_zero h

theorem digits_correspondence (n : Nat) (h : n ≠ 0) :
  (List.map (fun c => c.toNat - '0'.toNat) (toString n).toList) = (Nat.digits 10 n).reverse := by
    convert congr_arg _ ( toDigits_eq_digits_reverse n h ) using 1;
    refine' List.ext_get _ _ <;> simp +decide [ digit_char_to_nat_inv ];
    intro i hi₁ hi₂; have := Nat.digits_lt_base' ( show ( Nat.digits 10 n)[(Nat.digits 10 n).length - 1 - i] ∈ Nat.digits 10 n from by { exact List.getElem_mem _ } ) ; interval_cases ( Nat.digits 10 n)[(Nat.digits 10 n).length - 1 - i] <;> trivial;

theorem foldl_add_pow_eq_sum_map (l : List Nat) (k : Nat) :
  List.foldl (fun acc d => acc + d ^ k) 0 l = (l.map (fun d => d ^ k)).sum := by
    induction l using List.reverseRecOn <;> aesop

theorem foldl_add_pow_reverse (l : List Nat) (k : Nat) :
  List.foldl (fun acc d => acc + d ^ k) 0 l.reverse = List.foldl (fun acc d => acc + d ^ k) 0 l := by
    induction' l using List.reverseRecOn with d l ih <;> simp +decide [ *, add_comm ];
    induction' d using List.reverseRecOn with d l ih <;> simp_all +decide [ add_comm, add_left_comm, add_assoc ];
    have h_foldr : ∀ (l : List ℕ) (a b : ℕ), List.foldr (fun x y => y + x ^ k) (a + b) l = a + List.foldr (fun x y => y + x ^ k) b l := by
      intro l a b; induction l <;> simp +decide [ * ] ; ring;
    rw [ h_foldr, ih ]

theorem VerinaSpec_sum_eq_LLMSpec_sum (n : Nat) :
  let k := VerinaSpec.countDigits n
  let digits_verina := List.map (fun c => c.toNat - '0'.toNat) (toString n).toList
  List.foldl (fun acc d => acc + d ^ k) 0 digits_verina =
  LLMSpec.armstrongSum n := by
    by_cases hn : n = 0;
    · subst hn; native_decide;
    · unfold LLMSpec.armstrongSum;
      convert foldl_add_pow_reverse _ _ using 2;
      · convert digits_correspondence n hn using 1;
      · rw [ VerinaSpec_countDigits_eq ];
        unfold LLMSpec.numDecDigits; aesop;

end AristotleLemmas

theorem postcondition_equiv (n : Nat) (result : Bool) : LLMSpec.precondition n →
  (VerinaSpec.isArmstrong_postcond n result ↔ LLMSpec.postcondition n result) := by
  unfold VerinaSpec.isArmstrong_postcond LLMSpec.postcondition LLMSpec.isArmstrong;
  have := VerinaSpec_sum_eq_LLMSpec_sum n;
  grind

end Proof