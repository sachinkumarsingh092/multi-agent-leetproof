/- This proof typecheks under Lean 4.28 -/

import Mathlib.Tactic

namespace VerinaSpec


def maxProfit_precond (prices : List Nat) : Prop :=
  True

def updateMinAndProfit (price : Nat) (minSoFar : Nat) (maxProfit : Nat) : (Nat × Nat) :=
  let newMin := Nat.min minSoFar price
  let profit := if price > minSoFar then price - minSoFar else 0
  let newMaxProfit := Nat.max maxProfit profit
  (newMin, newMaxProfit)

def maxProfitAux (prices : List Nat) (minSoFar : Nat) (maxProfit : Nat) : Nat :=
  match prices with
  | [] => maxProfit
  | p :: ps =>
    let (newMin, newProfit) := updateMinAndProfit p minSoFar maxProfit
    maxProfitAux ps newMin newProfit

def maxProfit_postcond (prices : List Nat) (result: Nat) : Prop :=
  List.Pairwise (fun ⟨pi, i⟩ ⟨pj, j⟩ => i < j → pj - pi ≤ result) prices.zipIdx ∧
  (result = 0 ↔
    (prices.length ≤ 1 ∨
     prices.zipIdx.all (fun ⟨pi, i⟩ =>
       prices.zipIdx.all (fun ⟨pj, j⟩ => i ≥ j ∨ pj ≤ pi)))) ∧
  (result > 0 → prices.zipIdx.any (fun ⟨pi, i⟩ =>
    prices.zipIdx.any (fun ⟨pj, j⟩ => i < j ∧ pj - pi = result)))

end VerinaSpec

namespace LLMSpec

-- A realizable profit value from one buy/sell transaction.
def IsTransactionProfit (prices : List Nat) (p : Nat) : Prop :=
  ∃ (i : Nat) (j : Nat),
    i < j ∧ j < prices.length ∧ p = (prices[j]! - prices[i]!)

-- The result upper-bounds all transaction profits.
def IsUpperBoundProfit (prices : List Nat) (ub : Nat) : Prop :=
  ∀ (i : Nat) (j : Nat),
    i < j → j < prices.length → (prices[j]! - prices[i]!) ≤ ub

def precondition (prices : List Nat) : Prop :=
  True

def postcondition (prices : List Nat) (result : Nat) : Prop :=
  (prices.length < 2 ∧ result = 0) ∨
  (2 ≤ prices.length ∧
    IsTransactionProfit prices result ∧
    IsUpperBoundProfit prices result)

end LLMSpec

section Proof

set_option maxHeartbeats 1000000

theorem postcondition_equiv (prices : List Nat) (result : Nat) : LLMSpec.precondition prices →
  VerinaSpec.maxProfit_postcond prices result ↔ LLMSpec.postcondition prices result := by
  constructor <;> intro h' <;> norm_num [ LLMSpec.precondition, LLMSpec.postcondition ] at *;
  · by_cases h : result = 0 <;> simp_all +decide [ LLMSpec.IsTransactionProfit, LLMSpec.IsUpperBoundProfit ];
    · rcases prices with ( _ | ⟨ x, _ | ⟨ y, l ⟩ ⟩ ) <;> simp_all +arith +decide [ VerinaSpec.maxProfit_postcond ];
      constructor;
      · use 0, 1 ; simp +arith +decide [ * ];
      · intro i j hij hj; rcases i with ( _ | _ | i ) <;> rcases j with ( _ | _ | j ) <;> simp_all +arith +decide;
        · convert h'.1.1.2 _ _ _ _ using 1;
          exact j + 2;
          · grind;
          · grind;
        · have := h'.1.2.1 ( l[j] ) ( j + 2 ) ; simp_all +arith +decide [ List.getElem?_eq_getElem ] ;
          grind;
        · have := List.pairwise_iff_get.mp h'.1.2.2;
          specialize this ⟨ i, by
            simp +arith +decide [ List.length_zipIdx ] ; linarith ⟩ ⟨ j, by
            simp +arith +decide [ List.length_zipIdx ] ; linarith ⟩ hij
          generalize_proofs at *;
          simp_all +decide [ List.get ];
          rwa [ List.getElem?_eq_getElem ( by linarith ) ];
    · refine' ⟨ _, _, _ ⟩;
      · rcases prices with ( _ | ⟨ p, _ | ⟨ q, l ⟩ ⟩ ) <;> simp_all +arith +decide [ VerinaSpec.maxProfit_postcond ];
      · have := h'.2.2 ( Nat.pos_of_ne_zero h ) ; simp_all +decide [ List.zipIdx ] ;
        obtain ⟨ a, b, h₁, c, d, h₂, h₃, h₄ ⟩ := this; use b, d; simp_all +decide [ List.mem_iff_get ] ;
        grind +ring;
      · intro i j hij hj; have := h'.1; simp_all +decide [ List.pairwise_iff_get ] ;
        by_cases hi : i < List.length prices <;> by_cases hj : j < List.length prices <;> simp_all +decide [ List.get ];
        · convert this ⟨ i, by simpa using hi ⟩ ⟨ j, by simpa using hj ⟩ hij using 1;
        · grind;
  · rcases h' with ( ⟨ h₁, rfl ⟩ | ⟨ h₁, ⟨ i, j, hij, hj, rfl ⟩, h₂ ⟩ ) <;> simp_all +decide [ VerinaSpec.maxProfit_postcond ];
    · rcases prices with ( _ | ⟨ x, _ | ⟨ y, l ⟩ ⟩ ) <;> simp_all +arith +decide;
    · refine' ⟨ _, _, _ ⟩;
      · rw [ List.pairwise_iff_get ];
        intro ⟨ k, hk ⟩ ⟨ l, hl ⟩ hkl hkl'; have := h₂ k l; simp_all +decide [ List.get ] ;
        grind +ring;
      · constructor <;> intro h <;> contrapose! h₂;
        · obtain ⟨ a, b, h₁, c, d, h₂, h₃, h₄ ⟩ := h₂.2; simp_all +decide [ LLMSpec.IsUpperBoundProfit ] ;
          use b, d;
          grind;
        · cases h <;> simp_all +decide [ List.mem_iff_get ];
          · linarith;
          · rename_i h; specialize h ( prices[i] ) ⟨ i, by simpa using by linarith ⟩ rfl ( prices[j] ) ⟨ j, by simpa using by linarith ⟩ rfl; simp_all +decide [ not_or, Nat.sub_eq_zero_iff_le ] ;
            grind;
      · grind
end Proof
