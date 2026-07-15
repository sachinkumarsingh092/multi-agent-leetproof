/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 0a73fc13-82ee-4c03-bab0-9533bc3da009

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (digits : String) : VerinaSpec.letterCombinations_precond digits ↔ LLMSpec.precondition digits

The following was negated by Aristotle:

- theorem postcondition_equiv (digits : String) (result : List String) : LLMSpec.precondition digits →
  (VerinaSpec.letterCombinations_postcond digits result ↔ LLMSpec.postcondition digits result)

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


namespace VerinaSpec

def digitToLetters (c : Char) : List Char :=
  match c with
  | '2' => ['a', 'b', 'c']
  | '3' => ['d', 'e', 'f']
  | '4' => ['g', 'h', 'i']
  | '5' => ['j', 'k', 'l']
  | '6' => ['m', 'n', 'o']
  | '7' => ['p', 'q', 'r', 's']
  | '8' => ['t', 'u', 'v']
  | '9' => ['w', 'x', 'y', 'z']
  | _ => []

def letterCombinations_precond (digits : String) : Prop :=
  True

def letterCombinations_postcond (digits : String) (result: List String) : Prop :=
  if digits.isEmpty then
    result = []
  else if digits.toList.any (λ c => ¬(c ∈ ['2','3','4','5','6','7','8','9'])) then
    result = []
  else
    let expected := digits.toList.map digitToLetters |>.foldl (λ acc ls => acc.flatMap (λ s => ls.map (λ c => s ++ String.singleton c)) ) [""]
    result.length = expected.length ∧ result.all (λ s => s ∈ expected) ∧ expected.all (λ s => s ∈ result)

end VerinaSpec

namespace LLMSpec

-- Helper: validity of a keypad digit character.
def validDigit (c : Char) : Bool :=
  c = '2' || c = '3' || c = '4' || c = '5' || c = '6' || c = '7' || c = '8' || c = '9'

-- Helper: keypad letter mapping.
def lettersOf (c : Char) : List Char :=
  if c = '2' then ['a', 'b', 'c'] else
  if c = '3' then ['d', 'e', 'f'] else
  if c = '4' then ['g', 'h', 'i'] else
  if c = '5' then ['j', 'k', 'l'] else
  if c = '6' then ['m', 'n', 'o'] else
  if c = '7' then ['p', 'q', 'r', 's'] else
  if c = '8' then ['t', 'u', 'v'] else
  if c = '9' then ['w', 'x', 'y', 'z'] else
  []

def allValidDigits (ds : List Char) : Bool :=
  ds.all validDigit

-- A character-list `combo` is a valid combination for `ds` iff
-- it has the same length and each position picks a letter allowed by that digit.
def isValidCombinationFor (ds : List Char) (combo : List Char) : Prop :=
  combo.length = ds.length ∧
  ∀ (i : Nat), i < ds.length → combo.get! i ∈ lettersOf (ds.get! i)

-- The function is total: it must return [] on empty/invalid input.
def precondition (digits : String) : Prop :=
  True

def postcondition (digits : String) (result : List String) : Prop :=
  let ds : List Char := digits.data
  ((ds = [] ∨ allValidDigits ds = false) → result = []) ∧
  ((ds ≠ [] ∧ allValidDigits ds = true) →
      (∀ (s : String), s ∈ result → isValidCombinationFor ds s.data) ∧
      (∀ (combo : List Char), isValidCombinationFor ds combo → (String.mk combo) ∈ result) ∧
      result.Nodup ∧
      result.Sorted (fun a b => a ≤ b))

end LLMSpec

section Proof

theorem precondition_equiv (digits : String) : VerinaSpec.letterCombinations_precond digits ↔ LLMSpec.precondition digits := by
  -- Since both preconditions are True, their equivalence is trivial.
  simp [VerinaSpec.letterCombinations_precond, LLMSpec.precondition]

/- Aristotle found this block to be false. Here is a proof of the negation:

noncomputable section AristotleLemmas

def verina_combinations (dss : List (List Char)) : List String :=
  dss.foldl (λ acc ls => acc.flatMap (λ s => ls.map (λ c => s ++ String.singleton c))) [""]

theorem verina_combinations_step (dss : List (List Char)) (ls : List Char) :
  verina_combinations (dss ++ [ls]) = (verina_combinations dss).flatMap (λ s => ls.map (λ c => s ++ String.singleton c)) := by
    -- By definition of `verina_combinations`, we can rewrite the left-hand side of the equation.
    simp [verina_combinations]

theorem verina_combinations_mem (dss : List (List Char)) (s : String) :
  s ∈ verina_combinations dss ↔ s.length = dss.length ∧ ∀ (i : Nat), i < dss.length → s.data.get! i ∈ dss.get! i := by
    induction' dss using List.reverseRecOn with dss ih generalizing s <;> simp_all +decide [ verina_combinations ];
    · -- The length of the empty string is zero, and if the length of a string is zero, then the string must be empty.
      simp [String.length];
      exact ⟨ fun h => h ▸ rfl, fun h => String.ext h ⟩;
    · constructor <;> intro h;
      · obtain ⟨ a, ha, b, hb, rfl ⟩ := h; simp_all +decide [ List.getElem_append ] ;
        cases a ; aesop;
      · -- Let's split the string s into the first part (the first dss.length characters) and the last character.
        obtain ⟨a, c, ha⟩ : ∃ a : String, ∃ c : Char, s = a ++ String.singleton c ∧ a.length = dss.length := by
          use String.mk (List.take dss.length s.data), s.data.get! dss.length;
          -- The length of the string s is indeed dss.length + 1.
          have h_len : s.data.length = dss.length + 1 := by
            exact h.1;
          rw [ String.ext_iff ] ; aesop;
        use a, by
          simp_all +decide [ String.ext_iff ];
          intro i hi; specialize h i ( Nat.lt_succ_of_lt hi ) ; simp_all +decide [ List.getElem?_append ] ;
          split_ifs at h <;> simp_all +decide [ String.length ], c, by
          -- Since $i = dss.length$, we have $i < dss.length + 1$, so we can apply the hypothesis $h$.
          have h_last : s.data[dss.length]?.getD 'A' ∈ (dss ++ [ih])[dss.length] := by
            exact h.2 _ ( Nat.lt_succ_self _ );
          simp_all +decide [ String.length ], by
          rw [ha.left]

theorem string_append_lt_of_lt_same_length (s1 s2 : String) (c1 c2 : Char) :
  s1.length = s2.length → s1 < s2 → s1 ++ String.singleton c1 < s2 ++ String.singleton c2 := by
    intros h1 h2
    have h_prefix : s1 < s2 → s1 ++ String.singleton c1 < s2 ++ String.singleton c2 := by
      intro h2
      have h_prefix : s1 ++ String.singleton c1 < s2 ++ String.singleton c2 := by
        have h_lex : ∀ (s1 s2 : List Char), s1.length = s2.length → s1 < s2 → s1 ++ [c1] < s2 ++ [c2] := by
          intros s1 s2 h1 h2
          induction' s1 with s1_head s1_tail s1_ih generalizing s2 <;> induction' s2 with s2_head s2_tail s2_ih <;> simp_all +decide [ List.append ];
          cases h2 <;> simp_all +decide [ List.cons_lt_cons_iff ]
        exact?
      exact h_prefix
    exact h_prefix h2

theorem string_append_le_of_le (s : String) (c1 c2 : Char) :
  c1 ≤ c2 → s ++ String.singleton c1 ≤ s ++ String.singleton c2 := by
    -- Since the first part is the same, the comparison will be based on the last character.
    have h_lex : ∀ (s : String) (c1 c2 : Char), c1 ≤ c2 → s ++ String.singleton c1 ≤ s ++ String.singleton c2 := by
      intros s c1 c2 hc
      by_cases h_eq : c1 = c2;
      · -- If c1 equals c2, then the strings s ++ String.singleton c1 and s ++ String.singleton c2 are identical, so the inequality holds trivially.
        simp [h_eq];
      · -- Since the lists are compared element-wise and the first difference is where c1 is less than c2, the entire list after s is less than the other list.
        have h_lex : List.Lex (· < ·) (s.data ++ [c1]) (s.data ++ [c2]) := by
          have h_first_diff : ∃ i, i < s.length + 1 ∧ (s.data ++ [c1]).get! i < (s.data ++ [c2]).get! i := by
            use s.length; simp [h_eq];
            simp +decide [ List.getElem?_append, h_eq ];
            split_ifs <;> simp_all +decide [ String.length ];
            exact?
          obtain ⟨ i, hi, hi' ⟩ := h_first_diff;
          have h_lex : ∀ (l1 l2 : List Char), l1.length = l2.length → (∃ i, i < l1.length ∧ l1.get! i < l2.get! i ∧ ∀ j < i, l1.get! j = l2.get! j) → List.Lex (· < ·) l1 l2 := by
            intros l1 l2 h_len h_diff
            induction' l1 with a l1 ih generalizing l2;
            · cases l2 <;> trivial;
            · rcases l2 with ( _ | ⟨ b, l2 ⟩ ) <;> simp_all +decide;
              rcases h_diff with ⟨ i, hi, hi', hi'' ⟩ ; rcases i with ( _ | i ) <;> simp_all +decide [ List.get ] ;
              · exact List.Lex.rel hi';
              · -- Since $a = b$, the lists $a :: l1$ and $b :: l2$ are equal in the first element, and the rest of the lists are $l1$ and $l2$, which are less than each other by the induction hypothesis.
                have h_eq : a = b := by
                  simpa using hi'' 0 ( Nat.zero_lt_succ _ );
                -- Since $a = b$, the lists $a :: l1$ and $b :: l2$ are equal in the first element, and the rest of the lists are $l1$ and $l2$, which are less than each other by the induction hypothesis. Therefore, $a :: l1 < b :: l2$.
                have h_lex : l1 < l2 := by
                  exact ih l2 rfl i hi hi' fun j hj => by simpa [ h_eq ] using hi'' ( j + 1 ) ( by linarith ) ;
                exact h_eq.symm ▸ List.Lex.cons h_lex;
          apply h_lex;
          · simp +arith +decide;
          · use i;
            -- Since $j < i$ and $i < s.length + 1$, we have $j < s.length$. Therefore, the $j$-th element of $s.data ++ [c1]$ is the same as the $j$-th element of $s.data ++ [c2]$.
            have h_eq : ∀ j < i, j < s.length := by
              exact fun j hj => by linarith;
            simp_all +decide [ List.getElem?_append, Nat.lt_succ_iff ];
            exact ⟨ by simpa using hi, fun j hj => by rw [ if_pos ( by simpa using h_eq j hj ), if_pos ( by simpa using h_eq j hj ) ] ⟩;
        exact?;
    exact h_lex s c1 c2

theorem sorted_map_append (s : String) (chars : List Char) :
  chars.Sorted (·≤·) → (chars.map (λ c => s ++ String.singleton c)).Sorted (·≤·) := by
    intro h_sorted_chars;
    induction chars <;> simp_all +decide [ List.Sorted ];
    intro a ha; exact (by
    apply_rules [ string_append_le_of_le ];
    exact h_sorted_chars.1 a ha)

theorem sorted_flatMap_step (l : List String) (chars : List Char) (n : Nat) :
  l.Sorted (·≤·) → l.Nodup → chars.Sorted (·≤·) → (∀ s ∈ l, s.length = n) →
  (l.flatMap (λ s => chars.map (λ c => s ++ String.singleton c))).Sorted (·≤·) := by
    intros hl hl_nodup hchars hlen
    induction' l with s l ih generalizing n;
    · simp [List.Sorted];
    · have h_merge : List.Sorted (· ≤ ·) (List.map (fun c => s ++ String.singleton c) chars) ∧ List.Sorted (· ≤ ·) (List.flatMap (fun s => List.map (fun c => s ++ String.singleton c) chars) l) ∧ ∀ x ∈ List.map (fun c => s ++ String.singleton c) chars, ∀ y ∈ List.flatMap (fun s => List.map (fun c => s ++ String.singleton c) chars) l, x ≤ y := by
        refine' ⟨ _, _, _ ⟩;
        · exact?;
        · exact ih n ( List.sorted_cons.mp hl |>.2 ) ( List.nodup_cons.mp hl_nodup |>.2 ) fun s hs => hlen s ( List.mem_cons_of_mem _ hs );
        · -- Since $s$ is less than or equal to any element in $l$, and the lengths of $s$ and $l$ are the same, appending the same character to both will preserve the inequality.
          intros x hx y hy
          obtain ⟨c, hc⟩ : ∃ c, x = s ++ String.singleton c := by
            rw [ List.mem_map ] at hx; obtain ⟨ c, hc, rfl ⟩ := hx; exact ⟨ c, rfl ⟩ ;
          obtain ⟨s', hs', c', hc'⟩ : ∃ s' ∈ l, ∃ c', y = s' ++ String.singleton c' := by
            grind
          have h_le : s ≤ s' := by
            have := List.pairwise_cons.mp hl; aesop;
          have h_append : s ++ String.singleton c ≤ s' ++ String.singleton c' := by
            by_cases h_eq : s = s';
            · grind;
            · have h_append : s ++ String.singleton c < s' ++ String.singleton c' := by
                apply string_append_lt_of_lt_same_length;
                · rw [ hlen s ( by simp +decide ), hlen s' ( by simp +decide [ hs' ] ) ];
                · exact?;
              exact?
          aesop;
      rw [ List.Sorted ] at *;
      grind

theorem sorted_flatMap_step_v2 (l : List String) (chars : List Char) (n : Nat) :
  l.Sorted (·≤·) → l.Nodup → chars.Sorted (·≤·) → (∀ s ∈ l, s.length = n) →
  (l.flatMap (λ s => chars.map (λ c => s ++ String.singleton c))).Sorted (·≤·) := by
    apply_rules [ sorted_flatMap_step ]

theorem verina_combinations_sorted (dss : List (List Char)) :
  (∀ ds ∈ dss, ds.Sorted (·≤·)) → (∀ ds ∈ dss, ds.Nodup) → (verina_combinations dss).Sorted (·≤·) := by
    intro h1 h2;
    induction' dss using List.reverseRecOn with dss ih;
    · native_decide +revert;
    · rw [ verina_combinations_step ];
      apply sorted_flatMap_step;
      any_goals exact dss.length;
      · aesop;
      · have h_nodup : ∀ (dss : List (List Char)), (∀ ds ∈ dss, ds.Nodup) → List.Nodup (verina_combinations dss) := by
          intro dss hdss; induction' dss using List.reverseRecOn with dss ih <;> simp_all +decide [ verina_combinations_step ] ;
          rw [ List.nodup_flatMap ];
          simp_all +decide [ List.nodup_map_iff_inj_on, List.pairwise_map ];
          constructor;
          · simp +contextual [ String.ext_iff ];
          · rw [ List.pairwise_iff_get ];
            intro i j hij; simp +decide [ List.disjoint_left ] ;
            intro a ha x hx; intro H; have := congr_arg String.length H; simp +decide at this;
            have h_eq : (verina_combinations dss)[(j : ℕ)] = (verina_combinations dss)[(i : ℕ)] := by
              rw [ String.ext_iff ] at H;
              exact String.ext <| by simpa [ this ] using congr_arg ( fun s => s.dropLast ) H;
            exact absurd ( List.nodup_iff_injective_get.mp ‹_› h_eq ) ( ne_of_gt hij );
        exact h_nodup dss fun ds hds => h2 ds <| List.mem_append_left _ hds;
      · exact h1 _ ( List.mem_append_right _ ( List.mem_singleton_self _ ) );
      · intro s hs; rw [ verina_combinations_mem ] at hs; aesop;

theorem nodup_flatMap_step (l : List String) (chars : List Char) (n : Nat) :
  l.Nodup → chars.Nodup → (∀ s ∈ l, s.length = n) →
  (l.flatMap (λ s => chars.map (λ c => s ++ String.singleton c))).Nodup := by
    intros hl hchars hn
    have h_disjoint : ∀ s1 s2 : String, s1 ∈ l → s2 ∈ l → s1 ≠ s2 → Disjoint (chars.map (fun c => s1 ++ String.singleton c)).toFinset (chars.map (fun c => s2 ++ String.singleton c)).toFinset := by
      intros s1 s2 hs1 hs2 hne; simp_all +decide [ Finset.disjoint_left ] ;
      intro a ha b hb; intro H; have := congr_arg String.data H; simp_all +decide [ String.ext_iff ] ;
      replace this := congr_arg ( fun x => x.dropLast ) this ; simp_all +decide [ List.dropLast ] ;
    rw [ List.nodup_flatMap ];
    refine' ⟨ _, List.Pairwise.imp_of_mem _ hl ⟩;
    · intros s hs; exact List.Nodup.map (fun c1 c2 h => by
        replace h := congr_arg String.data h ; aesop) hchars;
    · simp_all +decide [ Finset.disjoint_left, List.disjoint_left ]

theorem verina_combinations_nodup (dss : List (List Char)) :
  (∀ ds ∈ dss, ds.Nodup) → (verina_combinations dss).Nodup := by
    induction' dss using List.reverseRecOn with dss ih;
    · decide +revert;
    · -- By definition of `verina_combinations`, we have:
      have h_combinations : verina_combinations (dss ++ [ih]) = (verina_combinations dss).flatMap (fun s => ih.map (fun c => s ++ String.singleton c)) := by
        exact?;
      intro h; rw [ h_combinations ] ; apply_rules [ nodup_flatMap_step ] ; aesop;
      exact List.mem_append_right _ ( List.mem_singleton_self _ );
      exact fun s hs => by rw [ verina_combinations_mem ] at hs; exact hs.1;

theorem verina_combinations_sorted_v2 (dss : List (List Char)) :
  (∀ ds ∈ dss, ds.Sorted (·≤·)) → (∀ ds ∈ dss, ds.Nodup) → (verina_combinations dss).Sorted (·≤·) := by
    exact?

theorem digitToLetters_sorted_nodup (c : Char) :
  (VerinaSpec.digitToLetters c).Sorted (·≤·) ∧ (VerinaSpec.digitToLetters c).Nodup := by
    unfold VerinaSpec.digitToLetters; aesop;

theorem digitToLetters_eq_lettersOf (c : Char) : VerinaSpec.digitToLetters c = LLMSpec.lettersOf c := by
  unfold VerinaSpec.digitToLetters LLMSpec.lettersOf; aesop;

theorem postcondition_equiv_false : ¬ (∀ (digits : String) (result : List String), LLMSpec.precondition digits → (VerinaSpec.letterCombinations_postcond digits result ↔ LLMSpec.postcondition digits result)) := by
  push_neg;
  use "2";
  use [ "c", "b", "a" ];
  unfold VerinaSpec.letterCombinations_postcond LLMSpec.postcondition; simp +decide ;
  exact?

end AristotleLemmas

theorem postcondition_equiv (digits : String) (result : List String) : LLMSpec.precondition digits →
  (VerinaSpec.letterCombinations_postcond digits result ↔ LLMSpec.postcondition digits result) := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Prove that the postpersonal holding condition is always false.
  simp [LLMSpec.precondition] at *;
  unfold VerinaSpec.letterCombinations_postcond LLMSpec.postcondition;
  use "2";
  use [ "c", "b", "a" ] ; simp +decide ;

-/
theorem postcondition_equiv (digits : String) (result : List String) : LLMSpec.precondition digits →
  (VerinaSpec.letterCombinations_postcond digits result ↔ LLMSpec.postcondition digits result) := by
  sorry

end Proof