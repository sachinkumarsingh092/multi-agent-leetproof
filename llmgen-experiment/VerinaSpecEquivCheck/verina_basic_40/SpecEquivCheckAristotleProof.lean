/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 176c8ec4-2c53-4360-9d73-5d0371e7d56f

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (s : Array Int) : VerinaSpec.secondSmallest_precond s ↔ LLMSpec.precondition s

- theorem postcondition_equiv (s : Array Int) (result : Int) : LLMSpec.precondition s →
  (VerinaSpec.secondSmallest_postcond s result ↔ LLMSpec.postcondition s result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def secondSmallest_precond (s : Array Int) : Prop :=
  s.size > 1 ∧ ∃ i j, i < s.size ∧ j < s.size ∧ s[i]! ≠ s[j]!

-- at least two distinct values

def minListHelper : List Int → Int
| [] => panic! "minListHelper: empty list"
| [_] => panic! "minListHelper: singleton list"
| a :: b :: [] => if a ≤ b then a else b
| a :: b :: c :: xs =>
    let m := minListHelper (b :: c :: xs)
    if a ≤ m then a else m

def minList (l : List Int) : Int :=
  minListHelper l

def secondSmallestAux (s : Array Int) (i minIdx secondIdx : Nat) : Int :=
  if i ≥ s.size then
    s[secondIdx]!
  else
    let x    := s[i]!
    let m    := s[minIdx]!
    let smin := s[secondIdx]!
    if x < m then
      secondSmallestAux s (i + 1) i minIdx
    else if x < smin then
      secondSmallestAux s (i + 1) minIdx i
    else
      secondSmallestAux s (i + 1) minIdx secondIdx
termination_by s.size - i

def secondSmallest_postcond (s : Array Int) (result: Int) :=
  (∃ i, i < s.size ∧ s[i]! = result) ∧
  (∃ j, j < s.size ∧ s[j]! < result ∧
    ∀ k, k < s.size → s[k]! ≠ s[j]! → s[k]! ≥ result)

end VerinaSpec

namespace LLMSpec

-- Membership predicate for arrays, phrased using Nat indices (preferred for specs).
def InArray (s : Array Int) (x : Int) : Prop :=
  ∃ (i : Nat), i < s.size ∧ s[i]! = x

-- At least two distinct elements occur in the array.
def HasTwoDistinct (s : Array Int) : Prop :=
  ∃ (i : Nat) (j : Nat),
    i < s.size ∧ j < s.size ∧ s[i]! ≠ s[j]!

-- Preconditions: size ≥ 2 and at least two distinct values.
def precondition (s : Array Int) : Prop :=
  s.size ≥ 2 ∧ HasTwoDistinct s

-- Postcondition: result is the least element strictly greater than the minimum element of s.
def postcondition (s : Array Int) (result : Int) : Prop :=
  ∃ (m : Int),
    s.min? = some m ∧
    InArray s m ∧
    (∀ (x : Int), InArray s x → m ≤ x) ∧
    InArray s result ∧
    m < result ∧
    (∀ (x : Int), InArray s x → m < x → result ≤ x)

end LLMSpec

section Proof

theorem precondition_equiv (s : Array Int) : VerinaSpec.secondSmallest_precond s ↔ LLMSpec.precondition s := by
  -- The preconditions for VerinaSpec and LLMSpec are equivalent because they both require the array to have at least two elements and at least two distinct values.
  simp [VerinaSpec.secondSmallest_precond, LLMSpec.precondition];
  -- The preconditions for VerinaSpec and LLMSpec are equivalent because they both require the array to have at least two elements and at least two distinct values. The definitions are identical.
  simp [LLMSpec.HasTwoDistinct];
  -- The equivalence is trivially true since 1 < s.size is equivalent to 2 ≤ s.size.
  intros x hx x_1 hx_1 hne
  exact ⟨fun h => by linarith, fun h => by linarith⟩

noncomputable section AristotleLemmas

/-
Relate LLMSpec.InArray to List membership.
-/
theorem InArray_iff_mem_toList (s : Array Int) (x : Int) : LLMSpec.InArray s x ↔ x ∈ s.toList := by
  constructor <;> intro h;
  · obtain ⟨ i, hi, hx ⟩ := h;
    cases s ; aesop;
  · obtain ⟨ i, hi ⟩ := List.mem_iff_get.mp h; use i; aesop;

/-
Characterization of List.min? for Int lists.
-/
theorem List_min?_eq_some_iff (l : List Int) (m : Int) : l.min? = some m ↔ (m ∈ l ∧ ∀ x ∈ l, m ≤ x) := by
  -- We'll use induction on the list `l`.
  induction' l with a l ih generalizing m;
  · aesop;
  · cases h : List.min? l <;> simp +decide [ * ];
    · cases l <;> aesop;
    · grind

/-
Equivalence of Array.min? and List.min? for Int arrays.
-/
theorem Array_min?_eq_List_min? (s : Array Int) : s.min? = s.toList.min? := by
  unfold Array.min?;
  split_ifs <;> simp_all +decide [ Array.minD ];
  -- By definition of `minWith`, we can express it in terms of the foldl operation.
  have h_minWith_foldl : ∀ (l : List ℤ), l ≠ [] → List.min? l = List.foldl (fun acc x => if x < acc then x else acc) (l.head!) (l.tail) := by
    intro l hl; induction l <;> simp_all +decide [ List.min? ] ;
    congr! 1;
    exact funext fun x => funext fun y => by cases min_cases x y <;> split_ifs <;> linarith;
  -- By induction on the array's size, we can show that the foldl operation on the array's elements is equal to the foldl operation on the list of elements.
  have h_ind : ∀ (s : Array ℤ) (i : ℕ) (acc : ℤ), i ≤ s.size → Array.foldl (fun acc x => if x < acc then x else acc) acc s i = List.foldl (fun acc x => if x < acc then x else acc) acc (s.toList.drop i) := by
    intros s i acc hi
    induction' h : s.size - i with k hk generalizing i acc;
    · simp_all +decide [ Nat.sub_eq_iff_eq_add hi ];
      rw [ Array.foldl ];
      rw [ Array.foldlM ];
      simp +decide [ h, Array.foldlM.loop ];
      rw [ List.drop_eq_nil_of_le ] <;> aesop;
    · rw [ Array.foldl ];
      simp +decide [ Array.foldlM ];
      rw [ Array.foldlM.loop ];
      split_ifs <;> simp_all +decide [ Nat.sub_succ ];
      convert hk ( i + 1 ) ( if s[i] < acc then s[i] else acc ) ( by omega ) ( by omega ) using 1;
      · rw [ Array.foldl ];
        rw [ Array.foldlM ];
        grind;
      · rw [ List.drop_eq_getElem_cons ];
        grind;
        simpa;
  rcases n : s.toList with ( _ | ⟨ x, _ | ⟨ y, l ⟩ ⟩ ) <;> simp_all +decide [ Array.minWith ];
  · aesop;
  · rcases s with ⟨ ⟨ l ⟩ ⟩ <;> aesop;
  · convert h_ind s 1 ( s[0] ) ( by linarith ) using 1;
    · simp +decide [ Ord.compare ];
    · rcases s with ⟨ ⟨ l ⟩ ⟩ <;> aesop

/-
Characterization of Array.min? for Int arrays.
-/
theorem min_eq_some_iff (s : Array Int) (m : Int) :
  s.min? = some m ↔ (∃ i : Nat, i < s.size ∧ s[i]! = m) ∧ (∀ i : Nat, i < s.size → s[i]! ≥ m) := by
    convert List_min?_eq_some_iff s.toList m using 1;
    · rw [ Array_min?_eq_List_min? ];
    · constructor <;> intro h <;> simp_all +decide [ List.mem_iff_get ];
      · -- Since $i < s.size$, we can convert it to a `Fin s.size` element.
        obtain ⟨i, hi₁, hi₂⟩ := h.left;
        use ⟨i, hi₁⟩;
        aesop;
      · exact ⟨ by obtain ⟨ n, hn ⟩ := h.1; exact ⟨ n, n.2, by simpa [ Fin.cast_val_eq_self ] using hn ⟩, fun i hi => by simpa [ Fin.cast_val_eq_self ] using h.2 ⟨ i, hi ⟩ ⟩

end AristotleLemmas

theorem postcondition_equiv (s : Array Int) (result : Int) : LLMSpec.precondition s →
  (VerinaSpec.secondSmallest_postcond s result ↔ LLMSpec.postcondition s result) := by
  intro h_pre;
  constructor <;> intro h;
  · obtain ⟨ i, hi, hi' ⟩ := h.1
    obtain ⟨ j, hj, hj' ⟩ := h.2
    use s[j]!;
    refine' ⟨ _, _, _, _, hj'.1, _ ⟩;
    · rw [ min_eq_some_iff ];
      grind;
    · exact ⟨ j, hj, rfl ⟩;
    · rintro x ⟨ k, hk, rfl ⟩ ; exact if hk' : s[k]! = s[j]! then hk'.symm ▸ le_rfl else hj'.2 k hk hk' |> le_trans ( le_of_lt hj'.1 ) ;
    · exact ⟨ i, hi, hi' ⟩;
    · rintro x ⟨ k, hk, rfl ⟩ hk' ; cases eq_or_ne ( s[k]! ) ( s[j]! ) <;> aesop;
  · obtain ⟨ m, hm₁, hm₂, hm₃, hm₄, hm₅, hm₆ ⟩ := h;
    constructor;
    · exact?;
    · obtain ⟨ j, hj₁, hj₂ ⟩ := hm₂;
      exact ⟨ j, hj₁, by linarith, fun k hk₁ hk₂ => hm₆ _ ( by exact ⟨ k, hk₁, rfl ⟩ ) ( lt_of_le_of_ne ( hm₃ _ ( by exact ⟨ k, hk₁, rfl ⟩ ) ) ( Ne.symm <| by aesop ) ) ⟩

end Proof