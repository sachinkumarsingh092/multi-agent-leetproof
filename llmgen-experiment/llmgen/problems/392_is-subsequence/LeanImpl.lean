import Lean
import Mathlib.Tactic
import Velvet.Std
import Extensions.VelvetPBT

set_option maxHeartbeats 10000000

section Specs
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false
set_option pp.funBinderTypes true

/- Problem Description
    392. Is Subsequence: decide whether s is a subsequence of t.
    **Important: complexity should be O(n) time and O(1) space**
    Natural language breakdown:
    1. Inputs are two sequences of characters s and t.
    2. s is a subsequence of t if we can delete zero or more characters from t and obtain exactly s.
    3. Deletions may be none; the relative order of the remaining characters must be preserved.
    4. The output is true exactly when s is a subsequence of t, and false otherwise.
    5. The empty sequence is a subsequence of any sequence.
    6. If s is longer than t, then s cannot be a subsequence of t.
-/

-- We define the subsequence relation via an order-preserving index embedding.
-- This avoids relying on a particular library name for subsequence.
--
-- `subseqByIndex s t` means: there exists a (partial) index map f from indices of `s`
-- into indices of `t` such that:
--  * f maps valid indices of s to valid indices of t
--  * f is strictly increasing on indices < s.length
--  * each character of s matches the character of t at the mapped index

def subseqByIndex (s : List Char) (t : List Char) : Prop :=
  ∃ f : Nat → Nat,
    (∀ i : Nat, i < s.length → f i < t.length) ∧
    StrictMonoOn f (Set.Iio s.length) ∧
    (∀ i : Nat, i < s.length → s.get! i = t.get! (f i))

def precondition (s : List Char) (t : List Char) : Prop :=
  True

def postcondition (s : List Char) (t : List Char) (result : Bool) : Prop :=
  (result = true ↔ subseqByIndex s t)
end Specs

section Impl
def implementation (s : List Char) (t : List Char) : Bool :=
  match s, t with
  | [], _ => true
  | _ :: _, [] => false
  | sc :: ss, tc :: ts =>
    if sc == tc then implementation ss ts
    else implementation (sc :: ss) ts
end Impl

section TestCases
-- Test case 1: Example 1
-- s = "abc", t = "ahbgdc" => true

def test1_s : List Char := ['a', 'b', 'c']
def test1_t : List Char := ['a', 'h', 'b', 'g', 'd', 'c']
def test1_Expected : Bool := true

-- Test case 2: Example 2
-- s = "axc", t = "ahbgdc" => false

def test2_s : List Char := ['a', 'x', 'c']
def test2_t : List Char := ['a', 'h', 'b', 'g', 'd', 'c']
def test2_Expected : Bool := false

-- Test case 3: Empty s is a subsequence of any t

def test3_s : List Char := []
def test3_t : List Char := ['z', 'y']
def test3_Expected : Bool := true

-- Test case 4: Non-empty s cannot be subsequence of empty t

def test4_s : List Char := ['a']
def test4_t : List Char := []
def test4_Expected : Bool := false

-- Test case 5: s equals t

def test5_s : List Char := ['l', 'e', 'a', 'n']
def test5_t : List Char := ['l', 'e', 'a', 'n']
def test5_Expected : Bool := true

-- Test case 6: Single character present later in t

def test6_s : List Char := ['c']
def test6_t : List Char := ['a', 'b', 'c']
def test6_Expected : Bool := true

-- Test case 7: Single character absent from t

def test7_s : List Char := ['x']
def test7_t : List Char := ['a', 'b', 'c']
def test7_Expected : Bool := false

-- Test case 8: Repeated characters succeed when enough occurrences exist
-- s = "aa" is subsequence of "abca" (use positions 0 and 3)

def test8_s : List Char := ['a', 'a']
def test8_t : List Char := ['a', 'b', 'c', 'a']
def test8_Expected : Bool := true

-- Test case 9: Repeated characters fail when not enough occurrences exist

def test9_s : List Char := ['a', 'a', 'a']
def test9_t : List Char := ['a', 'a']
def test9_Expected : Bool := false

-- Recommend to validate: empty-s behavior, repeated-character behavior, order-preservation
end TestCases

section Assertions
-- Test case 1
#assert_same_evaluation #[(implementation test1_s test1_t), test1_Expected]

-- Test case 2
#assert_same_evaluation #[(implementation test2_s test2_t), test2_Expected]

-- Test case 3
#assert_same_evaluation #[(implementation test3_s test3_t), test3_Expected]

-- Test case 4
#assert_same_evaluation #[(implementation test4_s test4_t), test4_Expected]

-- Test case 5
#assert_same_evaluation #[(implementation test5_s test5_t), test5_Expected]

-- Test case 6
#assert_same_evaluation #[(implementation test6_s test6_t), test6_Expected]

-- Test case 7
#assert_same_evaluation #[(implementation test7_s test7_t), test7_Expected]

-- Test case 8
#assert_same_evaluation #[(implementation test8_s test8_t), test8_Expected]

-- Test case 9
#assert_same_evaluation #[(implementation test9_s test9_t), test9_Expected]
end Assertions

section Pbt
method implementationPbt (s : List Char) (t : List Char)
  return (result : Bool)
  require precondition s t
  ensures postcondition s t result
  do
  return (implementation s t)

velvet_plausible_test implementationPbt (config := { maxMs := some 20000 })
end Pbt

section Proof
theorem correctness_goal_0_0
    (s : List Char)
    (t : List Char)
    : ∀ (s t : List Char), implementation s t = true ↔ s.Sublist t := by
    intro s t
    suffices h : implementation s t = s.isSublist t by
      rw [h]
      exact List.isSublist_iff_sublist
    induction s, t using implementation.induct with
    | case1 t => simp [implementation, List.isSublist]
    | case2 sc ss => simp [implementation, List.isSublist]
    | case3 sc ss tc ts h ih => simp [implementation, List.isSublist, h, ih]
    | case4 sc ss tc ts h ih => simp [implementation, List.isSublist, h, ih]

lemma list_get!_eq_getElem {l : List Char} {i : Nat} (h : i < l.length) : l.get! i = l[i] := by
  simp [List.get!_eq_getElem!]
  rw [List.getElem?_eq_getElem h]
  simp


theorem correctness_goal_0_1
    (s : List Char)
    (t : List Char)
    : ∀ (s t : List Char), s.Sublist t ↔ subseqByIndex s t := by
    intro s' t'
    rw [List.sublist_iff_exists_fin_orderEmbedding_get_eq]
    unfold subseqByIndex
    constructor
    · -- Forward: Fin order embedding → Nat function
      rintro ⟨f, hf⟩
      refine ⟨fun i => if h : i < s'.length then (f ⟨i, h⟩).val else 0, ?_, ?_, ?_⟩
      · intro i hi; simp [hi]
      · intro i (hi : i < s'.length) j (hj : j < s'.length) hij
        simp only [hi, hj, dite_true]
        exact f.strictMono (show (⟨i, hi⟩ : Fin s'.length) < ⟨j, hj⟩ from hij)
      · intro i hi
        simp only [hi, dite_true]
        have h1 := hf ⟨i, hi⟩
        rw [List.get_eq_getElem, List.get_eq_getElem] at h1
        rw [list_get!_eq_getElem hi, list_get!_eq_getElem (f ⟨i, hi⟩).isLt]
        exact h1
    · -- Backward: Nat function → Fin order embedding
      rintro ⟨g, hbound, hstrict, hchar⟩
      let f : Fin s'.length → Fin t'.length := fun ⟨i, hi⟩ => ⟨g i, hbound i hi⟩
      have hf_strict : StrictMono f := by
        intro ⟨i, hi⟩ ⟨j, hj⟩ hij
        exact hstrict (Set.mem_Iio.mpr hi) (Set.mem_Iio.mpr hj) hij
      refine ⟨OrderEmbedding.ofStrictMono f hf_strict, ?_⟩
      intro ⟨i, hi⟩
      have h1 := hchar i hi
      rw [list_get!_eq_getElem hi, list_get!_eq_getElem (hbound i hi)] at h1
      show s'.get ⟨i, hi⟩ = t'.get (OrderEmbedding.ofStrictMono f hf_strict ⟨i, hi⟩)
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [OrderEmbedding.coe_ofStrictMono]
      exact h1

theorem correctness_goal_0
    (s : List Char)
    (t : List Char)
    : ∀ (s t : List Char), implementation s t = true ↔ subseqByIndex s t := by
    have h_impl_sublist : ∀ (s t : List Char), implementation s t = true ↔ List.Sublist s t := by expose_names; exact (correctness_goal_0_0 s t)
    have h_sublist_subseq : ∀ (s t : List Char), List.Sublist s t ↔ subseqByIndex s t := by expose_names; exact (correctness_goal_0_1 s t)
    intro s' t'
    rw [h_impl_sublist, h_sublist_subseq]

theorem correctness_goal
    (s : List Char)
    (t : List Char)
    : postcondition s t (implementation s t) := by
    have h_main : ∀ (s t : List Char), implementation s t = true ↔ subseqByIndex s t := by expose_names; exact (correctness_goal_0 s t)
    unfold postcondition
    exact h_main s t
end Proof
