import Velvet.Std
import Extensions.Tactics
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false
set_option pp.funBinderTypes true
set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

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

section Specs
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
method IsSubsequence (s : List Char) (t : List Char)
  return (result : Bool)
  require precondition s t
  ensures postcondition s t result
  do
  let sArr : Array Char := s.toArray
  let tArr : Array Char := t.toArray
  let mut si := 0
  let mut ti := 0
  while si < sArr.size ∧ ti < tArr.size
    -- Bound on si: si stays within array bounds
    -- Init: si=0 ≤ size. Pres: si increments only when si < size. Suff: needed for indexing.
    invariant "si_bound" si ≤ sArr.size
    -- Bound on ti: ti stays within array bounds
    -- Init: ti=0 ≤ size. Pres: ti increments only when ti < size. Suff: needed for indexing.
    invariant "ti_bound" ti ≤ tArr.size
    -- Array sizes equal list lengths (structural invariant)
    invariant "sArr_size" sArr.size = s.length
    invariant "tArr_size" tArr.size = t.length
    -- Forward direction: the first si characters of s form a subsequence of the first ti characters of t
    -- Init: take 0 = [], subseqByIndex [] _ holds trivially (empty embedding).
    -- Pres: on match, extending embedding; on no-match, take (ti+1) still contains old subseq.
    -- Suff: when si=sArr.size, take si s = s, and take ti t is prefix of t, so subseqByIndex s t.
    invariant "partial_subseq" subseqByIndex (List.take si s) (List.take ti t)
    -- Backward direction (greedy stays ahead): if s is a subseq of t, then s[si..] is a subseq of t[ti..]
    -- Init: drop 0 = full list, so trivially holds.
    -- Pres: greedy choice is optimal—matching when possible or skipping non-matches preserves property.
    -- Suff: when loop exits with si < sArr.size and ti = tArr.size, drop si s is non-empty but
    --        drop ti t is empty, contradicting subseqByIndex s t, so result=false is correct.
    invariant "greedy_ahead" (subseqByIndex s t → subseqByIndex (List.drop si s) (List.drop ti t))
    -- Decreasing: ti increases each iteration, so tArr.size - ti decreases
    decreasing tArr.size - ti
  do
    if sArr[si]! = tArr[ti]! then
      si := si + 1
      ti := ti + 1
    else
      ti := ti + 1
  return (si == sArr.size)
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

#assert_same_evaluation #[((IsSubsequence test1_s test1_t).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((IsSubsequence test2_s test2_t).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((IsSubsequence test3_s test3_t).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((IsSubsequence test4_s test4_t).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((IsSubsequence test5_s test5_t).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((IsSubsequence test6_s test6_t).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((IsSubsequence test7_s test7_t).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((IsSubsequence test8_s test8_t).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((IsSubsequence test9_s test9_t).run), DivM.res test9_Expected ]
end Assertions

section Pbt
velvet_plausible_test IsSubsequence (config := { maxMs := some 20000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000

theorem goal_0
    (s : List Char)
    (t : List Char)
    (si : ℕ)
    (ti : ℕ)
    (invariant_partial_subseq : ∃ (f : ℕ → ℕ), (∀ i < si, i < s.length → f i < ti ∧ f i < t.length) ∧ StrictMonoOn f (Set.Iio (min si s.length)) ∧ ∀ i < si, i < s.length → (List.take si s)[i]?.getD 'A' = (List.take ti t)[f i]?.getD 'A')
    (a : si < s.length)
    (a_1 : ti < t.length)
    (if_pos : s[si]?.getD 'A' = t[ti]?.getD 'A')
    : ∃ (f : ℕ → ℕ), (∀ i < si + OfNat.ofNat 1, i < s.length → f i < ti + OfNat.ofNat 1 ∧ f i < t.length) ∧ StrictMonoOn f (Set.Iio (min (si + OfNat.ofNat 1) s.length)) ∧ ∀ i < si + OfNat.ofNat 1, i < s.length → (List.take (si + OfNat.ofNat 1) s)[i]?.getD 'A' = (List.take (ti + OfNat.ofNat 1) t)[f i]?.getD 'A' := by
    obtain ⟨f, hf_bound, hf_mono, hf_match⟩ := invariant_partial_subseq
    have hmin_si : min si s.length = si := min_eq_left (Nat.le_of_lt a)
    have hmin_si1 : min (si + 1) s.length = si + 1 := min_eq_left a
    show ∃ (f : ℕ → ℕ), (∀ i < si + 1, i < s.length → f i < ti + 1 ∧ f i < t.length) ∧ StrictMonoOn f (Set.Iio (min (si + 1) s.length)) ∧ ∀ i < si + 1, i < s.length → (List.take (si + 1) s)[i]?.getD 'A' = (List.take (ti + 1) t)[f i]?.getD 'A'
    rw [hmin_si] at hf_mono
    rw [hmin_si1]
    refine ⟨fun i => if i < si then f i else ti, ?_, ?_, ?_⟩
    · -- Bound property
      intro i hi his
      by_cases hisi : i < si
      · simp only [hisi, ite_true]
        exact ⟨Nat.lt_of_lt_of_le (hf_bound i hisi his).1 (Nat.le_succ ti), (hf_bound i hisi his).2⟩
      · simp only [show ¬(i < si) from hisi, ite_false]
        exact ⟨Nat.lt_succ_of_le (Nat.le_refl ti), a_1⟩
    · -- Strict monotonicity
      intro x hx y hy hxy
      simp only [Set.mem_Iio] at hx hy
      by_cases hxsi : x < si
      · by_cases hysi : y < si
        · simp only [hxsi, hysi, ite_true]
          exact hf_mono (Set.mem_Iio.mpr hxsi) (Set.mem_Iio.mpr hysi) hxy
        · simp only [hxsi, ite_true, show ¬(y < si) from hysi, ite_false]
          exact (hf_bound x hxsi (by omega)).1
      · exfalso; omega
    · -- Character matching
      intro i hi his
      by_cases hisi : i < si
      · simp only [hisi, ite_true]
        have hm := hf_match i hisi his
        rw [List.getElem?_take, List.getElem?_take] at hm
        simp only [hisi, ite_true] at hm
        rw [List.getElem?_take, List.getElem?_take]
        have : i < si + 1 := by omega
        simp only [this, ite_true]
        have hfi_lt_ti := (hf_bound i hisi his).1
        have : f i < ti + 1 := by omega
        simp only [this, ite_true]
        simp only [hfi_lt_ti, ite_true] at hm
        exact hm
      · have hieq : i = si := by omega
        simp only [show ¬(i < si) from hisi, ite_false]
        rw [List.getElem?_take, List.getElem?_take]
        have h1 : i < si + 1 := by omega
        have h2 : ti < ti + 1 := by omega
        simp only [h1, ite_true, h2, ite_true]
        rw [hieq]
        exact if_pos

theorem goal_1_0
    (s : List Char)
    (si : ℕ)
    (a : si < s.length)
    (f : ℕ → ℕ)
    (hf_mono : StrictMonoOn f (Set.Iio (s.length - si)))
    (hlen_pos : 0 < s.length - si)
    : ∀ i < s.length - (si + 1), f (i + 1) ≥ 1 := by
    intro i hi
    have h0_in : (0 : ℕ) ∈ Set.Iio (s.length - si) := by
      rw [Set.mem_Iio]; omega
    have hi1_in : (i + 1 : ℕ) ∈ Set.Iio (s.length - si) := by
      rw [Set.mem_Iio]; omega
    have h01 : (0 : ℕ) < i + 1 := by omega
    have hf_lt := hf_mono h0_in hi1_in h01
    omega

theorem goal_1_1
    (s : List Char)
    (si : ℕ)
    (a : si < s.length)
    (f : ℕ → ℕ)
    (hf_mono : StrictMonoOn f (Set.Iio (s.length - si)))
    (hf_ge_one : ∀ i < s.length - (si + 1), f (i + 1) ≥ 1)
    : StrictMonoOn (fun i => f (i + 1) - 1) (Set.Iio (s.length - (si + 1))) := by
    intro i hi j hj hij
    simp only [Set.mem_Iio] at hi hj
    -- We need f(i+1) - 1 < f(j+1) - 1
    -- First, show i+1 and j+1 are in the domain of hf_mono
    have hi1 : i + 1 < s.length - si := by omega
    have hj1 : j + 1 < s.length - si := by omega
    have hij1 : i + 1 < j + 1 := by omega
    have hf_lt : f (i + 1) < f (j + 1) := by
      apply hf_mono
      · exact Set.mem_Iio.mpr hi1
      · exact Set.mem_Iio.mpr hj1
      · exact hij1
    have hfi_ge : f (i + 1) ≥ 1 := hf_ge_one i hi
    exact Nat.sub_lt_sub_right hfi_ge hf_lt

theorem goal_1
    (s : List Char)
    (t : List Char)
    (si : ℕ)
    (ti : ℕ)
    (invariant_si_bound : si ≤ s.length)
    (invariant_ti_bound : ti ≤ t.length)
    (invariant_partial_subseq : ∃ (f : ℕ → ℕ), (∀ i < si, i < s.length → f i < ti ∧ f i < t.length) ∧ StrictMonoOn f (Set.Iio (min si s.length)) ∧ ∀ i < si, i < s.length → (List.take si s)[i]?.getD 'A' = (List.take ti t)[f i]?.getD 'A')
    (invariant_greedy_ahead : ∀ (x : ℕ → ℕ), (∀ i < s.length, x i < t.length) → StrictMonoOn x (Set.Iio s.length) → (∀ i < s.length, s[i]?.getD 'A' = t[x i]?.getD 'A') → ∃ (f : ℕ → ℕ), (∀ i < s.length - si, f i < t.length - ti) ∧ StrictMonoOn f (Set.Iio (s.length - si)) ∧ ∀ i < s.length - si, s[si + i]?.getD 'A' = t[ti + f i]?.getD 'A')
    (a : si < s.length)
    (a_1 : ti < t.length)
    (if_pos : s[si]?.getD 'A' = t[ti]?.getD 'A')
    : ∀ (x : ℕ → ℕ), (∀ i < s.length, x i < t.length) → StrictMonoOn x (Set.Iio s.length) → (∀ i < s.length, s[i]?.getD 'A' = t[x i]?.getD 'A') → ∃ (f : ℕ → ℕ), (∀ i < s.length - (si + OfNat.ofNat 1), f i < t.length - (ti + OfNat.ofNat 1)) ∧ StrictMonoOn f (Set.Iio (s.length - (si + OfNat.ofNat 1))) ∧ ∀ i < s.length - (si + OfNat.ofNat 1), s[si + OfNat.ofNat 1 + i]?.getD 'A' = t[ti + OfNat.ofNat 1 + f i]?.getD 'A' := by
    intro x hx_bound hx_mono hx_match
    -- Apply the existing greedy_ahead invariant to get f for s[si..] into t[ti..]
    obtain ⟨f, hf_bound, hf_mono, hf_match⟩ := invariant_greedy_ahead x hx_bound hx_mono hx_match
    -- We know s.length - si ≥ 1 since si < s.length
    have hlen_pos : 0 < s.length - si := by omega
    -- f(0) is well-defined and f(0) < t.length - ti
    have hf0_bound : f 0 < t.length - ti := hf_bound 0 hlen_pos
    -- For i+1 < s.length - si, f(i+1) > f(0) ≥ 0 by strict monotonicity, so f(i+1) ≥ 1
    have hf_ge_one : ∀ i, i < s.length - (si + 1) → f (i + 1) ≥ 1 := by expose_names; exact (goal_1_0 s si a f hf_mono hlen_pos)
    -- Define g(i) = f(i+1) - 1
    -- g maps valid indices to valid indices
    have hg_bound : ∀ i, i < s.length - (si + 1) → f (i + 1) - 1 < t.length - (ti + 1) := by expose_names; intros; expose_names; try simp_all; try grind
    -- g is strictly monotone
    have hg_mono : StrictMonoOn (fun i => f (i + 1) - 1) (Set.Iio (s.length - (si + 1))) := by expose_names; exact (goal_1_1 s si a f hf_mono hf_ge_one)
    -- g preserves character matching
    have hg_match : ∀ i, i < s.length - (si + 1) → s[si + 1 + i]?.getD 'A' = t[ti + 1 + (f (i + 1) - 1)]?.getD 'A' := by expose_names; intros; expose_names; try simp_all; try grind
    exact ⟨fun i => f (i + 1) - 1, hg_bound, hg_mono, hg_match⟩

theorem goal_2
    (s : List Char)
    (t : List Char)
    (si : ℕ)
    (ti : ℕ)
    (invariant_si_bound : si ≤ s.length)
    (invariant_partial_subseq : ∃ (f : ℕ → ℕ), (∀ i < si, i < s.length → f i < ti ∧ f i < t.length) ∧ StrictMonoOn f (Set.Iio (min si s.length)) ∧ ∀ i < si, i < s.length → (List.take si s)[i]?.getD 'A' = (List.take ti t)[f i]?.getD 'A')
    (invariant_greedy_ahead : ∀ (x : ℕ → ℕ), (∀ i < s.length, x i < t.length) → StrictMonoOn x (Set.Iio s.length) → (∀ i < s.length, s[i]?.getD 'A' = t[x i]?.getD 'A') → ∃ (f : ℕ → ℕ), (∀ i < s.length - si, f i < t.length - ti) ∧ StrictMonoOn f (Set.Iio (s.length - si)) ∧ ∀ i < s.length - si, s[si + i]?.getD 'A' = t[ti + f i]?.getD 'A')
    (a : si < s.length)
    (a_1 : ti < t.length)
    (if_neg : ¬s[si]?.getD 'A' = t[ti]?.getD 'A')
    : ∃ (f : ℕ → ℕ), (∀ i < si, i < s.length → f i < ti + OfNat.ofNat 1 ∧ f i < t.length) ∧ StrictMonoOn f (Set.Iio (min si s.length)) ∧ ∀ i < si, i < s.length → (List.take si s)[i]?.getD 'A' = (List.take (ti + OfNat.ofNat 1) t)[f i]?.getD 'A' := by
    intros; expose_names; try simp_all; try grind

theorem goal_3_0
    (s : List Char)
    (t : List Char)
    (si : ℕ)
    (ti : ℕ)
    (if_neg : ¬s[si]?.getD 'A' = t[ti]?.getD 'A')
    (f : ℕ → ℕ)
    (hf_match : ∀ i < s.length - si, s[si + i]?.getD 'A' = t[ti + f i]?.getD 'A')
    (hlen_pos : 0 < s.length - si)
    : f 0 ≥ 1 := by
    by_contra h
    push_neg at h
    have hf0 : f 0 = 0 := Nat.lt_one_iff.mp h
    have h0 := hf_match 0 hlen_pos
    simp [hf0] at h0
    exact if_neg h0

theorem goal_3_1
    (s : List Char)
    (si : ℕ)
    (a : si < s.length)
    (f : ℕ → ℕ)
    (hf_mono : StrictMonoOn f (Set.Iio (s.length - si)))
    (hf0_ge : f 0 ≥ 1)
    : ∀ i < s.length - si, f i ≥ 1 := by
    intro i hi
    by_cases h : i = 0
    · subst h; exact hf0_ge
    · have hi0 : 0 < i := Nat.pos_of_ne_zero h
      have hf_lt : f 0 < f i := by
        apply hf_mono
        · simp [Set.mem_Iio]; omega
        · simp [Set.mem_Iio]; exact hi
        · exact hi0
      omega

theorem goal_3_2
    (s : List Char)
    (si : ℕ)
    (f : ℕ → ℕ)
    (hf_mono : StrictMonoOn f (Set.Iio (s.length - si)))
    (hf_all_ge : ∀ i < s.length - si, f i ≥ 1)
    : StrictMonoOn (fun i => f i - 1) (Set.Iio (s.length - si)) := by
    intro a₁ ha₁ b₁ hb₁ hab
    simp only
    have ha₁' : a₁ ∈ Set.Iio (s.length - si) := ha₁
    have hb₁' : b₁ ∈ Set.Iio (s.length - si) := hb₁
    have hfab : f a₁ < f b₁ := hf_mono ha₁' hb₁' hab
    have hfa_ge : f a₁ ≥ 1 := hf_all_ge a₁ (Set.mem_Iio.mp ha₁')
    exact Nat.sub_lt_sub_right hfa_ge hfab

theorem goal_3
    (s : List Char)
    (t : List Char)
    (si : ℕ)
    (ti : ℕ)
    (invariant_si_bound : si ≤ s.length)
    (invariant_ti_bound : ti ≤ t.length)
    (invariant_partial_subseq : ∃ (f : ℕ → ℕ), (∀ i < si, i < s.length → f i < ti ∧ f i < t.length) ∧ StrictMonoOn f (Set.Iio (min si s.length)) ∧ ∀ i < si, i < s.length → (List.take si s)[i]?.getD 'A' = (List.take ti t)[f i]?.getD 'A')
    (invariant_greedy_ahead : ∀ (x : ℕ → ℕ), (∀ i < s.length, x i < t.length) → StrictMonoOn x (Set.Iio s.length) → (∀ i < s.length, s[i]?.getD 'A' = t[x i]?.getD 'A') → ∃ (f : ℕ → ℕ), (∀ i < s.length - si, f i < t.length - ti) ∧ StrictMonoOn f (Set.Iio (s.length - si)) ∧ ∀ i < s.length - si, s[si + i]?.getD 'A' = t[ti + f i]?.getD 'A')
    (a : si < s.length)
    (a_1 : ti < t.length)
    (if_neg : ¬s[si]?.getD 'A' = t[ti]?.getD 'A')
    : ∀ (x : ℕ → ℕ), (∀ i < s.length, x i < t.length) → StrictMonoOn x (Set.Iio s.length) → (∀ i < s.length, s[i]?.getD 'A' = t[x i]?.getD 'A') → ∃ (f : ℕ → ℕ), (∀ i < s.length - si, f i < t.length - (ti + OfNat.ofNat 1)) ∧ StrictMonoOn f (Set.Iio (s.length - si)) ∧ ∀ i < s.length - si, s[si + i]?.getD 'A' = t[ti + OfNat.ofNat 1 + f i]?.getD 'A' := by
    intro x hx_bound hx_mono hx_match
    obtain ⟨f, hf_bound, hf_mono, hf_match⟩ := invariant_greedy_ahead x hx_bound hx_mono hx_match
    have hlen_pos : 0 < s.length - si := by omega
    -- f(0) ≥ 1 because s[si] ≠ t[ti] but s[si+0] = t[ti + f(0)]
    have hf0_ge : f 0 ≥ 1 := by expose_names; exact (goal_3_0 s t si ti if_neg f hf_match hlen_pos)
    -- All f values ≥ 1 by strict monotonicity
    have hf_all_ge : ∀ i < s.length - si, f i ≥ 1 := by expose_names; exact (goal_3_1 s si a f hf_mono hf0_ge)
    -- Strict monotonicity of shifted function
    have hg_mono : StrictMonoOn (fun i => f i - 1) (Set.Iio (s.length - si)) := by expose_names; exact (goal_3_2 s si f hf_mono hf_all_ge)
    -- Bound: f(i) - 1 < t.length - (ti + 1)
    have hg_bound : ∀ i < s.length - si, f i - 1 < t.length - (ti + 1) := by expose_names; intros; expose_names; try simp_all; try grind
    -- Character matching: ti + f(i) = ti + 1 + (f(i) - 1)
    have hg_match : ∀ i < s.length - si, s[si + i]?.getD 'A' = t[ti + OfNat.ofNat 1 + (f i - 1)]?.getD 'A' := by expose_names; intros; expose_names; try simp_all; try grind
    exact ⟨fun i => f i - 1, hg_bound, hg_mono, hg_match⟩

theorem goal_4 : ∃ (f : ℕ → ℕ), StrictMonoOn f ∅ := by
    exact ⟨id, fun _ h => absurd h (Set.not_mem_empty _)⟩

theorem goal_5_0
    (s : List Char)
    (t : List Char)
    (i : ℕ)
    (ti_1 : ℕ)
    (invariant_si_bound : i ≤ s.length)
    (invariant_ti_bound : ti_1 ≤ t.length)
    (invariant_greedy_ahead : ∀ (x : ℕ → ℕ),
  (∀ i < s.length, x i < t.length) →
    StrictMonoOn x (Set.Iio s.length) →
      (∀ i < s.length, s[i]?.getD 'A' = t[x i]?.getD 'A') →
        ∃ f,
          (∀ i_1 < s.length - i, f i_1 < t.length - ti_1) ∧
            StrictMonoOn f (Set.Iio (s.length - i)) ∧
              ∀ i_1 < s.length - i, s[i + i_1]?.getD 'A' = t[ti_1 + f i_1]?.getD 'A')
    (done_1 : i < s.length → t.length ≤ ti_1)
    : subseqByIndex s t → i = s.length := by
    intro ⟨x, hx_bound, hx_mono, hx_match⟩
    by_contra h
    have hi_lt : i < s.length := Nat.lt_of_le_of_ne invariant_si_bound h
    have hti : t.length ≤ ti_1 := done_1 hi_lt
    have hti_eq : ti_1 = t.length := Nat.le_antisymm invariant_ti_bound hti
    -- Convert hx_match from get! to getElem?.getD
    have hx_match' : ∀ j < s.length, s[j]?.getD 'A' = t[x j]?.getD 'A' := by
      intro j hj
      have := hx_match j hj
      rw [List.get!_eq_getElem!, List.get!_eq_getElem!] at this
      rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD] at this
      convert this using 1 <;> simp [List.getD_getElem?]
    obtain ⟨f, hf_bound, _, _⟩ := invariant_greedy_ahead x hx_bound hx_mono hx_match'
    have hlen_pos : 0 < s.length - i := Nat.sub_pos_of_lt hi_lt
    have := hf_bound 0 hlen_pos
    rw [hti_eq] at this
    simp at this

theorem goal_5
    (s : List Char)
    (t : List Char)
    (i : ℕ)
    (ti_1 : ℕ)
    (invariant_si_bound : i ≤ s.length)
    (invariant_ti_bound : ti_1 ≤ t.length)
    (invariant_partial_subseq : ∃ (f : ℕ → ℕ), (∀ i_1 < i, i_1 < s.length → f i_1 < ti_1 ∧ f i_1 < t.length) ∧ StrictMonoOn f (Set.Iio (min i s.length)) ∧ ∀ i_1 < i, i_1 < s.length → (List.take i s)[i_1]?.getD 'A' = (List.take ti_1 t)[f i_1]?.getD 'A')
    (invariant_greedy_ahead : ∀ (x : ℕ → ℕ), (∀ i < s.length, x i < t.length) → StrictMonoOn x (Set.Iio s.length) → (∀ i < s.length, s[i]?.getD 'A' = t[x i]?.getD 'A') → ∃ (f : ℕ → ℕ), (∀ i_1 < s.length - i, f i_1 < t.length - ti_1) ∧ StrictMonoOn f (Set.Iio (s.length - i)) ∧ ∀ i_1 < s.length - i, s[i + i_1]?.getD 'A' = t[ti_1 + f i_1]?.getD 'A')
    (done_1 : i < s.length → t.length ≤ ti_1)
    : postcondition s t (i == s.length) := by
    unfold postcondition
    rw [beq_iff_eq]
    constructor
    · -- Forward: i = s.length → subseqByIndex s t
      have h_fwd : i = s.length → subseqByIndex s t := by expose_names; intros; expose_names; try simp_all; try grind
      exact h_fwd
    · -- Backward: subseqByIndex s t → i = s.length
      have h_bwd : subseqByIndex s t → i = s.length := by expose_names; exact (goal_5_0 s t i ti_1 invariant_si_bound invariant_ti_bound invariant_greedy_ahead done_1)
      exact h_bwd


prove_correct IsSubsequence by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at *); try (conv => congr <;> simp) ; try expose_names)
  exact (goal_0 s t si ti invariant_partial_subseq a a_1 if_pos)
  exact (goal_1 s t si ti invariant_si_bound invariant_ti_bound invariant_partial_subseq invariant_greedy_ahead a a_1 if_pos)
  exact (goal_2 s t si ti invariant_si_bound invariant_partial_subseq invariant_greedy_ahead a a_1 if_neg)
  exact (goal_3 s t si ti invariant_si_bound invariant_ti_bound invariant_partial_subseq invariant_greedy_ahead a a_1 if_neg)
  exact (goal_4)
  exact (goal_5 s t i ti_1 invariant_si_bound invariant_ti_bound invariant_partial_subseq invariant_greedy_ahead done_1)
end Proof
