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
private lemma impl_sound : ∀ (s t : List Char), implementation s t = true → subseqByIndex s t := by
  intro s
  induction s with
  | nil =>
    intro t _
    exact ⟨id, fun i h => absurd h (Nat.not_lt_zero i),
           fun _ (h : _ ∈ Set.Iio ([] : List Char).length) => absurd (Set.mem_Iio.mp h) (Nat.not_lt_zero _),
           fun i h => absurd h (Nat.not_lt_zero i)⟩
  | cons sc ss ih =>
    intro t
    induction t with
    | nil =>
      simp [implementation]
    | cons tc ts iht =>
      intro h
      unfold implementation at h
      by_cases heq : sc = tc
      · -- heads match
        have hbeq : (sc == tc) = true := beq_iff_eq.mpr heq
        simp [hbeq] at h
        have hsub := ih ts h
        obtain ⟨f', hf'bound, hf'mono, hf'char⟩ := hsub
        refine ⟨fun i => if i = 0 then 0 else f' (i - 1) + 1, ?_, ?_, ?_⟩
        · -- valid indices
          intro i hi
          simp only [List.length_cons] at hi ⊢
          by_cases h0 : i = 0
          · simp [h0]
          · simp only [ite_eq_right_iff, h0, ↓reduceIte]
            have : i - 1 < ss.length := by omega
            have := hf'bound (i - 1) this
            omega
        · -- strict monotonicity
          intro i hi j hj hij
          simp only [Set.mem_Iio, List.length_cons] at hi hj
          show (if i = 0 then 0 else f' (i - 1) + 1) < (if j = 0 then 0 else f' (j - 1) + 1)
          by_cases hi0 : i = 0
          · subst hi0
            have hj0 : j ≠ 0 := by omega
            simp only [↓reduceIte, hj0]
            omega
          · have hj0 : j ≠ 0 := by omega
            simp only [hi0, hj0, ↓reduceIte]
            have hi' : i - 1 < ss.length := by omega
            have hj' : j - 1 < ss.length := by omega
            have hij' : i - 1 < j - 1 := by omega
            have := hf'mono (Set.mem_Iio.mpr hi') (Set.mem_Iio.mpr hj') hij'
            omega
        · -- character matching
          intro i hi
          simp only [List.length_cons] at hi
          show (sc :: ss).get! i = (tc :: ts).get! (if i = 0 then 0 else f' (i - 1) + 1)
          by_cases h0 : i = 0
          · subst h0
            simp only [↓reduceIte]
            exact (by rw [List.get!_cons_zero, List.get!_cons_zero]; exact heq)
          · simp only [h0, ↓reduceIte]
            have hi' : i - 1 < ss.length := by omega
            have hchar := hf'char (i - 1) hi'
            conv_lhs => rw [show i = (i - 1) + 1 from by omega]
            rw [List.get!_cons_succ, List.get!_cons_succ]
            exact hchar
      · -- heads don't match
        have hbeq : ¬ (sc == tc) = true := by rw [beq_iff_eq]; exact heq
        simp [hbeq] at h
        have hsub := iht h
        obtain ⟨f', hf'bound, hf'mono, hf'char⟩ := hsub
        refine ⟨fun i => f' i + 1, ?_, ?_, ?_⟩
        · -- valid indices
          intro i hi
          simp only [List.length_cons]
          have := hf'bound i hi
          omega
        · -- strict monotonicity
          intro i hi j hj hij
          show f' i + 1 < f' j + 1
          have := hf'mono hi hj hij
          omega
        · -- character matching
          intro i hi
          have hchar := hf'char i hi
          show (sc :: ss).get! i = (tc :: ts).get! (f' i + 1)
          rw [hchar, List.get!_cons_succ]


theorem correctness_goal_0
    (s : List Char)
    (t : List Char)
    : ∀ (s t : List Char), implementation s t = true → subseqByIndex s t := by
    intro s' t' h
    exact impl_sound s' t' h

private lemma subseq_complete : ∀ (s t : List Char), subseqByIndex s t → implementation s t = true := by
  intro s
  induction s with
  | nil => intro t _; simp [implementation]
  | cons sc ss ih_ss =>
    intro t
    induction t with
    | nil =>
      intro ⟨f, hbound, _, _⟩
      exact absurd (hbound 0 (Nat.zero_lt_succ _)) (Nat.not_lt_zero _)
    | cons tc ts ih_ts =>
      intro ⟨f, hbound, hmono, hmatch⟩
      simp [implementation]
      split
      case isTrue heq =>
        apply ih_ss ts
        let g : Nat → Nat := fun i => f (i + 1) - 1
        have hg_def : ∀ i, g i = f (i + 1) - 1 := fun _ => rfl
        have hss_len : (sc :: ss).length = ss.length + 1 := List.length_cons
        have hts_len : (tc :: ts).length = ts.length + 1 := List.length_cons
        have hf_succ_ge1 : ∀ i, i < ss.length → f (i + 1) ≥ 1 := by
          intro i hi
          have h0mem : (0 : Nat) ∈ Set.Iio (↑(sc :: ss).length : Nat) := by
            rw [Set.mem_Iio, hss_len]; omega
          have hi1mem : (i + 1) ∈ Set.Iio (↑(sc :: ss).length : Nat) := by
            rw [Set.mem_Iio, hss_len]; omega
          have := hmono h0mem hi1mem (Nat.zero_lt_succ i)
          omega
        exact ⟨g, fun i hi => by
          have hfi := hbound (i + 1) (by rw [hss_len]; omega)
          rw [hts_len] at hfi
          have := hf_succ_ge1 i hi
          rw [hg_def]; omega,
        fun a ha b hb hab => by
          rw [Set.mem_Iio] at ha hb
          have ha' : (a + 1) ∈ Set.Iio (↑(sc :: ss).length : Nat) := by rw [Set.mem_Iio, hss_len]; omega
          have hb' : (b + 1) ∈ Set.Iio (↑(sc :: ss).length : Nat) := by rw [Set.mem_Iio, hss_len]; omega
          have hfab := hmono ha' hb' (by omega : a + 1 < b + 1)
          have hfa := hf_succ_ge1 a (by omega)
          have hfb := hf_succ_ge1 b (by omega)
          rw [hg_def, hg_def]; omega,
        fun i hi => by
          have hi' : i + 1 < (sc :: ss).length := by rw [hss_len]; omega
          have hchar := hmatch (i + 1) hi'
          rw [List.get!_cons_succ] at hchar
          have hge := hf_succ_ge1 i hi
          -- goal: ss.get! i = ts.get! g(i)  where g(i) = f(i+1) - 1
          -- hchar: ss.get! i = (tc :: ts).get! (f (i + 1))
          -- We need: (tc :: ts).get! (f (i + 1)) = ts.get! (f (i + 1) - 1)
          rw [hg_def, hchar]
          -- goal: (tc :: ts).get! (f (i + 1)) = ts.get! (f (i + 1) - 1)
          have hfeq : f (i + 1) = (f (i + 1) - 1) + 1 := by omega
          conv_lhs => rw [hfeq]
          rw [List.get!_cons_succ]⟩
      case isFalse hneq =>
        apply ih_ts
        let g : Nat → Nat := fun i => f i - 1
        have hg_def : ∀ i, g i = f i - 1 := fun _ => rfl
        have hss_len : (sc :: ss).length = ss.length + 1 := List.length_cons
        have hts_len : (tc :: ts).length = ts.length + 1 := List.length_cons
        have hf0_pos : f 0 ≥ 1 := by
          by_contra h
          push_neg at h
          have hf0_zero : f 0 = 0 := by omega
          have hchar0 := hmatch 0 (by rw [hss_len]; omega)
          rw [List.get!_cons_zero, hf0_zero, List.get!_cons_zero] at hchar0
          exact hneq hchar0
        have hf_ge1 : ∀ i, i < (sc :: ss).length → f i ≥ 1 := by
          intro i hi
          by_cases h0 : i = 0
          · subst h0; exact hf0_pos
          · have hi_pos : 0 < i := Nat.pos_of_ne_zero h0
            have h0mem : (0 : Nat) ∈ Set.Iio (↑(sc :: ss).length : Nat) := by
              rw [Set.mem_Iio]; omega
            have himem : i ∈ Set.Iio (↑(sc :: ss).length : Nat) := Set.mem_Iio.mpr hi
            have := hmono h0mem himem hi_pos
            omega
        exact ⟨g, fun i hi => by
          have hfi := hbound i hi
          rw [hts_len] at hfi
          have := hf_ge1 i hi
          rw [hg_def]; omega,
        fun a ha b hb hab => by
          rw [Set.mem_Iio] at ha hb
          have hamem : a ∈ Set.Iio (↑(sc :: ss).length : Nat) := Set.mem_Iio.mpr ha
          have hbmem : b ∈ Set.Iio (↑(sc :: ss).length : Nat) := Set.mem_Iio.mpr hb
          have hfab := hmono hamem hbmem hab
          have hfa := hf_ge1 a ha
          rw [hg_def, hg_def]; omega,
        fun i hi => by
          have hchar := hmatch i hi
          have hge := hf_ge1 i hi
          rw [hg_def, hchar]
          -- goal: (tc :: ts).get! (f i) = ts.get! (f i - 1)
          have hfeq : f i = (f i - 1) + 1 := by omega
          conv_lhs => rw [hfeq]
          rw [List.get!_cons_succ]⟩


theorem correctness_goal_1
    (s : List Char)
    (t : List Char)
    : ∀ (s t : List Char), subseqByIndex s t → implementation s t = true := by
    exact fun s t h => subseq_complete s t h

theorem correctness_goal
    (s : List Char)
    (t : List Char)
    : postcondition s t (implementation s t) := by
    unfold postcondition
    constructor
    · -- Forward: implementation returns true → subseqByIndex
      intro h_impl
      have h_fwd : ∀ (s t : List Char), implementation s t = true → subseqByIndex s t := by expose_names; exact (correctness_goal_0 s t)
      exact h_fwd s t h_impl
    · -- Backward: subseqByIndex → implementation returns true
      intro h_sub
      have h_bwd : ∀ (s t : List Char), subseqByIndex s t → implementation s t = true := by expose_names; exact (correctness_goal_1 s t)
      exact h_bwd s t h_sub
end Proof
