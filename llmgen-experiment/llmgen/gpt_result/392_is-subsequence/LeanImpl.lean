import Lean
import Mathlib.Tactic
import Velvet.Std

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
  -- Two-pointer scan: advance through `t`, consuming from `s` when characters match.
  let rec go (s : List Char) (t : List Char) : Bool :=
    match s, t with
    | [], _ => true
    | _ :: _, [] => false
    | sh :: st, th :: tt =>
        if sh = th then
          go st tt
        else
          go s tt
  go s t
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

section Proof
theorem correctness_goal
    (s : List Char)
    (t : List Char)
    (h_precond : precondition s t)
    : postcondition s t (implementation s t) := by
  classical

  have _ : True := h_precond

  have get!_eq_get {α : Type} [Inhabited α] (l : List α) (n : Nat) (h : n < l.length) :
      l.get! n = l.get ⟨n, h⟩ := by
    induction l generalizing n with
    | nil =>
        cases (Nat.not_lt_zero n h)
    | cons a tl ih =>
        cases n with
        | zero =>
            simp
        | succ n =>
            have h' : n < tl.length := Nat.lt_of_succ_lt_succ h
            simpa [Nat.succ_eq_add_one, List.get!_cons_succ, List.get_cons_succ] using ih n h'

  have subseqByIndex_iff_sublist (s t : List Char) : subseqByIndex s t ↔ List.Sublist s t := by
    constructor
    · intro h
      rcases h with ⟨f, hf_bound, hf_mono, hf_match⟩
      let gFun : Fin s.length → Fin t.length := fun ix => ⟨f ix.1, hf_bound ix.1 ix.2⟩
      have hg_strict : StrictMono gFun := by
        intro i j hij
        have hi : (i.1 : Nat) ∈ Set.Iio s.length := i.2
        have hj : (j.1 : Nat) ∈ Set.Iio s.length := j.2
        have hij' : (i.1 : Nat) < j.1 := hij
        exact hf_mono hi hj hij'
      let gEmb : Fin s.length ↪o Fin t.length :=
        { toEmbedding :=
            { toFun := gFun
              inj' := hg_strict.injective }
          map_rel_iff' := by
            intro a b
            constructor
            · intro hab
              by_contra hn
              have hlt : b < a := lt_of_not_ge hn
              have : gFun b < gFun a := hg_strict hlt
              exact (not_lt_of_ge hab) this
            · intro hab
              exact hg_strict.monotone hab }
      have hget : ∀ ix : Fin s.length, s.get ix = t.get (gEmb ix) := by
        intro ix
        have hm : s.get! ix.1 = t.get! (f ix.1) := hf_match ix.1 ix.2
        have hs : s.get! ix.1 = s.get ix := (get!_eq_get s ix.1 ix.2)
        have ht : t.get! (f ix.1) = t.get ⟨f ix.1, hf_bound ix.1 ix.2⟩ :=
          (get!_eq_get t (f ix.1) (hf_bound ix.1 ix.2))
        have : s.get ix = t.get ⟨f ix.1, hf_bound ix.1 ix.2⟩ := by
          calc
            s.get ix = s.get! ix.1 := by simpa using hs.symm
            _ = t.get! (f ix.1) := by simpa using hm
            _ = t.get ⟨f ix.1, hf_bound ix.1 ix.2⟩ := by simpa using ht
        simpa [gEmb, gFun] using this
      exact (List.sublist_iff_exists_fin_orderEmbedding_get_eq).2 ⟨gEmb, hget⟩
    · intro h
      rcases (List.sublist_iff_exists_fin_orderEmbedding_get_eq).1 h with ⟨gEmb, hget⟩
      refine ⟨fun i => if hi : i < s.length then (gEmb ⟨i, hi⟩).1 else 0, ?_, ?_, ?_⟩
      · intro i hi
        simp [hi]
      · intro i hi j hj hij
        have hi' : i < s.length := by
          simpa [Set.mem_Iio] using hi
        have hj' : j < s.length := by
          simpa [Set.mem_Iio] using hj
        -- after unfolding the `if`s, the goal reduces to `i < j` (since `gEmb` reflects order)
        simp [hi', hj']
        exact hij
      · intro i hi
        have hget' : s.get ⟨i, hi⟩ = t.get (gEmb ⟨i, hi⟩) := hget ⟨i, hi⟩
        have hs : s.get! i = s.get ⟨i, hi⟩ := (get!_eq_get s i hi)
        have ht : t.get! (gEmb ⟨i, hi⟩).1 = t.get (gEmb ⟨i, hi⟩) :=
          (get!_eq_get t (gEmb ⟨i, hi⟩).1 (gEmb ⟨i, hi⟩).2)
        simpa [hs, ht, hi] using hget'

  have impl_eq_true_iff_sublist (s t : List Char) : implementation s t = true ↔ List.Sublist s t := by
    induction t generalizing s with
    | nil =>
        cases s with
        | nil =>
            simp [implementation, implementation.go, List.nil_sublist]
        | cons sh st =>
            simp [implementation, implementation.go]
    | cons th tt ih =>
        cases s with
        | nil =>
            simp [implementation, implementation.go, List.nil_sublist]
        | cons sh st =>
            by_cases hEq : sh = th
            · subst hEq
              constructor
              · intro hImpl
                have hImpl' : implementation st tt = true := by
                  simpa [implementation, implementation.go] using hImpl
                have hSub : List.Sublist st tt := (ih st).1 hImpl'
                exact List.Sublist.cons_cons sh hSub
              · intro hSub
                have hSubTail : List.Sublist st tt := List.Sublist.of_cons_cons hSub
                have : implementation st tt = true := (ih st).2 hSubTail
                simpa [implementation, implementation.go]
            ·
              have hSub_iff : List.Sublist (sh :: st) (th :: tt) ↔ List.Sublist (sh :: st) tt := by
                constructor
                · intro hSub
                  have : List.Sublist (sh :: st) tt ∨ ∃ r, (sh :: st) = th :: r ∧ List.Sublist r tt :=
                    (List.sublist_cons_iff).1 hSub
                  cases this with
                  | inl h => exact h
                  | inr h2 =>
                      rcases h2 with ⟨r, hr, _⟩
                      cases hr
                      contradiction
                · intro hSub
                  exact hSub.cons th
              have : implementation (sh :: st) tt = true ↔ List.Sublist (sh :: st) tt := ih (sh :: st)
              simpa [implementation, implementation.go, hEq, hSub_iff] using this

  simp [postcondition]
  have himpl : implementation s t = true ↔ List.Sublist s t := impl_eq_true_iff_sublist s t
  have hspec : subseqByIndex s t ↔ List.Sublist s t := subseqByIndex_iff_sublist s t
  exact Iff.trans himpl (Iff.symm hspec)
end Proof
