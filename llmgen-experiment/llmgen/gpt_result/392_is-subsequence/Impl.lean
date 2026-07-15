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
  -- O(n) time, O(1) extra space: two pointers over arrays (O(1) indexing).
  let sArr : Array Char := s.toArray
  let tArr : Array Char := t.toArray
  let mut i : Nat := 0
  let mut j : Nat := 0

  -- Scan t left-to-right, advancing i when matching next character of s.
  while (i < sArr.size ∧ j < tArr.size)
    -- Bounds for safe indexing.
    invariant "bounds" (i ≤ sArr.size ∧ j ≤ tArr.size)
    -- Greedy witness: the first `i` chars of `s` have been matched in order within the
    -- scanned prefix `t[0..j)`, and each match position is minimal (first occurrence after
    -- the previous match). Also, the next needed character (if any) has not appeared since
    -- the last match within `t[0..j)`.
    invariant "greedy_witness"
      (∃ f : Nat → Nat,
        (∀ p : Nat, p < i → f p < j) ∧
        StrictMonoOn f (Set.Iio i) ∧
        (∀ p : Nat, p < i → sArr[p]! = tArr[f p]!) ∧
        (∀ p : Nat, p < i →
          (∀ k : Nat,
            ((if p = 0 then 0 else (f (p - 1) + 1)) ≤ k ∧ k < f p) →
              tArr[k]! ≠ sArr[p]!)) ∧
        (i < sArr.size →
          ∀ k : Nat,
            ((if i = 0 then 0 else (f (i - 1) + 1)) ≤ k ∧ k < j) →
              tArr[k]! ≠ sArr[i]!))
    -- Termination: `j` strictly increases each iteration.
    decreasing (tArr.size - j)
  do
    if sArr[i]! = tArr[j]! then
      i := i + 1
      j := j + 1
    else
      j := j + 1

  if i = sArr.size then
    return true
  else
    return false
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
    (i : ℕ)
    (j : ℕ)
    (invariant_greedy_witness : ∃ (f : ℕ → ℕ), (∀ p < i, f p < j) ∧ StrictMonoOn f (Set.Iio i) ∧ (∀ p < i, s[p]?.getD 'A' = t[f p]?.getD 'A') ∧ (∀ p < i, ∀ (k : ℕ), (if p = OfNat.ofNat 0 then OfNat.ofNat 0 else f (p - OfNat.ofNat 1) + OfNat.ofNat 1) ≤ k → k < f p → ¬t[k]?.getD 'A' = s[p]?.getD 'A') ∧ (i < s.length → ∀ (k : ℕ), (if i = OfNat.ofNat 0 then OfNat.ofNat 0 else f (i - OfNat.ofNat 1) + OfNat.ofNat 1) ≤ k → k < j → ¬t[k]?.getD 'A' = s[i]?.getD 'A'))
    (a_2 : i < s.length)
    (if_pos : s[i]?.getD 'A' = t[j]?.getD 'A')
    : ∃ (f : ℕ → ℕ), (∀ p < i + OfNat.ofNat 1, f p < j + OfNat.ofNat 1) ∧ StrictMonoOn f (Set.Iio (i + OfNat.ofNat 1)) ∧ (∀ p < i + OfNat.ofNat 1, s[p]?.getD 'A' = t[f p]?.getD 'A') ∧ (∀ p < i + OfNat.ofNat 1, ∀ (k : ℕ), (if p = OfNat.ofNat 0 then OfNat.ofNat 0 else f (p - OfNat.ofNat 1) + OfNat.ofNat 1) ≤ k → k < f p → ¬t[k]?.getD 'A' = s[p]?.getD 'A') ∧ (i + OfNat.ofNat 1 < s.length → ∀ (k : ℕ), f i + OfNat.ofNat 1 ≤ k → k < j + OfNat.ofNat 1 → ¬t[k]?.getD 'A' = s[i + OfNat.ofNat 1]?.getD 'A') := by
  classical
  rcases invariant_greedy_witness with ⟨f, hfLt, hfMono, hfEq, hfMin, hfNext⟩

  let f' : Nat → Nat := fun p => if h : p < i then f p else j

  refine ⟨f', ?_, ?_, ?_, ?_, ?_⟩

  · intro p hp
    have hp' : p < i + 1 := by simpa using hp
    by_cases hpi : p < i
    · have : f p < j := hfLt p hpi
      have : f' p < j := by simpa [f', hpi] using this
      exact lt_trans this (Nat.lt_succ_self j)
    · have hple : p ≤ i := Nat.le_of_lt_succ (by simpa [Nat.succ_eq_add_one] using hp')
      have hige : i ≤ p := Nat.le_of_not_gt hpi
      have hpEq : p = i := Nat.le_antisymm hple hige
      cases hpEq
      have hf'i : f' i = j := by simp [f', Nat.lt_irrefl]
      simpa [hf'i] using (Nat.lt_succ_self j)

  · -- StrictMonoOn
    intro m hm n hn hmn
    have hn' : n < i + 1 := hn
    by_cases hni : n < i
    · have hmi : m < i := lt_trans hmn hni
      have hmn_f : f m < f n := hfMono hmi hni hmn
      simpa [f', hmi, hni] using hmn_f
    · have hnle : n ≤ i := Nat.le_of_lt_succ (by simpa [Nat.succ_eq_add_one] using hn')
      have hige : i ≤ n := Nat.le_of_not_gt hni
      have hnEq : n = i := Nat.le_antisymm hnle hige
      have hmi : m < i := by simpa [hnEq] using hmn
      have hm_lt_j : f m < j := hfLt m hmi
      -- f' n = j
      have hf'n : f' n = j := by
        -- n = i
        cases hnEq
        simp [f', Nat.lt_irrefl]
      -- f' m = f m
      have hf'm : f' m = f m := by simp [f', hmi]
      -- conclude
      simpa [hf'm, hf'n] using hm_lt_j

  · intro p hp
    have hp' : p < i + 1 := by simpa using hp
    by_cases hpi : p < i
    · simpa [f', hpi] using (hfEq p hpi)
    · have hple : p ≤ i := Nat.le_of_lt_succ (by simpa [Nat.succ_eq_add_one] using hp')
      have hige : i ≤ p := Nat.le_of_not_gt hpi
      have hpEq : p = i := Nat.le_antisymm hple hige
      cases hpEq
      simpa [f', Nat.lt_irrefl] using if_pos

  · intro p hp k hk1 hk2
    have hp' : p < i + 1 := by simpa using hp
    by_cases hpi : p < i
    · -- old matched position
      have hk2' : k < f p := by simpa [f', hpi] using hk2
      have hk1' : (if p = 0 then 0 else f (p - 1) + 1) ≤ k := by
        by_cases hp0 : p = 0
        · simpa [hp0] using hk1
        · have hpred_p : p - 1 < p := by
            have : Nat.pred p < p := Nat.pred_lt (n := p) hp0
            simpa [Nat.pred_eq_sub_one] using this
          have hpred : p - 1 < i := lt_trans hpred_p hpi
          simpa [hp0, f', hpred] using hk1
      exact hfMin p hpi k hk1' hk2'
    · -- new position p = i
      have hple : p ≤ i := Nat.le_of_lt_succ (by simpa [Nat.succ_eq_add_one] using hp')
      have hige : i ≤ p := Nat.le_of_not_gt hpi
      have hpEq : p = i := Nat.le_antisymm hple hige
      cases hpEq
      have hk2' : k < j := by simpa [f', Nat.lt_irrefl] using hk2
      have hk1' : (if i = 0 then 0 else f (i - 1) + 1) ≤ k := by
        by_cases hi0 : i = 0
        · simpa [hi0] using hk1
        · have hpred : i - 1 < i := by
            have : Nat.pred i < i := Nat.pred_lt (n := i) hi0
            simpa [Nat.pred_eq_sub_one] using this
          simpa [hi0, f', hpred] using hk1
      exact hfNext a_2 k hk1' hk2'

  · intro _h k hk1 hk2
    have hf'i : f' i = j := by simp [f', Nat.lt_irrefl]
    have hk1' : j + 1 ≤ k := by simpa [hf'i] using hk1
    have hk2' : k < j + 1 := by simpa using hk2
    have : False := (Nat.not_lt_of_ge hk1') hk2'
    exact this.elim

theorem goal_1 : ∃ (f : ℕ → ℕ), StrictMonoOn f ∅ := by
  refine ⟨fun n : ℕ => n, ?_⟩
  simp [StrictMonoOn]

theorem goal_2
    (s : List Char)
    (t : List Char)
    (j_1 : ℕ)
    (a_1 : j_1 ≤ t.length)
    (invariant_greedy_witness : ∃ (f : ℕ → ℕ), (∀ p < s.length, f p < j_1) ∧ StrictMonoOn f (Set.Iio s.length) ∧ (∀ p < s.length, s[p]?.getD 'A' = t[f p]?.getD 'A') ∧ ∀ p < s.length, ∀ (k : ℕ), (if p = OfNat.ofNat 0 then OfNat.ofNat 0 else f (p - OfNat.ofNat 1) + OfNat.ofNat 1) ≤ k → k < f p → ¬t[k]?.getD 'A' = s[p]?.getD 'A')
    : postcondition s t true := by
    intros; expose_names; try simp_all; try grind

theorem goal_3
    (s : List Char)
    (t : List Char)
    (i_1 : ℕ)
    (j_1 : ℕ)
    (if_neg : ¬i_1 = s.length)
    (a : i_1 ≤ s.length)
    (a_1 : j_1 ≤ t.length)
    (invariant_greedy_witness : ∃ (f : ℕ → ℕ), (∀ p < i_1, f p < j_1) ∧ StrictMonoOn f (Set.Iio i_1) ∧ (∀ p < i_1, s[p]?.getD 'A' = t[f p]?.getD 'A') ∧ (∀ p < i_1, ∀ (k : ℕ), (if p = OfNat.ofNat 0 then OfNat.ofNat 0 else f (p - OfNat.ofNat 1) + OfNat.ofNat 1) ≤ k → k < f p → ¬t[k]?.getD 'A' = s[p]?.getD 'A') ∧ (i_1 < s.length → ∀ (k : ℕ), (if i_1 = OfNat.ofNat 0 then OfNat.ofNat 0 else f (i_1 - OfNat.ofNat 1) + OfNat.ofNat 1) ≤ k → k < j_1 → ¬t[k]?.getD 'A' = s[i_1]?.getD 'A'))
    (done_1 : i_1 < s.length → t.length ≤ j_1)
    : postcondition s t false := by
  unfold postcondition
  constructor
  · intro h
    cases h
  · intro hsub
    have : False := by
      unfold subseqByIndex at hsub
      rcases hsub with ⟨g, hg_lt, hg_mono, hg_match⟩

      have hi1 : i_1 < s.length := Nat.lt_of_le_of_ne a if_neg
      have hj_ge : t.length ≤ j_1 := done_1 hi1
      have hj : j_1 = t.length := le_antisymm a_1 hj_ge

      rcases invariant_greedy_witness with ⟨f, hf_lt, hf_strict, hf_match', hf_min, hf_noNext⟩

      -- Convert between `get!` and `getD`-style indexing when the index is in-bounds.
      have getD_eq_get! {l : List Char} {n : Nat} (hn : n < l.length) :
          l[n]?.getD 'A' = l.get! n := by
        have hA : l[n]?.getD 'A' = l[n]'hn := by
          -- `getD` on `get?` reduces to the in-bounds element.
          simpa [List.getD_getElem?, hn] using (List.getD_getElem? (l := l) (i := n) (d := ('A' : Char)))
        have hdef : l.get! n = l[n]'hn := by
          calc
            l.get! n = l.getD n default := by
              simpa using (List.get!_eq_getD (l := l) n)
            _ = l[n]?.getD (default : Char) := by
              simpa using (List.getD_eq_getD_getElem? (l := l) (n := n) (d := (default : Char)))
            _ = l[n]'hn := by
              simpa [List.getD_getElem?, hn] using
                (List.getD_getElem? (l := l) (i := n) (d := (default : Char)))
        simpa [hdef] using hA

      -- Any subsequence witness `g` must place the p-th match no earlier than the greedy `f p`.
      have hfg : ∀ p, p < i_1 → f p ≤ g p := by
        intro p hp
        induction p with
        | zero =>
            by_contra hle
            have hlt : g 0 < f 0 := Nat.lt_of_not_ge hle
            have hslen_pos : 0 < s.length := Nat.lt_trans hp hi1
            have hg0_lt : g 0 < t.length := hg_lt 0 hslen_pos
            have hEq0 : t[g 0]?.getD 'A' = s[0]?.getD 'A' := by
              calc
                t[g 0]?.getD 'A' = t.get! (g 0) := getD_eq_get! (l := t) (n := g 0) hg0_lt
                _ = s.get! 0 := by
                  simpa using (hg_match 0 hslen_pos).symm
                _ = s[0]?.getD 'A' := (getD_eq_get! (l := s) (n := 0) hslen_pos).symm
            have hNe0 : ¬t[g 0]?.getD 'A' = s[0]?.getD 'A' := by
              simpa using (hf_min 0 hp (g 0) (by simp) hlt)
            exact hNe0 hEq0
        | succ p ih =>
            have hp' : p < i_1 := Nat.lt_of_succ_lt hp
            have ih' : f p ≤ g p := ih hp'
            by_contra hle
            have hlt : g (p + 1) < f (p + 1) := Nat.lt_of_not_ge hle
            have hp_s : p < s.length := Nat.lt_trans hp' hi1
            have hp1_s : p + 1 < s.length := Nat.lt_trans hp hi1
            have hg_step_lt : g p < g (p + 1) := hg_mono hp_s hp1_s (Nat.lt_succ_self p)
            have hg_step : g p + 1 ≤ g (p + 1) := Nat.succ_le_of_lt hg_step_lt
            have hstart : f p + 1 ≤ g (p + 1) := le_trans (Nat.succ_le_succ ih') hg_step
            have hg1_lt : g (p + 1) < t.length := hg_lt (p + 1) hp1_s
            have hEq1 : t[g (p + 1)]?.getD 'A' = s[p + 1]?.getD 'A' := by
              calc
                t[g (p + 1)]?.getD 'A' = t.get! (g (p + 1)) :=
                  getD_eq_get! (l := t) (n := g (p + 1)) hg1_lt
                _ = s.get! (p + 1) := by
                  simpa using (hg_match (p + 1) hp1_s).symm
                _ = s[p + 1]?.getD 'A' := (getD_eq_get! (l := s) (n := (p + 1)) hp1_s).symm
            have hNe1 : ¬t[g (p + 1)]?.getD 'A' = s[p + 1]?.getD 'A' := by
              simpa using (hf_min (p + 1) hp (g (p + 1)) (by simpa using hstart) hlt)
            exact hNe1 hEq1

      -- `g i_1` must lie after the previous greedy match, in the scanned prefix.
      have hstart_le :
          (if i_1 = 0 then 0 else f (i_1 - 1) + 1) ≤ g i_1 := by
        by_cases hi0 : i_1 = 0
        · subst hi0
          simp
        · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
          have hn_lt : n < n + 1 := Nat.lt_succ_self n
          have hfn : f n ≤ g n := hfg n hn_lt
          have hn_s : n < s.length := Nat.lt_trans hn_lt hi1
          have hn1_s : n + 1 < s.length := hi1
          have hg_step_lt : g n < g (n + 1) := hg_mono hn_s hn1_s (Nat.lt_succ_self n)
          have hg_step : g n + 1 ≤ g (n + 1) := Nat.succ_le_of_lt hg_step_lt
          have : f n + 1 ≤ g (n + 1) := le_trans (Nat.succ_le_succ hfn) hg_step
          simpa

      have hgi_lt_j : g i_1 < j_1 := by
        simpa [hj] using (hg_lt i_1 hi1)

      have hNeNext : ¬t[g i_1]?.getD 'A' = s[i_1]?.getD 'A' :=
        hf_noNext hi1 (g i_1) (by simpa using hstart_le) hgi_lt_j

      have hgi_lt : g i_1 < t.length := hg_lt i_1 hi1
      have hEqNext : t[g i_1]?.getD 'A' = s[i_1]?.getD 'A' := by
        calc
          t[g i_1]?.getD 'A' = t.get! (g i_1) := getD_eq_get! (l := t) (n := g i_1) hgi_lt
          _ = s.get! i_1 := by
            simpa using (hg_match i_1 hi1).symm
          _ = s[i_1]?.getD 'A' := (getD_eq_get! (l := s) (n := i_1) hi1).symm

      exact hNeNext hEqNext
    exact False.elim this


prove_correct IsSubsequence by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at *); try (conv => congr <;> simp) ; try expose_names)
  exact (goal_0 s t i j invariant_greedy_witness a_2 if_pos)
  exact (goal_1)
  exact (goal_2 s t j_1 a_1 invariant_greedy_witness)
  exact (goal_3 s t i_1 j_1 if_neg a a_1 invariant_greedy_witness done_1)
end Proof
