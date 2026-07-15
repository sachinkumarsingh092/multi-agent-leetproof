import Velvet.Std
import Extensions.Tactics
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false
set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

/- Problem Description
    383. Ransom Note: decide whether one note can be constructed from the letters of a magazine.
    **Important: complexity should be O(m + n) time and O(1) space**
    Natural language breakdown:
    1. Inputs are two sequences of characters: ransomNote and magazine.
    2. A character from magazine can be used at most once when constructing the ransomNote.
    3. Construction is possible exactly when every character occurs in magazine at least as many times as it occurs in ransomNote.
    4. The function returns true iff construction is possible; otherwise it returns false.
    5. The empty ransom note is always constructible from any magazine.
-/

section Specs
-- Helper: multiset-style availability condition via per-character counts.
-- Mathlib provides `List.count` for decidable equality types.
def canConstructProp (ransomNote : List Char) (magazine : List Char) : Prop :=
  ∀ c : Char, ransomNote.count c ≤ magazine.count c

def precondition (ransomNote : List Char) (magazine : List Char) : Prop :=
  True

def postcondition (ransomNote : List Char) (magazine : List Char) (result : Bool) : Prop :=
  (result = true ↔ canConstructProp ransomNote magazine)
end Specs

section Impl
method RansomNote (ransomNote : List Char) (magazine : List Char)
  return (result : Bool)
  require precondition ransomNote magazine
  ensures postcondition ransomNote magazine result
  do
  -- Specification is over all `Char`, so we cannot assume a small fixed alphabet.
  -- We implement the spec directly using `List.count`.
  let mut ok : Bool := true
  let mut rs : List Char := ransomNote

  while ok ∧ rs ≠ []
    -- rs is always a suffix of the original ransomNote.
    invariant "inv_suffix" (∃ ps : List Char, ps ++ rs = ransomNote)
    -- If ok is still true, then every character that has appeared in the processed prefix ps
    -- has its *full* ransomNote count bounded by the magazine count (checked at its first appearance).
    invariant "inv_ok_checked" (∃ ps : List Char, ps ++ rs = ransomNote ∧ (ok = true → ∀ c : Char, c ∈ ps → ransomNote.count c ≤ magazine.count c))
    -- If we ever set ok := false, we have found a concrete witness character that violates canConstructProp.
    invariant "inv_false_witness" (ok = false → ∃ c : Char, magazine.count c < ransomNote.count c)
    -- Once ok becomes false, the loop body forces rs := [] and keeps it that way.
    invariant "inv_false_rs_nil" (ok = false → rs = [])
    done_with (ok = false ∨ rs = [])
    decreasing rs.length
  do
    match rs with
    | [] =>
      rs := []
    | c :: cs =>
      if (rs.count c) ≤ (magazine.count c) then
        rs := cs
      else
        ok := false
        rs := []

  return ok
end Impl

section TestCases
-- Test case 1: Example 1: ransomNote = "a", magazine = "b" => false
def test1_ransomNote : List Char := ['a']
def test1_magazine : List Char := ['b']
def test1_Expected : Bool := false

-- Test case 2: Example 2: ransomNote = "aa", magazine = "ab" => false
def test2_ransomNote : List Char := ['a', 'a']
def test2_magazine : List Char := ['a', 'b']
def test2_Expected : Bool := false

-- Test case 3: Example 3: ransomNote = "aa", magazine = "aab" => true
def test3_ransomNote : List Char := ['a', 'a']
def test3_magazine : List Char := ['a', 'a', 'b']
def test3_Expected : Bool := true

-- Test case 4: Edge: empty ransom note, empty magazine => true
def test4_ransomNote : List Char := []
def test4_magazine : List Char := []
def test4_Expected : Bool := true

-- Test case 5: Edge: empty ransom note, nonempty magazine => true
def test5_ransomNote : List Char := []
def test5_magazine : List Char := ['x', 'y']
def test5_Expected : Bool := true

-- Test case 6: Edge: nonempty ransom note, empty magazine => false
def test6_ransomNote : List Char := ['z']
def test6_magazine : List Char := []
def test6_Expected : Bool := false

-- Test case 7: Exact match with repeats => true
def test7_ransomNote : List Char := ['a', 'b', 'c', 'a']
def test7_magazine : List Char := ['a', 'b', 'c', 'a']
def test7_Expected : Bool := true

-- Test case 8: Insufficient multiplicity for one letter => false
def test8_ransomNote : List Char := ['a', 'b', 'b']
def test8_magazine : List Char := ['b', 'a']
def test8_Expected : Bool := false

-- Test case 9: Magazine has extra letters and permuted order => true
def test9_ransomNote : List Char := ['c', 'a', 't']
def test9_magazine : List Char := ['t', 'a', 'c', 'h', 'e', 'r']
def test9_Expected : Bool := true
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((RansomNote test1_ransomNote test1_magazine).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((RansomNote test2_ransomNote test2_magazine).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((RansomNote test3_ransomNote test3_magazine).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((RansomNote test4_ransomNote test4_magazine).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((RansomNote test5_ransomNote test5_magazine).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((RansomNote test6_ransomNote test6_magazine).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((RansomNote test7_ransomNote test7_magazine).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((RansomNote test8_ransomNote test8_magazine).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((RansomNote test9_ransomNote test9_magazine).run), DivM.res test9_Expected ]
end Assertions

section Pbt
velvet_plausible_test RansomNote (config := { maxMs := some 20000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000

theorem goal_0
    (ransomNote : List Char)
    (i : Char)
    (i_1 : List Char)
    (invariant_inv_suffix : ∃ ps, ps ++ i :: i_1 = ransomNote)
    : ∃ ps, ps ++ i_1 = ransomNote := by
    rcases invariant_inv_suffix with ⟨ps, hps⟩
    refine ⟨ps ++ [i], ?_⟩
    -- reassociate and use the witness equality
    calc
      (ps ++ [i]) ++ i_1 = ps ++ ([i] ++ i_1) := by
        simp [List.append_assoc]
      _ = ps ++ (i :: i_1) := by
        simp
      _ = ransomNote := by
        simpa using hps

theorem goal_1
    (ransomNote : List Char)
    (magazine : List Char)
    (i : Char)
    (i_1 : List Char)
    (if_pos : List.count i i_1 + OfNat.ofNat 1 ≤ List.count i magazine)
    (invariant_inv_ok_checked : ∃ ps, ps ++ i :: i_1 = ransomNote ∧ ∀ c ∈ ps, List.count c ransomNote ≤ List.count c magazine)
    : ∃ ps, ps ++ i_1 = ransomNote ∧ ∀ c ∈ ps, List.count c ransomNote ≤ List.count c magazine := by
  rcases invariant_inv_ok_checked with ⟨ps0, hps0, hbound⟩
  refine ⟨ps0 ++ [i], ?_, ?_⟩
  · calc
      (ps0 ++ [i]) ++ i_1 = ps0 ++ ([i] ++ i_1) := by
        simp [List.append_assoc]
      _ = ps0 ++ (i :: i_1) := by simp
      _ = ransomNote := by simpa [hps0]
  · intro c hc
    have hmem : c ∈ ps0 ∨ c ∈ [i] := by
      simpa using (List.mem_append.mp hc)
    cases hmem with
    | inl hc0 =>
        exact hbound c hc0
    | inr hci =>
        have hcEq : c = i := by
          simpa using (List.mem_singleton.mp hci)
        subst c
        by_cases hi : i ∈ ps0
        · exact hbound i hi
        · have h0 : List.count i ps0 = 0 := List.count_eq_zero_of_not_mem hi
          have hleft : List.count i (ps0 ++ (i :: i_1)) = List.count i i_1 + 1 := by
            simp [List.count_append, h0, List.count_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
          have hle : List.count i (ps0 ++ (i :: i_1)) ≤ List.count i magazine := by
            have : List.count i i_1 + 1 ≤ List.count i magazine := by
              simpa using if_pos
            simpa [hleft] using this
          simpa [hps0] using hle

theorem goal_2
    (ransomNote : List Char)
    (magazine : List Char)
    (i : Bool)
    (rs_1 : List Char)
    (invariant_inv_false_witness : i = false → ∃ c, List.count c magazine < List.count c ransomNote)
    (invariant_inv_ok_checked : ∃ ps, ps ++ rs_1 = ransomNote ∧ (i = true → ∀ c ∈ ps, List.count c ransomNote ≤ List.count c magazine))
    (done_1 : i = false ∨ rs_1 = [])
    : postcondition ransomNote magazine i := by
  unfold postcondition canConstructProp
  rcases done_1 with hiFalse | hrs
  · -- case i = false
    constructor
    · intro hiTrue
      -- contradiction, hence anything follows
      have : False := by
        -- simp turns this into `False` because it becomes `false = true`
        simpa [hiFalse] using hiTrue
      exact False.elim this
    · intro hall
      -- show i = true; contradiction from witness
      have : False := by
        rcases invariant_inv_false_witness hiFalse with ⟨c, hwit⟩
        have hle : List.count c ransomNote ≤ List.count c magazine := hall c
        have : List.count c magazine < List.count c magazine := Nat.lt_of_lt_of_le hwit hle
        exact (Nat.lt_irrefl _ this)
      exact False.elim this
  · -- case rs_1 = []
    constructor
    · intro hiTrue
      rcases invariant_inv_ok_checked with ⟨ps, hps, hchecked⟩
      have hps' : ps = ransomNote := by
        simpa [hrs] using hps
      have hall_mem : ∀ c ∈ ransomNote, List.count c ransomNote ≤ List.count c magazine := by
        have hall_mem_ps : ∀ c ∈ ps, List.count c ransomNote ≤ List.count c magazine := hchecked hiTrue
        simpa [hps'] using hall_mem_ps
      intro c
      by_cases hc : c ∈ ransomNote
      · exact hall_mem c hc
      · have hcount0 : List.count c ransomNote = 0 := List.count_eq_zero_of_not_mem hc
        simpa [hcount0] using (Nat.zero_le (List.count c magazine))
    · intro hcan
      -- canConstructProp implies ok cannot be false (else we'd have a witness contradiction)
      cases hi : i with
      | false =>
          rcases invariant_inv_false_witness hi with ⟨c, hwit⟩
          have hle : List.count c ransomNote ≤ List.count c magazine := hcan c
          have : List.count c magazine < List.count c magazine := Nat.lt_of_lt_of_le hwit hle
          exact (False.elim (Nat.lt_irrefl _ this))
      | true =>
          rfl


prove_correct RansomNote by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at *); try (conv => congr <;> simp) ; try expose_names)
  exact (goal_0 ransomNote i i_1 invariant_inv_suffix)
  exact (goal_1 ransomNote magazine i i_1 if_pos invariant_inv_ok_checked)
  exact (goal_2 ransomNote magazine i rs_1 invariant_inv_false_witness invariant_inv_ok_checked done_1)
end Proof
