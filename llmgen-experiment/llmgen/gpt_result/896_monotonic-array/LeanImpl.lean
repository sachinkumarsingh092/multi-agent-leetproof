import Lean
import Mathlib.Tactic
import Velvet.Std

set_option maxHeartbeats 10000000

section Specs
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false

/- Problem Description
    896. Monotonic Array: decide whether an integer array is monotone increasing or monotone decreasing.
    **Important: complexity should be O(n) time and O(1) space**
    Natural language breakdown:
    1. Input is an array of integers `nums`.
    2. `nums` is monotone increasing if for all indices i and j with i ≤ j, we have nums[i] ≤ nums[j].
    3. `nums` is monotone decreasing if for all indices i and j with i ≤ j, we have nums[i] ≥ nums[j].
    4. The array is monotonic if it is monotone increasing or monotone decreasing.
    5. The function returns `true` exactly when the input array is monotonic, otherwise `false`.
    6. Empty arrays and single-element arrays are monotonic (both conditions hold vacuously).
-/

-- A property-based definition of monotone increasing over Array Int using Nat indices.
-- We quantify over all i ≤ j that are valid indices.
def monotoneIncreasing (nums : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < nums.size → j < nums.size → i ≤ j → nums[i]! ≤ nums[j]!

-- A property-based definition of monotone decreasing over Array Int using Nat indices.
def monotoneDecreasing (nums : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < nums.size → j < nums.size → i ≤ j → nums[i]! ≥ nums[j]!

def monotonic (nums : Array Int) : Prop :=
  monotoneIncreasing nums ∨ monotoneDecreasing nums

def precondition (nums : Array Int) : Prop :=
  True

def postcondition (nums : Array Int) (result : Bool) : Prop :=
  (result = true ↔ monotonic nums) ∧
  (result = false ↔ ¬ monotonic nums)
end Specs

section Impl
def implementation (nums : Array Int) : Bool :=
  let n := nums.size
  if n ≤ 1 then
    true
  else
    let init : (Bool × Bool) × Int := ((true, true), nums[0]!)
    let step := fun (st : (Bool × Bool) × Int) (x : Int) =>
      let incOk := st.1.1
      let decOk := st.1.2
      let prev := st.2
      let incOk' := incOk && (prev ≤ x)
      let decOk' := decOk && (prev ≥ x)
      ((incOk', decOk'), x)
    let st := nums.foldl step init
    st.1.1 || st.1.2
end Impl

section TestCases
-- Test case 1: Example 1
-- Input: [1,2,2,3]
-- Output: true
def test1_nums : Array Int := #[1, 2, 2, 3]
def test1_Expected : Bool := true

-- Test case 2: Example 2
-- Input: [6,5,4,4]
-- Output: true
def test2_nums : Array Int := #[6, 5, 4, 4]
def test2_Expected : Bool := true

-- Test case 3: Example 3
-- Input: [1,3,2]
-- Output: false
def test3_nums : Array Int := #[1, 3, 2]
def test3_Expected : Bool := false

-- Test case 4: Empty array (vacuously monotonic)
def test4_nums : Array Int := #[]
def test4_Expected : Bool := true

-- Test case 5: Singleton array (vacuously monotonic)
def test5_nums : Array Int := #[0]
def test5_Expected : Bool := true

-- Test case 6: Constant array (both increasing and decreasing)
def test6_nums : Array Int := #[2, 2, 2, 2]
def test6_Expected : Bool := true

-- Test case 7: Strictly increasing with negatives and positives (covers -1,0,1)
def test7_nums : Array Int := #[-1, 0, 1]
def test7_Expected : Bool := true

-- Test case 8: Strictly decreasing with negatives and positives (covers 1,0,-1)
def test8_nums : Array Int := #[1, 0, -1]
def test8_Expected : Bool := true

-- Test case 9: Not monotonic due to a rise then fall
def test9_nums : Array Int := #[1, 2, 1, 2]
def test9_Expected : Bool := false
end TestCases

section Assertions
-- Test case 1
#assert_same_evaluation #[(implementation test1_nums), test1_Expected]

-- Test case 2
#assert_same_evaluation #[(implementation test2_nums), test2_Expected]

-- Test case 3
#assert_same_evaluation #[(implementation test3_nums), test3_Expected]

-- Test case 4
#assert_same_evaluation #[(implementation test4_nums), test4_Expected]

-- Test case 5
#assert_same_evaluation #[(implementation test5_nums), test5_Expected]

-- Test case 6
#assert_same_evaluation #[(implementation test6_nums), test6_Expected]

-- Test case 7
#assert_same_evaluation #[(implementation test7_nums), test7_Expected]

-- Test case 8
#assert_same_evaluation #[(implementation test8_nums), test8_Expected]

-- Test case 9
#assert_same_evaluation #[(implementation test9_nums), test9_Expected]
end Assertions

section Proof
theorem correctness_goal
    (nums : Array Int)
    (h_precond : precondition nums)
    : postcondition nums (implementation nums) := by
  unfold precondition at h_precond
  unfold postcondition
  by_cases hsz : nums.size ≤ 1
  ·
    have himpl : implementation nums = true := by
      simp [implementation, hsz]
    have hmono : monotonic nums := by
      left
      intro i j hi hj hij
      have hi1 : i < 1 := lt_of_lt_of_le hi hsz
      have hj1 : j < 1 := lt_of_lt_of_le hj hsz
      have hi0 : i = 0 := by
        have : i ≤ 0 := Nat.lt_succ_iff.mp hi1
        exact Nat.eq_zero_of_le_zero this
      have hj0 : j = 0 := by
        have : j ≤ 0 := Nat.lt_succ_iff.mp hj1
        exact Nat.eq_zero_of_le_zero this
      subst hi0; subst hj0
      exact le_rfl
    refine And.intro ?_ ?_
    · constructor
      · intro _; exact hmono
      · intro _; exact himpl
    · constructor
      · intro hfalse
        have : (true : Bool) = false := by simpa [himpl] using hfalse
        cases this
      · intro hnot
        exact False.elim (hnot hmono)
  ·
    have getBang_eq_get : ∀ (i : Nat) (hi : i < nums.size), nums[i]! = nums[i] := by
      intro i hi
      have hopt : nums[i]? = some nums[i] := by
        simp [Array.getElem?_eq_getElem, hi]
      calc
        nums[i]! = nums.getD i default := by
          simp [Array.getElem!_eq_getD]
        _ = (nums[i]?).getD default := by
          simp [Array.getD_eq_getD_getElem?]
        _ = nums[i] := by
          simp [hopt]

    let init : (Bool × Bool) × Int := ((true, true), nums[0]!)
    let step : (Bool × Bool) × Int → Int → (Bool × Bool) × Int := fun st x =>
      let incOk := st.1.1
      let decOk := st.1.2
      let prev := st.2
      let incOk' := incOk && (prev ≤ x)
      let decOk' := decOk && (prev ≥ x)
      ((incOk', decOk'), x)
    let st := nums.foldl step init

    let IncPrefix : Nat → Prop := fun m => ∀ k : Nat, k + 1 < m → nums[k]! ≤ nums[k+1]!
    let DecPrefix : Nat → Prop := fun m => ∀ k : Nat, k + 1 < m → nums[k]! ≥ nums[k+1]!

    let motive : Nat → ((Bool × Bool) × Int) → Prop := fun m s =>
      (s.1.1 = true ↔ IncPrefix m) ∧
      (s.1.2 = true ↔ DecPrefix m) ∧
      (s.2 = nums[Nat.pred m]!)

    have hxFin : ∀ i : Fin nums.size, nums[i] = nums[i.1]! := by
      intro i
      have : nums[i.1]! = nums[i.1] := getBang_eq_get i.1 i.2
      simpa using this.symm

    have h0 : motive 0 init := by
      simp [motive, IncPrefix, DecPrefix, init]

    have hf : ∀ i : Fin nums.size, ∀ b, motive i.1 b → motive (i.1 + 1) (step b nums[i]) := by
      intro i b hb
      rcases b with ⟨⟨incOk, decOk⟩, prev⟩
      rcases hb with ⟨hinc, hdec, hprev⟩
      have hx : nums[i] = nums[i.1]! := hxFin i
      cases hidx : i.1 with
      | zero =>
          have hinc' : incOk = true ↔ IncPrefix 0 := by simpa [hidx] using hinc
          have hdec' : decOk = true ↔ DecPrefix 0 := by simpa [hidx] using hdec
          have hprev' : prev = nums[0]! := by simpa [hidx, Nat.pred] using hprev

          have hInc0 : IncPrefix 0 := by
            intro k hk
            cases Nat.not_lt_zero _ hk
          have hDec0 : DecPrefix 0 := by
            intro k hk
            cases Nat.not_lt_zero _ hk
          have hInc1 : IncPrefix 1 := by
            intro k hk
            have : False := by simpa using hk
            cases this
          have hDec1 : DecPrefix 1 := by
            intro k hk
            have : False := by simpa using hk
            cases this

          have hinc0 : incOk = true := hinc'.mpr hInc0
          have hdec0 : decOk = true := hdec'.mpr hDec0
          have hle : prev ≤ nums[i] := by
            simpa [hprev', hx, hidx] using (le_rfl : (nums[0]!) ≤ nums[0]!)
          have hge : prev ≥ nums[i] := by
            simpa [hprev', hx, hidx] using (le_rfl : (nums[0]!) ≥ nums[0]!)

          refine ⟨?_, ?_, ?_⟩
          · constructor
            · intro _; exact hInc1
            · intro _
              -- show new incOk is true
              -- simplify goal to and over decide
              have : incOk = true ∧ prev ≤ nums[i] := ⟨hinc0, hle⟩
              -- `simp` turns `prev ≤ nums[i]` into `decide ... = true`
              simpa [step, Bool.and_eq_true_iff, this]
          · constructor
            · intro _; exact hDec1
            · intro _
              have : decOk = true ∧ prev ≥ nums[i] := ⟨hdec0, hge⟩
              simpa [step, Bool.and_eq_true_iff, this]
          · -- prev
            simpa [step, hidx, hx, Nat.pred]
      | succ k =>
          have hinc' : incOk = true ↔ IncPrefix (k+1) := by simpa [hidx] using hinc
          have hdec' : decOk = true ↔ DecPrefix (k+1) := by simpa [hidx] using hdec
          have hprev' : prev = nums[k]! := by
            -- pred (k+1) = k
            simpa [hidx] using hprev
          have hxk : nums[i] = nums[k+1]! := by simpa [hidx] using hx

          have inc_succ : IncPrefix (k+2) ↔ (IncPrefix (k+1) ∧ nums[k]! ≤ nums[k+1]!) := by
            constructor
            · intro h
              refine ⟨?_, ?_⟩
              · intro t ht
                apply h t
                exact lt_trans ht (by simp)
              · simpa using h k (by simp)
            · rintro ⟨h1, hk⟩ t ht
              have hle : t ≤ k := by
                have : t.succ ≤ k.succ := (Nat.lt_succ_iff.mp ht)
                exact Nat.le_of_succ_le_succ this
              rcases lt_or_eq_of_le hle with hlt | rfl
              · apply h1 t
                exact Nat.succ_lt_succ hlt
              · simpa using hk
          have dec_succ : DecPrefix (k+2) ↔ (DecPrefix (k+1) ∧ nums[k]! ≥ nums[k+1]!) := by
            constructor
            · intro h
              refine ⟨?_, ?_⟩
              · intro t ht
                apply h t
                exact lt_trans ht (by simp)
              · simpa using h k (by simp)
            · rintro ⟨h1, hk⟩ t ht
              have hle : t ≤ k := by
                have : t.succ ≤ k.succ := (Nat.lt_succ_iff.mp ht)
                exact Nat.le_of_succ_le_succ this
              rcases lt_or_eq_of_le hle with hlt | rfl
              · apply h1 t
                exact Nat.succ_lt_succ hlt
              · simpa using hk

          refine ⟨?_, ?_, ?_⟩
          · -- incOk' iff
            constructor
            · intro h
              have hAnd : (incOk && (prev ≤ nums[i])) = true := by
                simpa [step] using h
              have hAnd' := (Bool.and_eq_true_iff).1 hAnd
              have hInc : incOk = true := hAnd'.1
              have hLe : prev ≤ nums[i] := by
                -- decide ... = true ↔ Prop
                simpa using hAnd'.2
              have hadj : IncPrefix (k+1) := hinc'.mp hInc
              have hk' : nums[k]! ≤ nums[k+1]! := by
                simpa [hprev', hxk] using hLe
              exact inc_succ.mpr ⟨hadj, hk'⟩
            · intro hadj2
              have hpair : IncPrefix (k+1) ∧ nums[k]! ≤ nums[k+1]! := inc_succ.mp hadj2
              have hInc : incOk = true := hinc'.mpr hpair.1
              have hLe : prev ≤ nums[i] := by
                simpa [hprev', hxk] using hpair.2
              have hAnd : (incOk && (prev ≤ nums[i])) = true := by
                have : incOk = true ∧ prev ≤ nums[i] := ⟨hInc, hLe⟩
                simpa [Bool.and_eq_true_iff, this]
              simpa [step] using hAnd
          · -- decOk' iff
            constructor
            · intro h
              have hAnd : (decOk && (prev ≥ nums[i])) = true := by
                simpa [step] using h
              have hAnd' := (Bool.and_eq_true_iff).1 hAnd
              have hDec : decOk = true := hAnd'.1
              have hGe : prev ≥ nums[i] := by
                simpa using hAnd'.2
              have hadj : DecPrefix (k+1) := hdec'.mp hDec
              have hk' : nums[k]! ≥ nums[k+1]! := by
                simpa [hprev', hxk] using hGe
              exact dec_succ.mpr ⟨hadj, hk'⟩
            · intro hadj2
              have hpair : DecPrefix (k+1) ∧ nums[k]! ≥ nums[k+1]! := dec_succ.mp hadj2
              have hDec : decOk = true := hdec'.mpr hpair.1
              have hGe : prev ≥ nums[i] := by
                simpa [hprev', hxk] using hpair.2
              have hAnd : (decOk && (prev ≥ nums[i])) = true := by
                have : decOk = true ∧ prev ≥ nums[i] := ⟨hDec, hGe⟩
                simpa [Bool.and_eq_true_iff, this]
              simpa [step] using hAnd
          · -- prev
            simpa [step, hidx, hxk, Nat.pred]

    have hmot : motive nums.size st := by
      have := Array.foldl_induction (motive := motive) (init := init) (h0 := h0) (f := step) (hf := hf)
      simpa [st] using this

    rcases hmot with ⟨hInc, hDec, hPrev⟩

    have adjLE_to_monoInc : (IncPrefix nums.size) → monotoneIncreasing nums := by
      intro hadj
      intro i j hi hj hij
      have hchain : ∀ n, i ≤ n → n < nums.size → nums[i]! ≤ nums[n]! := by
        intro n hin
        refine (Nat.le_induction (m := i)
          (P := fun n hn => n < nums.size → nums[i]! ≤ nums[n]!)
          (base := by intro _; exact le_rfl)
          (succ := ?_) n hin)
        intro n hn ih hn1
        have hnlt : n < nums.size := Nat.lt_of_succ_lt hn1
        have h1 : nums[i]! ≤ nums[n]! := ih hnlt
        have h2 : nums[n]! ≤ nums[n+1]! := hadj n hn1
        exact le_trans h1 h2
      exact hchain j hij hj

    have adjGE_to_monoDec : (DecPrefix nums.size) → monotoneDecreasing nums := by
      intro hadj
      intro i j hi hj hij
      have hchain : ∀ n, i ≤ n → n < nums.size → nums[i]! ≥ nums[n]! := by
        intro n hin
        refine (Nat.le_induction (m := i)
          (P := fun n hn => n < nums.size → nums[i]! ≥ nums[n]!)
          (base := by intro _; exact le_rfl)
          (succ := ?_) n hin)
        intro n hn ih hn1
        have hnlt : n < nums.size := Nat.lt_of_succ_lt hn1
        have h1 : nums[i]! ≥ nums[n]! := ih hnlt
        have h2 : nums[n]! ≥ nums[n+1]! := hadj n hn1
        exact ge_trans h1 h2
      exact hchain j hij hj

    have monoInc_to_adjLE : monotoneIncreasing nums → IncPrefix nums.size := by
      intro hI k hk
      have hk' : k < nums.size := Nat.lt_of_succ_lt hk
      exact hI k (k+1) hk' hk (Nat.le_succ k)

    have monoDec_to_adjGE : monotoneDecreasing nums → DecPrefix nums.size := by
      intro hD k hk
      have hk' : k < nums.size := Nat.lt_of_succ_lt hk
      exact hD k (k+1) hk' hk (Nat.le_succ k)

    have himpl_eq : implementation nums = (st.1.1 || st.1.2) := by
      simp [implementation, hsz, init, step, st]

    have htrue : implementation nums = true ↔ monotonic nums := by
      rw [himpl_eq]
      constructor
      · intro hor
        have hor' : st.1.1 = true ∨ st.1.2 = true := (Bool.or_eq_true_iff).1 hor
        cases hor' with
        | inl hstInc =>
            have hadj : IncPrefix nums.size := (hInc.mp hstInc)
            exact Or.inl (adjLE_to_monoInc hadj)
        | inr hstDec =>
            have hadj : DecPrefix nums.size := (hDec.mp hstDec)
            exact Or.inr (adjGE_to_monoDec hadj)
      · intro hmono
        rcases hmono with hI | hD
        · have hadj : IncPrefix nums.size := monoInc_to_adjLE hI
          have hstInc : st.1.1 = true := (hInc.mpr hadj)
          exact (Bool.or_eq_true_iff).2 (Or.inl hstInc)
        · have hadj : DecPrefix nums.size := monoDec_to_adjGE hD
          have hstDec : st.1.2 = true := (hDec.mpr hadj)
          exact (Bool.or_eq_true_iff).2 (Or.inr hstDec)

    have hfalse : implementation nums = false ↔ ¬ monotonic nums := by
      constructor
      · intro hf
        intro hmono
        have ht : implementation nums = true := htrue.mpr hmono
        have : (true : Bool) = false := by simpa [ht] using hf
        cases this
      · intro hnot
        cases hb : implementation nums with
        | false =>
            rfl
        | true =>
            have hmono : monotonic nums := htrue.mp hb
            exact False.elim (hnot hmono)

    exact And.intro htrue hfalse
end Proof
