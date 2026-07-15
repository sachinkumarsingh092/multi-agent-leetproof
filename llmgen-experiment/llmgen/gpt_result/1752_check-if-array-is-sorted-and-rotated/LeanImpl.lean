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
    1752. Check if Array Is Sorted and Rotated: decide whether an array can be obtained by rotating a non-decreasingly sorted array.
    **Important: complexity should be O(n) time and O(1) space**
    Natural language breakdown:
    1. We are given an array `nums` of integers; duplicates are allowed.
    2. A non-decreasingly sorted array has no adjacent decrease: for each valid i, A[i] ≤ A[i+1].
    3. Rotating an array by x positions shifts elements cyclically; rotation by 0 leaves the array unchanged.
    4. The input `nums` is valid iff there exists some rotation of `nums` that is non-decreasing.
    5. Equivalent circular characterization: scanning the array cyclically, there is at most one index i where nums[i] > nums[(i+1) mod n].
    6. Arrays of length 0 or 1 are always considered sorted-and-rotated.
-/

-- A “drop” is a strict decrease from an element to its cyclic successor.
-- We define it as a Prop so it can be used in specifications.

def isDrop (nums : Array Int) (i : Nat) : Prop :=
  nums.size > 0 ∧ i < nums.size ∧ nums[(i + 1) % nums.size]! < nums[i]!

-- `rotSortedProp nums` holds exactly when `nums` is sorted-and-rotated in the sense of the problem.
-- Using the standard circular-drop characterization: at most one drop.

def rotSortedProp (nums : Array Int) : Prop :=
  nums.size ≤ 1 ∨ (∀ (i : Nat) (j : Nat), isDrop nums i → isDrop nums j → i = j)

-- No input constraints.

def precondition (nums : Array Int) : Prop :=
  True

def postcondition (nums : Array Int) (result : Bool) : Prop :=
  (result = true ↔ rotSortedProp nums) ∧
  (result = false ↔ ¬ rotSortedProp nums)
end Specs

section Impl
def implementation (nums : Array Int) : Bool :=
  let n := nums.size
  if h : n ≤ 1 then
    true
  else
    -- count strict decreases in the cyclic scan
    let rec go (i : Nat) (drops : Nat) : Bool :=
      if hlt : i < n then
        if drops > 1 then
          false
        else
          let a := nums[i]!
          let j := (i + 1) % n
          let b := nums[j]!
          let drops' := if b < a then drops + 1 else drops
          go (i + 1) drops'
      else
        drops ≤ 1
    go 0 0
end Impl

section TestCases
-- Test case 1: Example 1
-- nums = [3,4,5,1,2] -> true

def test1_nums : Array Int := #[3, 4, 5, 1, 2]

def test1_Expected : Bool := true

-- Test case 2: Example 2
-- nums = [2,1,3,4] -> false

def test2_nums : Array Int := #[2, 1, 3, 4]

def test2_Expected : Bool := false

-- Test case 3: Example 3
-- nums = [1,2,3] -> true

def test3_nums : Array Int := #[1, 2, 3]

def test3_Expected : Bool := true

-- Test case 4: Empty array (degenerate)

def test4_nums : Array Int := #[]

def test4_Expected : Bool := true

-- Test case 5: Singleton array (degenerate)

def test5_nums : Array Int := #[42]

def test5_Expected : Bool := true

-- Test case 6: All equal elements (duplicates; any rotation is the same)

def test6_nums : Array Int := #[7, 7, 7, 7]

def test6_Expected : Bool := true

-- Test case 7: Sorted but not rotated (0 rotation)

def test7_nums : Array Int := #[0, 0, 1, 2, 2, 5]

def test7_Expected : Bool := true

-- Test case 8: Rotated with duplicates, still valid
-- Original sorted: [1,1,2,3,3], rotate by 3 -> [3,3,1,1,2]

def test8_nums : Array Int := #[3, 3, 1, 1, 2]

def test8_Expected : Bool := true

-- Test case 9: Two drops in the cyclic scan -> invalid
-- Drops at 0: 3>1 and at 2: 2>0

def test9_nums : Array Int := #[3, 1, 2, 0]

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

section Pbt
method implementationPbt (nums : Array Int)
  return (result : Bool)
  require precondition nums
  ensures postcondition nums result
  do
  return (implementation nums)

velvet_plausible_test implementationPbt (config := { maxMs := some 20000 })
end Pbt

section Proof
theorem correctness_goal
    (nums : Array Int)
    : postcondition nums (implementation nums) := by
  classical
  unfold postcondition

  have ht : implementation nums = true ↔ rotSortedProp nums := by
    by_cases hsz : nums.size ≤ 1
    · simp [implementation, hsz, rotSortedProp]
    ·
      simp [implementation, hsz, rotSortedProp]
      set n : Nat := nums.size
      have hsz' : ¬ n ≤ 1 := by simpa [n] using hsz
      have h1lt : 1 < n := lt_of_not_ge (by simpa using hsz')
      have hnpos : 0 < n := Nat.lt_trans Nat.zero_lt_one h1lt

      let dropPred : Nat → Prop := fun k => nums[((k + 1) % n)]! < nums[k]!
      let AtMostOneFrom : Nat → Prop := fun start =>
        ∀ a b : Nat,
          start ≤ a → a < n →
          start ≤ b → b < n →
          dropPred a → dropPred b → a = b
      let NoDropFrom : Nat → Prop := fun start =>
        ∀ a : Nat, start ≤ a → a < n → ¬ dropPred a

      have go_two : ∀ i : Nat, implementation.go nums n i 2 = false := by
        intro i
        by_cases hi : i < n
        · conv_lhs => unfold implementation.go
          simp [hi]
        · conv_lhs => unfold implementation.go
          simp [hi]

      have sub_succ_add_one (k : Nat) (hk : k.succ ≤ n) : n - k.succ + 1 = n - k := by
        have hklt : k < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk
        have h1le : 1 ≤ n - k := Nat.succ_le_of_lt (Nat.sub_pos_of_lt hklt)
        rw [Nat.sub_succ]
        exact Nat.sub_add_cancel h1le

      have go_spec : ∀ k : Nat, k ≤ n →
          ((implementation.go nums n (n - k) 0 = true ↔ AtMostOneFrom (n - k)) ∧
           (implementation.go nums n (n - k) 1 = true ↔ NoDropFrom (n - k))) := by
        intro k hk
        induction k with
        | zero =>
            constructor
            · constructor
              · intro _
                intro a b ha hla hb hlb _ _
                exfalso
                exact (Nat.not_lt_of_ge ha hla)
              · intro _
                conv_lhs => unfold implementation.go
                have : ¬ (n < n) := Nat.lt_irrefl n
                simp [this]
            · constructor
              · intro _
                intro a ha hla _
                exfalso
                exact (Nat.not_lt_of_ge ha hla)
              · intro _
                conv_lhs => unfold implementation.go
                have : ¬ (n < n) := Nat.lt_irrefl n
                simp [this]
        | succ k ih =>
            have hk' : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
            have ihk := ih hk'
            set i : Nat := n - Nat.succ k
            have hi_lt : i < n := by
              have hsum : i + Nat.succ k = n := by
                simpa [i, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using (Nat.sub_add_cancel hk)
              have : i < i + Nat.succ k :=
                Nat.lt_add_of_pos_right (n := i) (k := Nat.succ k) (Nat.succ_pos k)
              simpa [hsum] using this
            have hi_succ : i + 1 = n - k := by
              simpa [i] using sub_succ_add_one k hk

            have atMostOne_drop (hdi : dropPred i) : AtMostOneFrom i ↔ NoDropFrom (i + 1) := by
              constructor
              · intro huniq a ha hla
                intro hda
                have hEq : i = a :=
                  huniq i a (Nat.le_refl _) hi_lt (Nat.le_trans (Nat.le_succ i) ha) hla hdi hda
                have hne : i ≠ a := by
                  exact Nat.ne_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self i) ha)
                exact hne hEq
              · intro hnodrop
                intro a b ha hla hb hlb hda hdb
                have haCase := Nat.eq_or_lt_of_le ha
                cases haCase with
                | inl haEq =>
                    subst haEq
                    have hbCase := Nat.eq_or_lt_of_le hb
                    cases hbCase with
                    | inl hbEq => simpa [hbEq]
                    | inr hbLt =>
                        have hb1 : i + 1 ≤ b := Nat.succ_le_of_lt hbLt
                        have : ¬ dropPred b := hnodrop b hb1 hlb
                        exact False.elim (this hdb)
                | inr haLt =>
                    have ha1 : i + 1 ≤ a := Nat.succ_le_of_lt haLt
                    have : ¬ dropPred a := hnodrop a ha1 hla
                    exact False.elim (this hda)

            have atMostOne_nodrop (hndi : ¬ dropPred i) : AtMostOneFrom i ↔ AtMostOneFrom (i + 1) := by
              constructor
              · intro huniq a b ha hla hb hlb hda hdb
                exact huniq a b (Nat.le_trans (Nat.le_succ i) ha) hla (Nat.le_trans (Nat.le_succ i) hb) hlb hda hdb
              · intro huniq
                intro a b ha hla hb hlb hda hdb
                have haCase := Nat.eq_or_lt_of_le ha
                have hbCase := Nat.eq_or_lt_of_le hb
                cases haCase with
                | inl haEq =>
                    subst haEq
                    exact False.elim (hndi hda)
                | inr haLt =>
                    cases hbCase with
                    | inl hbEq =>
                        subst hbEq
                        exact False.elim (hndi hdb)
                    | inr hbLt =>
                        have ha1 : i + 1 ≤ a := Nat.succ_le_of_lt haLt
                        have hb1 : i + 1 ≤ b := Nat.succ_le_of_lt hbLt
                        exact huniq a b ha1 hla hb1 hlb hda hdb

            have nodrop_nodrop (hndi : ¬ dropPred i) : NoDropFrom i ↔ NoDropFrom (i + 1) := by
              constructor
              · intro hnodrop a ha hla
                exact hnodrop a (Nat.le_trans (Nat.le_succ i) ha) hla
              · intro hnodrop a ha hla
                have haCase := Nat.eq_or_lt_of_le ha
                cases haCase with
                | inl hEq =>
                    subst hEq
                    exact hndi
                | inr hlt =>
                    have ha1 : i + 1 ≤ a := Nat.succ_le_of_lt hlt
                    exact hnodrop a ha1 hla

            constructor
            · -- drops 0
              have ih0 : implementation.go nums n (i + 1) 0 = true ↔ AtMostOneFrom (i + 1) := by
                simpa [hi_succ.symm] using ihk.1
              have ih1 : implementation.go nums n (i + 1) 1 = true ↔ NoDropFrom (i + 1) := by
                simpa [hi_succ.symm] using ihk.2
              have : implementation.go nums n i 0 = true ↔ AtMostOneFrom i := by
                conv_lhs => unfold implementation.go
                simp [hi_lt]
                by_cases hcmp : nums[(i + 1) % n]! < nums[i]!
                · have hdi : dropPred i := by simpa [dropPred] using hcmp
                  have hrel : AtMostOneFrom i ↔ NoDropFrom (i + 1) := atMostOne_drop hdi
                  simpa [hcmp, hrel] using ih1
                · have hndi : ¬ dropPred i := by simpa [dropPred] using hcmp
                  have hrel : AtMostOneFrom i ↔ AtMostOneFrom (i + 1) := atMostOne_nodrop hndi
                  simpa [hcmp, hrel] using ih0
              simpa [i] using this
            · -- drops 1
              have ih1 : implementation.go nums n (i + 1) 1 = true ↔ NoDropFrom (i + 1) := by
                simpa [hi_succ.symm] using ihk.2
              have : implementation.go nums n i 1 = true ↔ NoDropFrom i := by
                conv_lhs => unfold implementation.go
                simp [hi_lt]
                by_cases hcmp : nums[(i + 1) % n]! < nums[i]!
                · have hdi : dropPred i := by simpa [dropPred] using hcmp
                  constructor
                  · intro htrue
                    have : implementation.go nums n (i + 1) 2 = true := by
                      simpa [hcmp] using htrue
                    simpa [go_two (i + 1)] using this
                  · intro hnodrop
                    have : ¬ dropPred i := hnodrop i (Nat.le_refl _) hi_lt
                    exact (this hdi).elim
                · have hndi : ¬ dropPred i := by simpa [dropPred] using hcmp
                  have hrel : NoDropFrom i ↔ NoDropFrom (i + 1) := nodrop_nodrop hndi
                  simpa [hcmp, hrel] using ih1
              simpa [i] using this

      have hgo0 : implementation.go nums n 0 0 = true ↔ AtMostOneFrom 0 := by
        simpa using (go_spec n (le_rfl)).1

      have huniq : AtMostOneFrom 0 ↔ (∀ (i j : Nat), isDrop nums i → isDrop nums j → i = j) := by
        constructor
        · intro hAM i j hi hj
          rcases hi with ⟨hnz, hi_lt, hid⟩
          rcases hj with ⟨_, hj_lt, hjd⟩
          have hid' : dropPred i := by simpa [dropPred, n] using hid
          have hjd' : dropPred j := by simpa [dropPred, n] using hjd
          exact hAM i j (Nat.zero_le _) (by simpa [n] using hi_lt)
            (Nat.zero_le _) (by simpa [n] using hj_lt) hid' hjd'
        · intro hQ a b ha hla hb hlb hda hdb
          have hnz : nums.size > 0 := by simpa [n] using hnpos
          have haDrop : isDrop nums a := by
            refine ⟨hnz, ?_, ?_⟩
            · simpa [n] using hla
            · simpa [dropPred, n] using hda
          have hbDrop : isDrop nums b := by
            refine ⟨hnz, ?_, ?_⟩
            · simpa [n] using hlb
            · simpa [dropPred, n] using hdb
          exact hQ a b haDrop hbDrop

      simpa [n] using (hgo0.trans huniq)

  have hf : implementation nums = false ↔ ¬ rotSortedProp nums := by
    constructor
    · intro hfalse
      intro hP
      have htrue : implementation nums = true := ht.mpr hP
      simpa [hfalse] using htrue
    · intro hnot
      cases hres : implementation nums with
      | false => simpa [hres]
      | true =>
          have hP : rotSortedProp nums := ht.mp (by simpa [hres])
          exact False.elim (hnot hP)

  exact ⟨ht, hf⟩
end Proof
