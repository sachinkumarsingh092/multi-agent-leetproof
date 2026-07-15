import Lean
import Mathlib.Tactic
import Velvet.Std

set_option maxHeartbeats 10000000

section Specs
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false

/- Problem Description
    459. Repeated Substring Pattern: decide whether a character sequence is a repetition of a shorter contiguous substring.
    **Important: complexity should be O(n^1.5) time and O(n) space**
    Natural language breakdown:
    1. Input is a sequence of characters s.
    2. We ask whether there exists a non-empty proper prefix length k (0 < k < n) such that n is a multiple of k.
    3. If such k exists, s is exactly repetitions of its first k characters iff every character at index i equals the character at index (i mod k).
    4. The output is a Bool: true exactly when such a k exists; otherwise false.
    5. For empty or length-1 inputs, the answer is false because no non-empty proper substring can repeat to form s.
-/

-- A property-based characterization of being a repetition of a shorter block.
-- We avoid constructing the repeated string; instead we specify periodicity by modular indexing.

def precondition (s : List Char) : Prop :=
  True

def postcondition (s : List Char) (result : Bool) : Prop :=
  let n := s.length
  (result = true) ↔
    (∃ k : Nat,
      0 < k ∧
      k < n ∧
      n % k = 0 ∧
      (∀ i : Nat, i < n → s[i]! = s[i % k]!))
end Specs

section Impl
def implementation (s : List Char) : Bool :=
  let n := s.length
  if n ≤ 1 then
    false
  else
    let checkPeriod (k : Nat) : Bool :=
      if k = 0 then
        false
      else
        (List.range n).all (fun i => s.get! i = s.get! (i % k))

    let limit : Nat := Nat.sqrt n

    -- collect all proper divisors k of n (1 ≤ k < n)
    let candidates : List Nat :=
      (List.range limit).foldl
        (fun acc d0 =>
          let d := d0 + 1
          if n % d = 0 then
            let q := n / d
            let acc := if d < n then d :: acc else acc
            let acc := if q < n ∧ q ≠ d then q :: acc else acc
            acc
          else
            acc)
        []

    candidates.any (fun k => (n % k = 0) && checkPeriod k)
end Impl

section TestCases
-- Test case 1: Example 1: "abab" -> true
def test1_s : List Char := ['a', 'b', 'a', 'b']
def test1_Expected : Bool := true

-- Test case 2: Example 2: "aba" -> false
def test2_s : List Char := ['a', 'b', 'a']
def test2_Expected : Bool := false

-- Test case 3: Example 3: "abcabcabcabc" -> true
def test3_s : List Char := ['a','b','c','a','b','c','a','b','c','a','b','c']
def test3_Expected : Bool := true

-- Test case 4: Edge case: empty input -> false
def test4_s : List Char := []
def test4_Expected : Bool := false

-- Test case 5: Edge case: single character -> false
def test5_s : List Char := ['x']
def test5_Expected : Bool := false

-- Test case 6: All same character, length 4 -> true ("a" repeated 4 times)
def test6_s : List Char := ['a','a','a','a']
def test6_Expected : Bool := true

-- Test case 7: Repetition with period 2, length 6 -> true ("ab" repeated 3 times)
def test7_s : List Char := ['a','b','a','b','a','b']
def test7_Expected : Bool := true

-- Test case 8: Not periodic though has some repeated prefix -> false
def test8_s : List Char := ['a','b','a','c']
def test8_Expected : Bool := false

-- Test case 9: Prime length with mixed chars -> false
def test9_s : List Char := ['a','b','c','a','b']
def test9_Expected : Bool := false
end TestCases

section Assertions
-- Test case 1
#assert_same_evaluation #[(implementation test1_s), test1_Expected]

-- Test case 2
#assert_same_evaluation #[(implementation test2_s), test2_Expected]

-- Test case 3
#assert_same_evaluation #[(implementation test3_s), test3_Expected]

-- Test case 4
#assert_same_evaluation #[(implementation test4_s), test4_Expected]

-- Test case 5
#assert_same_evaluation #[(implementation test5_s), test5_Expected]

-- Test case 6
#assert_same_evaluation #[(implementation test6_s), test6_Expected]

-- Test case 7
#assert_same_evaluation #[(implementation test7_s), test7_Expected]

-- Test case 8
#assert_same_evaluation #[(implementation test8_s), test8_Expected]

-- Test case 9
#assert_same_evaluation #[(implementation test9_s), test9_Expected]
end Assertions

section Proof
theorem correctness_goal
    (s : List Char)
    : postcondition s (implementation s) := by
  classical
  simp [precondition, postcondition, implementation]

  set n : Nat := s.length

  let step : List Nat → Nat → List Nat := fun acc d0 =>
    let d := d0 + 1
    if n % d = 0 then
      let q := n / d
      let acc := if d < n then d :: acc else acc
      let acc := if q < n ∧ q ≠ d then q :: acc else acc
      acc
    else
      acc

  set cand : List Nat := (List.range n.sqrt).foldl step []

  have mem_split {α : Type} [DecidableEq α] {a : α} {l : List α} (ha : a ∈ l) :
      ∃ l₁ l₂, l = l₁ ++ a :: l₂ := by
    induction l with
    | nil => cases ha
    | cons b l ih =>
        simp at ha
        rcases ha with rfl | ha
        · refine ⟨[], l, by simp⟩
        · rcases ih ha with ⟨l₁, l₂, rfl⟩
          refine ⟨b :: l₁, l₂, by simp [List.cons_append]⟩

  have mem_step_of_mem {x : Nat} {acc : List Nat} {d0 : Nat} (hx : x ∈ acc) : x ∈ step acc d0 := by
    by_cases hdiv : n % (d0 + 1) = 0
    · by_cases hdlt : d0 + 1 < n
      · by_cases hq : (n / (d0 + 1) < n ∧ n / (d0 + 1) ≠ d0 + 1)
        · simp [step, hdiv, hdlt, hq, hx]
        · simp [step, hdiv, hdlt, hq, hx]
      · by_cases hq : (n / (d0 + 1) < n ∧ n / (d0 + 1) ≠ d0 + 1)
        · simp [step, hdiv, hdlt, hq, hx]
        · simp [step, hdiv, hdlt, hq, hx]
    · simp [step, hdiv, hx]

  have mem_foldl_of_mem : ∀ (l : List Nat) (acc : List Nat) (x : Nat), x ∈ acc → x ∈ l.foldl step acc := by
    intro l
    induction l with
    | nil =>
        intro acc x hx
        simpa using hx
    | cons a l ih =>
        intro acc x hx
        simpa [List.foldl_cons] using ih (step acc a) x (mem_step_of_mem (x := x) (acc := acc) (d0 := a) hx)

  have step_lt : ∀ (acc : List Nat) (d0 : Nat), (∀ x ∈ acc, x < n) → (∀ x ∈ step acc d0, x < n) := by
    intro acc d0 hacc x hx
    by_cases hdiv : n % (d0 + 1) = 0
    · by_cases hdlt : d0 + 1 < n
      · by_cases hq : (n / (d0 + 1) < n ∧ n / (d0 + 1) ≠ d0 + 1)
        · simp [step, hdiv, hdlt, hq] at hx
          rcases hx with rfl | hx
          · exact hq.1
          rcases hx with rfl | hx
          · exact hdlt
          · exact hacc x hx
        · simp [step, hdiv, hdlt, hq] at hx
          rcases hx with rfl | hx
          · exact hdlt
          · exact hacc x hx
      · by_cases hq : (n / (d0 + 1) < n ∧ n / (d0 + 1) ≠ d0 + 1)
        · simp [step, hdiv, hdlt, hq] at hx
          rcases hx with rfl | hx
          · exact hq.1
          · exact hacc x hx
        · simp [step, hdiv, hdlt, hq] at hx
          exact hacc x hx
    · have hx' : x ∈ acc := by simpa [step, hdiv] using hx
      exact hacc x hx'

  have cand_lt : ∀ x : Nat, x ∈ cand → x < n := by
    intro x hx
    have fold_lt : ∀ (l : List Nat) (acc : List Nat), (∀ y ∈ acc, y < n) → (∀ y ∈ l.foldl step acc, y < n) := by
      intro l
      induction l with
      | nil =>
          intro acc hacc y hy
          simpa using hacc y hy
      | cons a l ih =>
          intro acc hacc y hy
          have hacc' : ∀ z ∈ step acc a, z < n := step_lt acc a hacc
          simpa [List.foldl_cons] using ih (step acc a) hacc' y hy
    have h0 : ∀ y ∈ ([] : List Nat), y < n := by intro y hy; cases hy
    exact (fold_lt (List.range n.sqrt) [] h0) x (by simpa [cand] using hx)

  have cand_complete : ∀ k : Nat, 0 < k → k < n → n % k = 0 → k ∈ cand := by
    intro k hkpos hklt hkmod
    have hk1 : 1 ≤ k := Nat.succ_le_of_lt hkpos
    have hkdvd : k ∣ n := Nat.dvd_of_mod_eq_zero hkmod
    let kp : Nat := n / k
    have hn_eq : k * kp = n := by
      simpa [kp, Nat.mul_comm] using (Nat.mul_div_cancel' (n := k) (m := n) hkdvd)
    have hkppos : 0 < kp := by
      have hnpos : 0 < n := lt_trans hkpos hklt
      have : kp ≠ 0 := by
        intro h0
        have : n = 0 := by
          simpa [kp, h0] using hn_eq.symm
        exact Nat.ne_of_gt hnpos this
      exact Nat.pos_of_ne_zero this

    by_cases hle : k ≤ kp
    · have hk_le_sqrt : k ≤ n.sqrt := by
        have hkk_le : k * k ≤ n := by
          have : k * k ≤ k * kp := Nat.mul_le_mul_left k hle
          simpa [hn_eq] using this
        exact (Nat.le_sqrt).2 hkk_le

      have hkpred_lt : k - 1 < k := by
        have : k - 1 < k - 1 + 1 := Nat.lt_succ_self (k - 1)
        simpa [Nat.succ_eq_add_one, Nat.sub_add_cancel hk1] using this
      have hd0_lt : k - 1 < n.sqrt := lt_of_lt_of_le hkpred_lt hk_le_sqrt
      have hd0_mem : k - 1 ∈ List.range n.sqrt := by
        simpa [List.mem_range] using hd0_lt

      rcases mem_split (α := Nat) (a := k - 1) (l := List.range n.sqrt) hd0_mem with ⟨l1, l2, hrange⟩
      let acc : List Nat := l1.foldl step []

      have hd : (k - 1) + 1 = k := by
        simpa [Nat.sub_add_cancel hk1]
      have hk_in_step : k ∈ step acc (k - 1) := by
        by_cases hq : (n / k < n ∧ n / k ≠ k)
        · simp [step, hd, hkmod, hklt, hq]
        · simp [step, hd, hkmod, hklt, hq]

      have hk_in_tail : k ∈ l2.foldl step (step acc (k - 1)) :=
        mem_foldl_of_mem l2 (step acc (k - 1)) k hk_in_step
      have hk_in_full : k ∈ (List.range n.sqrt).foldl step [] := by
        rw [hrange]
        simpa [List.foldl_append, acc, List.foldl_cons] using hk_in_tail
      simpa [cand] using hk_in_full

    · have hlt : kp < k := Nat.lt_of_not_ge hle
      have hk_ne_kp : k ≠ kp := Ne.symm (ne_of_lt hlt)

      have hkp_le_sqrt : kp ≤ n.sqrt := by
        have hkp_le : kp ≤ k := Nat.le_of_lt hlt
        have hmul : kp * kp ≤ kp * k := Nat.mul_le_mul_left kp hkp_le
        have hmulEq : kp * k = n := by simpa [hn_eq, Nat.mul_comm]
        have hkp2_le : kp * kp ≤ n := by simpa [hmulEq] using hmul
        exact (Nat.le_sqrt).2 hkp2_le

      have hkppred_lt : kp - 1 < kp := by
        have hk1' : 1 ≤ kp := Nat.succ_le_of_lt hkppos
        have : kp - 1 < kp - 1 + 1 := Nat.lt_succ_self (kp - 1)
        simpa [Nat.succ_eq_add_one, Nat.sub_add_cancel hk1'] using this
      have hd0_lt : kp - 1 < n.sqrt := lt_of_lt_of_le hkppred_lt hkp_le_sqrt
      have hd0_mem : kp - 1 ∈ List.range n.sqrt := by
        simpa [List.mem_range] using hd0_lt

      rcases mem_split (α := Nat) (a := kp - 1) (l := List.range n.sqrt) hd0_mem with ⟨l1, l2, hrange⟩
      let acc : List Nat := l1.foldl step []

      have hd : (kp - 1) + 1 = kp := by
        have hk1' : 1 ≤ kp := Nat.succ_le_of_lt hkppos
        simpa [Nat.sub_add_cancel hk1']

      have hq_eq : n / kp = k := by
        have : n = k * kp := by simpa [hn_eq, Nat.mul_comm] using hn_eq.symm
        exact Nat.div_eq_of_eq_mul_left hkppos this

      have hkpdvd : kp ∣ n := by
        refine ⟨k, ?_⟩
        simpa [hn_eq, Nat.mul_comm]
      have hmodkp : n % kp = 0 := Nat.mod_eq_zero_of_dvd hkpdvd

      have hk_in_step : k ∈ step acc (kp - 1) := by
        have hcond2 : k < n ∧ ¬k = kp := ⟨hklt, hk_ne_kp⟩
        simp [step, hd, hmodkp, hq_eq, hcond2]

      have hk_in_tail : k ∈ l2.foldl step (step acc (kp - 1)) :=
        mem_foldl_of_mem l2 (step acc (kp - 1)) k hk_in_step
      have hk_in_full : k ∈ (List.range n.sqrt).foldl step [] := by
        rw [hrange]
        simpa [List.foldl_append, acc, List.foldl_cons] using hk_in_tail
      simpa [cand] using hk_in_full

  constructor
  · intro h
    rcases h with ⟨hn1, x, hxmem, hxmod, hxne0, hxper⟩
    refine ⟨x, Nat.pos_of_ne_zero hxne0, cand_lt x (by simpa [cand] using hxmem), hxmod, hxper⟩
  · intro h
    rcases h with ⟨k, hkpos, hklt, hkmod, hkper⟩
    have hn1 : 1 < n := lt_of_le_of_lt (Nat.succ_le_of_lt hkpos) hklt
    refine ⟨hn1, k, cand_complete k hkpos hklt hkmod, hkmod, Nat.ne_of_gt hkpos, hkper⟩
end Proof
