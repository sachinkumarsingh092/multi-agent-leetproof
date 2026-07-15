import Lean
import Mathlib.Tactic
import Velvet.Std

set_option maxHeartbeats 10000000

section Specs
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false

/- Problem Description
    496. Next Greater Element I: For each element of nums1, find its next greater element in nums2.
    **Important: complexity should be O(m + n) time and O(n) space**
    Natural language breakdown:
    1. We are given two 0-indexed arrays nums1 and nums2 of integers.
    2. All elements in each array are distinct.
    3. Every element of nums1 appears somewhere in nums2 (nums1 is a subset of nums2).
    4. For a value x located at index j in nums2, its next greater element is the first element strictly greater than x that occurs at some index k > j.
    5. If such a k exists, the answer for x is nums2[k].
    6. If no such k exists, the answer for x is -1.
    7. The returned array ans has the same length as nums1.
    8. For each i, ans[i] is determined by the position of nums1[i] within nums2 and the next-greater rule above.
-/

-- Helper predicates are written purely in terms of Array operations (no Array/List conversion).

def DistinctArray (a : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < a.size → j < a.size → i ≠ j → a[i]! ≠ a[j]!

def IsSubsetArray (small : Array Int) (big : Array Int) : Prop :=
  ∀ (i : Nat), i < small.size → ∃ (j : Nat), j < big.size ∧ big[j]! = small[i]!

-- x occurs in array a at index j.
def OccursAt (a : Array Int) (x : Int) (j : Nat) : Prop :=
  j < a.size ∧ a[j]! = x

-- k is the (index of the) next greater element for position j in a.
-- This means:
-- * it is to the right (j < k)
-- * it is strictly greater
-- * no earlier index between j and k is strictly greater (k is the first such index)
def NextGreaterIndex (a : Array Int) (j : Nat) (k : Nat) : Prop :=
  j < k ∧
  k < a.size ∧
  a[k]! > a[j]! ∧
  (∀ (t : Nat), j < t → t < k → a[t]! ≤ a[j]!)

def HasNextGreater (a : Array Int) (j : Nat) : Prop :=
  ∃ (k : Nat), NextGreaterIndex a j k

-- v is the next-greater value for index j; v = -1 iff no next-greater exists.
def NextGreaterValue (a : Array Int) (j : Nat) (v : Int) : Prop :=
  (v = (-1) ∧ ¬ HasNextGreater a j) ∨
  (∃ (k : Nat), NextGreaterIndex a j k ∧ v = a[k]!)

-- Preconditions

def precondition (nums1 : Array Int) (nums2 : Array Int) : Prop :=
  DistinctArray nums1 ∧
  DistinctArray nums2 ∧
  IsSubsetArray nums1 nums2

-- Postconditions

def postcondition (nums1 : Array Int) (nums2 : Array Int) (ans : Array Int) : Prop :=
  ans.size = nums1.size ∧
  (∀ (i : Nat), i < nums1.size →
    ∃ (j : Nat), OccursAt nums2 nums1[i]! j ∧ NextGreaterValue nums2 j ans[i]!)
end Specs

section Impl
def implementation (nums1 : Array Int) (nums2 : Array Int) : Array Int :=
  -- Standard O(n) monotone-stack algorithm over `nums2`, recording next-greater values.
  -- We store in a hashmap mapping each value in `nums2` to its next greater value.
  let rec process (i : Nat) (stack : List Int) (m : Std.HashMap Int Int) : Std.HashMap Int Int :=
    if h : i < nums2.size then
      let x := nums2[i]!
      -- Pop all values smaller than x; for each popped v, x is its next greater.
      let rec pop (s : List Int) (m' : Std.HashMap Int Int) : List Int × Std.HashMap Int Int :=
        match s with
        | [] => ([], m')
        | v :: rest =>
          if v < x then
            pop rest (m'.insert v x)
          else
            (s, m')
      let (stack', m') := pop stack m
      process (i + 1) (x :: stack') m'
    else
      m
  let mp := process 0 [] (Std.HashMap.empty)
  -- Build answer for nums1 by lookup, defaulting to -1.
  let rec build (i : Nat) (acc : Array Int) : Array Int :=
    if h : i < nums1.size then
      let x := nums1[i]!
      let v := (mp.get? x).getD (-1)
      build (i + 1) (acc.push v)
    else
      acc
  build 0 #[]
end Impl

section TestCases
-- Test case 1: Example 1
-- nums1 = [4,1,2], nums2 = [1,3,4,2] => [-1,3,-1]
def test1_nums1 : Array Int := #[4, 1, 2]
def test1_nums2 : Array Int := #[1, 3, 4, 2]
def test1_Expected : Array Int := #[-1, 3, -1]

-- Test case 2: Example 2
-- nums1 = [2,4], nums2 = [1,2,3,4] => [3,-1]
def test2_nums1 : Array Int := #[2, 4]
def test2_nums2 : Array Int := #[1, 2, 3, 4]
def test2_Expected : Array Int := #[3, -1]

-- Test case 3: nums1 empty (vacuous subset), nums2 non-empty
-- ans should be empty
def test3_nums1 : Array Int := #[]
def test3_nums2 : Array Int := #[5, 1, 7]
def test3_Expected : Array Int := #[]

-- Test case 4: both arrays empty
def test4_nums1 : Array Int := #[]
def test4_nums2 : Array Int := #[]
def test4_Expected : Array Int := #[]

-- Test case 5: singleton where no next greater exists
def test5_nums1 : Array Int := #[10]
def test5_nums2 : Array Int := #[10]
def test5_Expected : Array Int := #[-1]

-- Test case 6: singleton where next greater exists immediately
def test6_nums1 : Array Int := #[1]
def test6_nums2 : Array Int := #[1, 2]
def test6_Expected : Array Int := #[2]

-- Test case 7: includes negative values
-- nums2 = [-2, -1, -3, 0], next greater of -2 is -1, of -3 is 0
def test7_nums1 : Array Int := #[-2, -3]
def test7_nums2 : Array Int := #[-2, -1, -3, 0]
def test7_Expected : Array Int := #[-1, 0]

-- Test case 8: nums1 = nums2, mixed next-greater and -1
def test8_nums1 : Array Int := #[3, 1, 4, 2]
def test8_nums2 : Array Int := #[3, 1, 4, 2]
def test8_Expected : Array Int := #[4, 4, -1, -1]

-- Test case 9: next greater is not adjacent (must be the first greater to the right)
-- nums2 = [2,1,3]; next greater of 1 is 3
def test9_nums1 : Array Int := #[1]
def test9_nums2 : Array Int := #[2, 1, 3]
def test9_Expected : Array Int := #[3]

-- Recommend to validate: parsing, precondition satisfiable, postcondition captures “first greater to the right”
end TestCases

section Assertions
-- Test case 1
#assert_same_evaluation #[(implementation test1_nums1 test1_nums2), test1_Expected]

-- Test case 2
#assert_same_evaluation #[(implementation test2_nums1 test2_nums2), test2_Expected]

-- Test case 3
#assert_same_evaluation #[(implementation test3_nums1 test3_nums2), test3_Expected]

-- Test case 4
#assert_same_evaluation #[(implementation test4_nums1 test4_nums2), test4_Expected]

-- Test case 5
#assert_same_evaluation #[(implementation test5_nums1 test5_nums2), test5_Expected]

-- Test case 6
#assert_same_evaluation #[(implementation test6_nums1 test6_nums2), test6_Expected]

-- Test case 7
#assert_same_evaluation #[(implementation test7_nums1 test7_nums2), test7_Expected]

-- Test case 8
#assert_same_evaluation #[(implementation test8_nums1 test8_nums2), test8_Expected]

-- Test case 9
#assert_same_evaluation #[(implementation test9_nums1 test9_nums2), test9_Expected]
end Assertions

section Proof
theorem correctness_goal_0
    (nums1 : Array ℤ)
    (nums2 : Array ℤ)
    : (implementation nums1 nums2).size = nums1.size := by
    classical
    simp [implementation]
    set mp : Std.HashMap Int Int := implementation.process nums2 0 [] Std.HashMap.empty

    have hbuild :
        ∀ (i : Nat) (acc : Array Int),
          (implementation.build nums1 mp i acc).size = acc.size + (nums1.size - i) := by
      intro i acc
      refine (Nat.rec
        (motive := fun n =>
          ∀ (i : Nat) (acc : Array Int),
            nums1.size - i = n →
            (implementation.build nums1 mp i acc).size = acc.size + n)
        ?base ?step (nums1.size - i) i acc rfl)
      · intro i acc hi
        have hle : nums1.size ≤ i := (Nat.sub_eq_zero_iff_le).1 hi
        have hnot : ¬ i < nums1.size := Nat.not_lt_of_ge hle
        rw [implementation.build.eq_1]
        simp [dif_neg hnot]
      · intro n ih i acc hi
        have hpos : 0 < nums1.size - i := by
          simpa [hi] using Nat.succ_pos n
        have hlt : i < nums1.size := Nat.lt_of_sub_pos hpos
        have hi' : nums1.size - (i + 1) = n := by
          simpa [Nat.sub_succ', hi]

        rw [implementation.build.eq_1]
        simp [dif_pos hlt]

        have ih' := ih (i := i + 1)
          (acc := acc.push (mp[nums1[i]!]?.getD (-1))) hi'
        rw [ih']
        simp [Array.size_push, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

    have := hbuild 0 (#[] : Array Int)
    simpa [mp, Array.size_empty, Nat.sub_zero] using this

lemma Array.getElem!_push_lt' [Inhabited α] (xs : Array α) (x : α) (i : Nat)
    (h : i < xs.size) : (xs.push x)[i]! = xs[i]! := by
  rw [Array.getElem!_eq_getD, Array.getElem!_eq_getD]
  have hiPush : i < (xs.push x).size := by
    simpa [Array.size_push] using Nat.lt_trans h (Nat.lt_succ_self xs.size)
  have hiPush' : i < xs.size + 1 := by
    simpa [Array.size_push] using hiPush
  simp [Array.getD, hiPush, h, Array.getElem_push]
  · intro hle
    exact (False.elim (Nat.not_lt_of_ge hle hiPush'))

lemma Array.getElem!_push_size' [Inhabited α] (xs : Array α) (x : α) : (xs.push x)[xs.size]! = x := by
  rw [Array.getElem!_eq_getD]
  have hiPush : xs.size < (xs.push x).size := by
    simpa [Array.size_push] using Nat.lt_succ_self xs.size
  simp [Array.getD, hiPush, Array.getElem_push]


theorem correctness_goal_1_0
    (nums1 : Array ℤ)
    (i : ℕ)
    (hi : i < nums1.size)
    (mp : Std.HashMap ℤ ℤ)
    : (implementation.build nums1 mp 0 #[])[i]! = (mp.get? nums1[i]!).getD (-1) := by

  have build_correct :
      ∀ (m k : Nat) (acc : Array ℤ),
        nums1.size - k = m →
        k ≤ nums1.size →
        acc.size = k →
        (∀ t : Nat, t < k → acc[t]! = (mp.get? nums1[t]!).getD (-1)) →
        ∀ idx : Nat, idx < nums1.size →
          (implementation.build nums1 mp k acc)[idx]! = (mp.get? nums1[idx]!).getD (-1) := by
    intro m
    induction m with
    | zero =>
        intro k acc hkm hk hsize hacc idx hidx
        have hkle : nums1.size ≤ k := Nat.sub_eq_zero_iff_le.mp hkm
        have hkEq : k = nums1.size := Nat.le_antisymm hk hkle
        have hnot : ¬ k < nums1.size := by
          simpa [hkEq] using (Nat.lt_irrefl nums1.size)
        have hidxk : idx < k := by
          simpa [hkEq] using hidx
        unfold implementation.build
        simp [hnot, hacc idx hidxk]

    | succ m ih =>
        intro k acc hkm hk hsize hacc idx hidx
        have hklt : k < nums1.size := by
          have : 0 < nums1.size - k := by
            simpa [hkm] using Nat.succ_pos m
          exact (Nat.sub_pos_iff_lt).1 this

        let x : ℤ := nums1[k]'hklt
        let v : ℤ := (mp.get? x).getD (-1)

        have hx : nums1[k]! = x := by
          -- `getElem!` agrees with `getElem` when in-bounds
          simp [x, Array.getElem!_eq_getD, Array.getD, hklt]

        have hv : v = (mp.get? nums1[k]!).getD (-1) := by
          simp [v, x, hx]

        have hkm' : nums1.size - (k + 1) = m := by
          simpa [Nat.sub_succ, hkm]

        have hk' : k + 1 ≤ nums1.size := Nat.succ_le_of_lt hklt

        have hsize' : (acc.push v).size = k + 1 := by
          -- size of `push` is `acc.size + 1`
          simpa [Array.size_push, hsize] using (Array.size_push (xs := acc) v)

        have hacc' : ∀ t : Nat, t < k + 1 → (acc.push v)[t]! = (mp.get? nums1[t]!).getD (-1) := by
          intro t ht
          have ht_le : t ≤ k := Nat.lt_succ_iff.mp ht
          cases Nat.lt_or_eq_of_le ht_le with
          | inl htk =>
              have htsize : t < acc.size := by
                simpa [hsize] using htk
              have hpush : (acc.push v)[t]! = acc[t]! :=
                Array.getElem!_push_lt' (xs := acc) (x := v) (i := t) htsize
              calc
                (acc.push v)[t]! = acc[t]! := hpush
                _ = (mp.get? nums1[t]!).getD (-1) := hacc t htk
          | inr htk =>
              subst t
              have hlast : (acc.push v)[acc.size]! = v :=
                Array.getElem!_push_size' (xs := acc) (x := v)
              have hlast' : (acc.push v)[k]! = v := by
                simpa [hsize] using hlast
              -- rewrite `v` to the expected lookup value
              simpa [hv] using hlast'

        -- unfold one iteration of `build` and apply IH
        unfold implementation.build
        -- reduce the top-level `if` and zeta-reduce `x`/`v`
        -- The goal becomes a call to `build` at `k+1` with `acc.push v`.
        simp [hklt, x, v]
        exact ih (k + 1) (acc.push v) hkm' hk' hsize' hacc' idx hidx

  have hsize0 : (#[] : Array ℤ).size = 0 := by simp
  have hacc0 : ∀ t : Nat, t < 0 → (#[] : Array ℤ)[t]! = (mp.get? nums1[t]!).getD (-1) := by
    intro t ht
    exact False.elim (Nat.not_lt_zero _ ht)

  simpa using
    build_correct nums1.size 0 (#[] : Array ℤ) (by simp) (Nat.zero_le _) hsize0 hacc0 i hi

theorem correctness_goal_1_1
    (nums1 : Array ℤ)
    (nums2 : Array ℤ)
    (h_precond : precondition nums1 nums2)
    (i : ℕ)
    (hi : i < nums1.size)
    (j : ℕ)
    (hj : j < nums2.size)
    (hjval : nums2[j]! = nums1[i]!)
    (mp : Std.HashMap ℤ ℤ)
    (hmp : mp = implementation.process nums2 0 [] Std.HashMap.empty)
    (h_build_i : (implementation.build nums1 mp 0 #[])[i]! = (mp.get? nums1[i]!).getD (-1))
    : NextGreaterValue nums2 j ((mp.get? nums2[j]!).getD (-1)) := by
    sorry

theorem correctness_goal_1
    (nums1 : Array ℤ)
    (nums2 : Array ℤ)
    (h_precond : precondition nums1 nums2)
    (i : ℕ)
    (hi : i < nums1.size)
    (j : ℕ)
    (hj : j < nums2.size)
    (hjval : nums2[j]! = nums1[i]!)
    : NextGreaterValue nums2 j (implementation.build nums1 (implementation.process nums2 0 [] Std.HashMap.empty) 0 #[])[i]! := by
  classical
  set mp : Std.HashMap ℤ ℤ := implementation.process nums2 0 [] Std.HashMap.empty with hmp
  -- goal is rewritten to use mp by `set`
  have h_build_i : (implementation.build nums1 mp 0 #[])[i]! = (mp.get? (nums1[i]!)).getD (-1) := by
    expose_names; exact (correctness_goal_1_0 nums1 i hi mp)
  have h_process_j : NextGreaterValue nums2 j ((mp.get? (nums2[j]!)).getD (-1)) := by
    expose_names; exact (correctness_goal_1_1 nums1 nums2 h_precond i hi j hj hjval mp hmp h_build_i)
  have h_key : (mp.get? (nums1[i]!)).getD (-1) = (mp.get? (nums2[j]!)).getD (-1) := by
    simpa [hjval]
  have : (implementation.build nums1 mp 0 #[])[i]! = (mp.get? (nums2[j]!)).getD (-1) := by
    simpa [h_build_i, h_key]
  simpa [this] using h_process_j

theorem correctness_goal
    (nums1 : Array Int)
    (nums2 : Array Int)
    (h_precond : precondition nums1 nums2)
    : postcondition nums1 nums2 (implementation nums1 nums2) := by
  classical
  unfold postcondition
  constructor
  · -- size
    expose_names; exact (correctness_goal_0 nums1 nums2)
  · intro i hi
    -- existence of j from subset precondition
    rcases h_precond.2.2 i hi with ⟨j, hj, hjval⟩
    refine ⟨j, ?_, ?_⟩
    · exact And.intro hj hjval
    · -- next-greater value correctness of implementation at index i
      -- unfold implementation to see structure
      simp [implementation] at *
      expose_names; exact (correctness_goal_1 nums1 nums2 h_precond i hi j hj hjval)
end Proof
