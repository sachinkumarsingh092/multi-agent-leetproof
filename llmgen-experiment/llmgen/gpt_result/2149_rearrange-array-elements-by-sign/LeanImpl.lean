import Lean
import Mathlib.Tactic
import Velvet.Std
import Extensions.VelvetPBT

set_option maxHeartbeats 10000000

set_option maxRecDepth 10000
section Specs
-- Never add new imports here

set_option pp.coercions false
set_option pp.funBinderTypes true

/- Problem Description
    2149. Rearrange Array Elements by Sign: Rearrange an even-length integer array with equal numbers of positive and negative elements so that signs alternate starting with a positive, while preserving relative order within each sign.
    **Important: complexity should be O(n) time and O(n) space**
    Natural language breakdown:
    1. The input is a 0-indexed array of integers of even length.
    2. Every element is either strictly positive or strictly negative (no zeros).
    3. The number of positive elements equals the number of negative elements.
    4. The output is an array of the same length that is a rearrangement (permutation) of the input.
    5. The output starts with a positive element when the array is nonempty.
    6. Consecutive elements in the output have opposite signs (equivalently, indices with even parity are positive and odd parity are negative).
    7. Among all positives (respectively negatives), their relative order in the output is the same as in the input (stable with respect to sign).
-/

-- Helper predicates as Bool for use with Array.filter/countP.
def isPosB (x : Int) : Bool := decide (x > 0)
def isNegB (x : Int) : Bool := decide (x < 0)

def countPos (nums : Array Int) : Nat := nums.countP isPosB

def countNeg (nums : Array Int) : Nat := nums.countP isNegB

def allNonZero (nums : Array Int) : Prop :=
  ∀ (i : Nat), i < nums.size → nums[i]! ≠ 0

-- Parity-based sign pattern for the desired result.
def alternatesStartingPos (arr : Array Int) : Prop :=
  ∀ (i : Nat), i < arr.size →
    ((i % 2 = 0) → arr[i]! > 0) ∧
    ((i % 2 = 1) → arr[i]! < 0)

-- Stable order within sign can be characterized by equality of the sign-filtered subsequences.
def stableBySign (nums : Array Int) (result : Array Int) : Prop :=
  result.filter isPosB = nums.filter isPosB ∧
  result.filter isNegB = nums.filter isNegB

-- Preconditions: even length, no zeros, equal number of positives and negatives.
def precondition (nums : Array Int) : Prop :=
  nums.size % 2 = 0 ∧
  allNonZero nums ∧
  countPos nums = nums.size / 2 ∧
  countNeg nums = nums.size / 2

-- Postconditions: permutation, correct alternating sign pattern, starts with positive if nonempty,
-- and stability of relative order within each sign.
def postcondition (nums : Array Int) (result : Array Int) : Prop :=
  result.size = nums.size ∧
  result.Perm nums ∧
  alternatesStartingPos result ∧
  (result.size > 0 → result[0]! > 0) ∧
  stableBySign nums result
end Specs

section Impl
def implementation (nums : Array Int) : Array Int :=
  -- Split into positives and negatives (stable) without using any spec-defined helpers.
  let pos := nums.filter (fun x => x > 0)
  let neg := nums.filter (fun x => x < 0)
  let n := pos.size
  -- Interleave: [pos[0], neg[0], pos[1], neg[1], ...]
  (Array.range n).foldl
    (fun acc i =>
      let acc := acc.push (pos[i]!)
      acc.push (neg[i]!))
    (#[])
end Impl

section TestCases
-- Test case 1: Example 1
-- Input: [3,1,-2,-5,2,-4]
-- Output: [3,-2,1,-5,2,-4]
def test1_nums : Array Int := #[3, 1, -2, -5, 2, -4]
def test1_Expected : Array Int := #[3, -2, 1, -5, 2, -4]

-- Test case 2: Example 2 (starts with a negative in input)
def test2_nums : Array Int := #[-1, 1]
def test2_Expected : Array Int := #[1, -1]

-- Test case 3: Empty array (degenerate but satisfies even length and equal counts)
def test3_nums : Array Int := #[]
def test3_Expected : Array Int := #[]

-- Test case 4: Smallest nontrivial already-correct alternating order
def test4_nums : Array Int := #[1, -1]
def test4_Expected : Array Int := #[1, -1]

-- Test case 5: Larger array where positives/negatives are grouped
-- Positives: [1,2,3], Negatives: [-1,-2,-3]
def test5_nums : Array Int := #[1, 2, 3, -1, -2, -3]
def test5_Expected : Array Int := #[1, -1, 2, -2, 3, -3]

-- Test case 6: Alternating input but begins with negative; must start with positive in output
-- Positives: [5,6], Negatives: [-5,-6]
def test6_nums : Array Int := #[-5, 5, -6, 6]
def test6_Expected : Array Int := #[5, -5, 6, -6]

-- Test case 7: Mixed order; checks stability within each sign
-- Positives in input: [2,4,6,8], Negatives: [-1,-3,-5,-7]
def test7_nums : Array Int := #[2, -1, 4, -3, 6, -5, 8, -7]
def test7_Expected : Array Int := #[2, -1, 4, -3, 6, -5, 8, -7]

-- Test case 8: All positives first but with different magnitudes; confirms stable order
-- Positives: [10,1,7], Negatives: [-2,-9,-3]
def test8_nums : Array Int := #[10, 1, 7, -2, -9, -3]
def test8_Expected : Array Int := #[10, -2, 1, -9, 7, -3]
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
end Assertions

section Pbt
method implementationPbt (nums : Array Int)
  return (result : Array Int)
  require precondition nums
  ensures postcondition nums result
  do
  return (implementation nums)

velvet_plausible_test implementationPbt (config := { maxMs := some 20000 })
end Pbt

section Proof
theorem correctness_goal_0
    (nums : Array ℤ)
    (h_precond : precondition nums)
    : (Array.filter (fun x => decide (x > 0)) nums).size = nums.size / 2 := by
  rcases h_precond with ⟨_hEven, _hNonZero, hPos, _hNeg⟩
  have hcount : nums.countP (fun x => decide (x > 0)) = nums.size / 2 := by
    simpa [countPos, isPosB] using hPos
  have hsize : (Array.filter (fun x => decide (x > 0)) nums).size =
      nums.countP (fun x => decide (x > 0)) := by
    simpa using
      (Eq.symm (Array.countP_eq_size_filter (p := fun x => decide (x > 0)) (xs := nums)))
  exact hsize.trans hcount

theorem correctness_goal_1
    (nums : Array ℤ)
    (h_precond : precondition nums)
    : (Array.filter (fun x => decide (x < 0)) nums).size = nums.size / 2 := by
  rcases h_precond with ⟨hEven, hNonZero, hCountPos, hCountNeg⟩
  have hcount : (nums.filter isNegB).size = countNeg nums := by
    simpa [countNeg] using
      (Array.countP_eq_size_filter (xs := nums) (p := isNegB)).symm
  calc
    (Array.filter (fun x => decide (x < 0)) nums).size
        = (nums.filter isNegB).size := by
            rfl
    _ = countNeg nums := hcount
    _ = nums.size / 2 := hCountNeg

theorem correctness_goal_2
    (nums : Array ℤ)
    (h_precond : precondition nums)
    (hpos_size : (Array.filter (fun x => decide (x > 0)) nums).size = nums.size / 2)
    : (implementation nums).size = nums.size := by
  have hEven : nums.size % 2 = 0 := h_precond.1

  have hpos_size' : (nums.filter (fun x => decide (x > 0))).size = nums.size / 2 := by
    simpa using hpos_size

  -- Local definitions matching `implementation`.
  let pos : Array Int := nums.filter (fun x => decide (x > 0))
  let neg : Array Int := nums.filter (fun x => decide (x < 0))
  let n : Nat := pos.size
  let f : Array Int → Nat → Array Int := fun acc i =>
    let acc := acc.push (pos[i]!)
    acc.push (neg[i]!)

  have hfold : ((Array.range n).foldl f (#[])).size = 2 * n := by
    -- Use `Array.foldl_induction` with the invariant `acc.size = 2*k`.
    have hmotive :
        (fun k (acc : Array Int) => acc.size = 2 * k)
          (Array.range n).size ((Array.range n).foldl f (#[] : Array Int)) := by
      refine Array.foldl_induction 
        (motive := fun k (acc : Array Int) => acc.size = 2 * k)
        (init := (#[] : Array Int)) (f := f) ?h0 ?hf
      · -- base case
        simp
      · -- step case
        intro i acc hik
        -- After pushing two elements, the size increases by 2.
        have : (f acc (Array.range n)[i]).size = acc.size + 2 := by
          simp [f, Array.size_push, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        -- Use the induction hypothesis.
        calc
          (f acc (Array.range n)[i]).size
              = acc.size + 2 := this
          _ = (2 * i.1) + 2 := by simpa [hik]
          _ = 2 * (i.1 + 1) := by
                simp [Nat.mul_succ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

    -- Convert from `(Array.range n).size` to `n`.
    simpa [Array.size_range] using hmotive

  have hdiv : 2 ∣ nums.size := Nat.dvd_of_mod_eq_zero hEven

  have hn : n = nums.size / 2 := by
    -- unfold `n` and `pos`
    simp [n, pos, hpos_size']

  calc
    (implementation nums).size
        = ((Array.range n).foldl f (#[] : Array Int)).size := by
            simp [implementation, pos, neg, n, f]
    _ = 2 * n := hfold
    _ = 2 * (nums.size / 2) := by simp [hn]
    _ = nums.size := by
          simpa using (Nat.mul_div_cancel' (n := 2) (m := nums.size) hdiv)

lemma Array.get!_eq_getElem {α : Type} [Inhabited α] (xs : Array α) (i : Nat) (h : i < xs.size) : xs[i]! = xs[i] := by
  -- try unfolding get! to getD and then simplifying getD at an in-bounds index
  -- `simp` should reduce `getD`/`get?` on arrays
  simp [Array.get!_eq_getD, Array.getD, h]



theorem correctness_goal_3_0
    (nums : Array ℤ)
    (hpos_size : (Array.filter (fun x => decide (x > 0)) nums).size = nums.size / 2)
    (hneg_size : (Array.filter (fun x => decide (x < 0)) nums).size = nums.size / 2)
    (h_pos_entries : ∀ j < (Array.filter (fun x => decide (x > 0)) nums).size, (Array.filter (fun x => decide (x > 0)) nums)[j]! > 0)
    (h_neg_entries : ∀ j < (Array.filter (fun x => decide (x < 0)) nums).size, (Array.filter (fun x => decide (x < 0)) nums)[j]! < 0)
    : alternatesStartingPos
  (Array.foldl
    (fun acc i =>
      let acc := acc.push (Array.filter (fun x => decide (x > 0)) nums)[i]!;
      acc.push (Array.filter (fun x => decide (x < 0)) nums)[i]!)
    #[] (Array.range (Array.filter (fun x => decide (x > 0)) nums).size)) := by
  classical
  let pos : Array Int := Array.filter (fun x => decide (x > 0)) nums
  let neg : Array Int := Array.filter (fun x => decide (x < 0)) nums
  let n : Nat := pos.size

  have hpos_size' : pos.size = nums.size / 2 := by
    simpa [pos] using hpos_size
  have hneg_size' : neg.size = nums.size / 2 := by
    simpa [neg] using hneg_size
  have hneg_eq : neg.size = pos.size := by
    simpa using (hneg_size'.trans hpos_size'.symm)

  have push2_alt :
      ∀ (acc : Array Int) (k : Nat) (x y : Int),
        acc.size = 2 * k →
        alternatesStartingPos acc →
        x > 0 → y < 0 →
        alternatesStartingPos ((acc.push x).push y) := by
    intro acc k x y hsz halt hx hy
    intro i hi
    set arr : Array Int := (acc.push x).push y
    have hi_arr : i < arr.size := by simpa [arr] using hi

    by_cases hlt : i < acc.size
    · -- old index
      have hi_push1 : i < (acc.push x).size := by
        simpa [Array.size_push] using Nat.lt_succ_of_lt hlt
      have hi_push1' : i < acc.size + 1 := by
        simpa [Array.size_push] using hi_push1
      have hi_push2 : i < ((acc.push x).push y).size := by simpa [arr] using hi

      have harr_get : arr[i] = acc[i] := by
        have h1 := (Array.getElem_push (xs := acc.push x) (x := y) (i := i) hi_push2)
        have h2 := (Array.getElem_push (xs := acc) (x := x) (i := i) hi_push1)
        have h1' : ((acc.push x).push y)[i] = (acc.push x)[i] := by
          simpa [hi_push1'] using h1
        have h2' : (acc.push x)[i] = acc[i] := by
          simpa [hlt] using h2
        simpa [arr, h1', h2']

      have halt_i := halt i hlt
      refine And.intro ?_ ?_
      · intro hmod
        have hacc : acc[i]! > 0 := halt_i.1 hmod
        have hacc' : acc[i] > 0 := by
          simpa [Array.get!_eq_getElem _ _ hlt] using hacc
        have harr' : arr[i] > 0 := by simpa [harr_get] using hacc'
        simpa [Array.get!_eq_getElem _ _ hi_arr] using harr'
      · intro hmod
        have hacc : acc[i]! < 0 := halt_i.2 hmod
        have hacc' : acc[i] < 0 := by
          simpa [Array.get!_eq_getElem _ _ hlt] using hacc
        have harr' : arr[i] < 0 := by simpa [harr_get] using hacc'
        simpa [Array.get!_eq_getElem _ _ hi_arr] using harr'
    · -- new indices
      have hge : acc.size ≤ i := Nat.le_of_not_gt hlt
      have hi' : i < acc.size + 2 := by
        have : arr.size = acc.size + 2 := by
          simp [arr, Array.size_push, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        simpa [arr, this] using hi
      have hle : i ≤ acc.size + 1 := by
        exact Nat.lt_succ_iff.mp (by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hi')
      rcases Nat.exists_eq_add_of_le hge with ⟨d, rfl⟩
      have hd_le : d ≤ 1 := by
        exact Nat.le_of_add_le_add_left hle
      have hd_cases : d = 0 ∨ d = 1 := Nat.le_one_iff_eq_zero_or_eq_one.mp hd_le
      cases hd_cases with
      | inl hd0 =>
          subst hd0
          -- i = acc.size
          have h_in_bounds : acc.size < arr.size := by
            have : arr.size = acc.size + 2 := by
              simp [arr, Array.size_push, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
            simpa [this] using Nat.lt_succ_of_lt (Nat.lt_succ_self acc.size)
          have hi_push : acc.size < (acc.push x).size := by
            simp [Array.size_push]
          have hi_push' : acc.size < acc.size + 1 := by
            simpa [Array.size_push] using hi_push
          have harr_val : arr[acc.size] = x := by
            have h1 := (Array.getElem_push (xs := acc.push x) (x := y) (i := acc.size) h_in_bounds)
            have h2 := (Array.getElem_push (xs := acc) (x := x) (i := acc.size) hi_push)
            have h1' : ((acc.push x).push y)[acc.size] = (acc.push x)[acc.size] := by
              simpa [hi_push'] using h1
            have h2' : (acc.push x)[acc.size] = x := by
              simpa [Nat.lt_irrefl] using h2
            simpa [arr, h1', h2']

          have hmod0 : acc.size % 2 = 0 := by
            have : acc.size = 2 * k := hsz
            calc
              acc.size % 2 = (2 * k) % 2 := by simpa [this]
              _ = 0 := Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_right 2 k)

          refine And.intro ?_ ?_
          · intro _
            have hx' : arr[acc.size] > 0 := by simpa [harr_val] using hx
            simpa [Array.get!_eq_getElem _ _ h_in_bounds] using hx'
          · intro hmod
            have : (0 : Nat) = 1 := by simpa [hmod0] using hmod
            cases this
      | inr hd1 =>
          subst hd1
          -- i = acc.size + 1
          have h_in_bounds : acc.size + 1 < arr.size := by
            have : arr.size = acc.size + 2 := by
              simp [arr, Array.size_push, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
            simpa [this, Nat.add_assoc] using Nat.lt_succ_self (acc.size + 1)

          have harr_val : arr[acc.size + 1] = y := by
            have hlt_last : ¬(acc.size + 1 < (acc.push x).size) := by
              simp [Array.size_push]
            have h1 := (Array.getElem_push (xs := acc.push x) (x := y) (i := acc.size + 1) h_in_bounds)
            simpa [arr, hlt_last] using h1

          have hmod1 : (acc.size + 1) % 2 = 1 := by
            have : acc.size = 2 * k := hsz
            calc
              (acc.size + 1) % 2 = ((2 * k) + 1) % 2 := by simpa [this]
              _ = 1 := by
                have h0 : (2 * k) % 2 = 0 := Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_right 2 k)
                simpa [Nat.add_mod, h0]

          refine And.intro ?_ ?_
          · intro hmod
            have : (1 : Nat) = 0 := by simpa [hmod1] using hmod
            cases this
          · intro _
            have hy' : arr[acc.size + 1] < 0 := by simpa [harr_val] using hy
            simpa [Array.get!_eq_getElem _ _ h_in_bounds] using hy'

  let step (acc : Array Int) (i : Nat) : Array Int :=
    let acc := acc.push (pos[i]!);
    acc.push (neg[i]!)

  have hmot :
      (fun k (acc : Array Int) => acc.size = 2 * k ∧ alternatesStartingPos acc)
        (Array.range n).size
        ((Array.range n).foldl step #[]) := by
    apply Array.foldl_induction 
      (motive := fun k acc => acc.size = 2 * k ∧ alternatesStartingPos acc)
      (init := (#[] : Array Int))
    · constructor
      · simp
      · simp [alternatesStartingPos]
    · intro i b hb
      rcases hb with ⟨hbsize, hbalt⟩
      have hi_lt_n : i.1 < n := by
        simpa [Array.size_range] using i.2
      have hidx : (Array.range n)[i] = i.1 := by
        simpa using
          (Array.getElem_range (n := n) (i := i.1)
            (h := by simpa [Array.size_range] using i.2))

      have hx : pos[i.1]! > 0 := by
        simpa [pos] using h_pos_entries i.1 (by simpa [n] using hi_lt_n)
      have hy : neg[i.1]! < 0 := by
        have hi_lt_neg : i.1 < neg.size := by
          have : i.1 < pos.size := by simpa [n] using hi_lt_n
          simpa [hneg_eq] using this
        simpa [neg] using h_neg_entries i.1 hi_lt_neg

      have hstep_size : (step b (Array.range n)[i]).size = 2 * (i.1 + 1) := by
        simp [step, hidx, Array.size_push, hbsize, Nat.mul_add, Nat.add_mul]

      have hstep_alt : alternatesStartingPos (step b (Array.range n)[i]) := by
        simpa [step, hidx] using
          push2_alt b i.1 (pos[i.1]!) (neg[i.1]!) hbsize hbalt hx hy

      exact ⟨hstep_size, hstep_alt⟩

  simpa [pos, neg, n, step] using (hmot.2)

theorem correctness_goal_3
    (nums : Array ℤ)
    (hpos_size : (Array.filter (fun x => decide (x > 0)) nums).size = nums.size / 2)
    (hneg_size : (Array.filter (fun x => decide (x < 0)) nums).size = nums.size / 2)
    (hsize : (implementation nums).size = nums.size)
    : alternatesStartingPos (implementation nums) := by
  -- First, show every element in the filtered arrays has the intended sign.
  have h_pos_entries : ∀ j, j < (nums.filter (fun x => x > 0)).size → (nums.filter (fun x => x > 0))[j]! > 0 := by
    expose_names; intros; expose_names; try simp_all; try grind
  have h_neg_entries : ∀ j, j < (nums.filter (fun x => x < 0)).size → (nums.filter (fun x => x < 0))[j]! < 0 := by
    expose_names; intros; expose_names; try simp_all; try grind

  -- Main interleaving lemma for the specific `pos` and `neg` used in `implementation`.
  have h_interleave_alt : alternatesStartingPos
      ((Array.range ((nums.filter (fun x => x > 0)).size)).foldl
        (fun acc i =>
          let acc := acc.push ((nums.filter (fun x => x > 0))[i]!)
          acc.push ((nums.filter (fun x => x < 0))[i]!))
        (#[])) := by
    expose_names; exact (correctness_goal_3_0 nums hpos_size hneg_size h_pos_entries h_neg_entries)

  -- Now rewrite `implementation` and conclude.
  simpa [implementation] using h_interleave_alt

theorem correctness_goal_4
    (nums : Array ℤ)
    (hsize : (implementation nums).size = nums.size)
    (halt : alternatesStartingPos (implementation nums))
    : (implementation nums).size > 0 → (implementation nums)[0]! > 0 := by
  simp_all [isPosB, isNegB, countPos, countNeg, allNonZero, alternatesStartingPos, stableBySign, precondition, postcondition]

theorem correctness_goal_5
    (nums : Array ℤ)
    (hpos_size : (Array.filter (fun x => decide (x > 0)) nums).size = nums.size / 2)
    (hneg_size : (Array.filter (fun x => decide (x < 0)) nums).size = nums.size / 2)
    : stableBySign nums (implementation nums) := by
  classical

  let pos : Array Int := nums.filter (fun x => decide (0 < x))
  let neg : Array Int := nums.filter (fun x => decide (x < 0))
  let n : Nat := pos.size

  have hpos_size' : pos.size = nums.size / 2 := by
    simpa [pos] using hpos_size
  have hneg_size' : neg.size = nums.size / 2 := by
    simpa [neg] using hneg_size
  have hneg_eq : neg.size = pos.size := by
    simpa [hpos_size', hneg_size']

  have get!_eq_getElem {α} [Inhabited α] (xs : Array α) (i : Nat) (h : i < xs.size) :
      xs[i]! = xs[i] := by
    simpa using (by simp [Array.getElem!_eq_getD, Array.getD_getElem?, h])

  have pos_isPos (k : Nat) (hk : k < pos.size) : isPosB (pos[k]!) = true := by
    have hm : pos[k] ∈ pos := Array.getElem_mem hk
    have hm' : pos[k] ∈ nums.filter (fun x => decide (0 < x)) := by simpa [pos] using hm
    have hp : decide (0 < pos[k]) := (Array.mem_filter).1 hm' |>.2
    have hp' : decide (0 < pos[k]) = true := by simpa using hp
    have hget : pos[k]! = pos[k] := get!_eq_getElem pos k hk
    simpa [isPosB, hget] using hp'

  have neg_isNeg (k : Nat) (hk : k < neg.size) : isNegB (neg[k]!) = true := by
    have hm : neg[k] ∈ neg := Array.getElem_mem hk
    have hm' : neg[k] ∈ nums.filter (fun x => decide (x < 0)) := by simpa [neg] using hm
    have hp : decide (neg[k] < 0) := (Array.mem_filter).1 hm' |>.2
    have hp' : decide (neg[k] < 0) = true := by simpa using hp
    have hget : neg[k]! = neg[k] := get!_eq_getElem neg k hk
    simpa [isNegB, hget] using hp'

  have pos_isNeg_false (k : Nat) (hk : k < pos.size) : isNegB (pos[k]!) = false := by
    have hpB : isPosB (pos[k]!) = true := pos_isPos k hk
    have hp : pos[k]! > 0 := by simpa [isPosB] using hpB
    have hge : pos[k]! ≥ 0 := le_of_lt hp
    have hnlt : ¬ pos[k]! < 0 := not_lt_of_ge hge
    simp [isNegB, hnlt]

  have neg_isPos_false (k : Nat) (hk : k < neg.size) : isPosB (neg[k]!) = false := by
    have hnB : isNegB (neg[k]!) = true := neg_isNeg k hk
    have hn : neg[k]! < 0 := by simpa [isNegB] using hnB
    have hle : neg[k]! ≤ 0 := le_of_lt hn
    have hnlt : ¬ neg[k]! > 0 := not_lt_of_ge hle
    simp [isPosB, hnlt]

  let step : Array Int → Nat → Array Int := fun acc i => (acc.push (pos[i]!)).push (neg[i]!)
  let res : Nat → Array Int := fun k => (Array.range k).foldl step #[]

  have hres : ∀ k, k ≤ n →
      (res k).filter isPosB = (Array.range k).map (fun i => pos[i]!) ∧
      (res k).filter isNegB = (Array.range k).map (fun i => neg[i]!) := by
    intro k hk
    induction k with
    | zero =>
        constructor <;> simp [res, Array.range]
    | succ k ih =>
        have hk' : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
        have ih' := ih hk'
        have hklt : k < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk
        have hkpos : k < pos.size := by simpa [n] using hklt
        have hkneg : k < neg.size := by simpa [hneg_eq] using hkpos

        have hres_succ : res (k+1) = step (res k) k := by
          simp [res, Array.range_succ, Array.foldl_append, step]

        constructor
        · simp [hres_succ, step, Array.filter_push, pos_isPos k hkpos, neg_isPos_false k hkneg, ih'.1,
            Array.range_succ]
        · simp [hres_succ, step, Array.filter_push, neg_isNeg k hkneg, pos_isNeg_false k hkpos, ih'.2,
            Array.range_succ]

  have hfinal := hres n (le_rfl)
  have hpos_final : (res n).filter isPosB = (Array.range n).map (fun i => pos[i]!) := hfinal.1
  have hneg_final : (res n).filter isNegB = (Array.range n).map (fun i => neg[i]!) := hfinal.2

  have hmap_pos : (Array.range n).map (fun i => pos[i]!) = pos := by
    apply Array.ext
    · simp [n]
    · intro i hi; intro hi2
      have hipos : i < pos.size := hi2
      simpa [Array.getElem_map, Array.getElem_range, get!_eq_getElem pos i hipos]

  have hmap_neg : (Array.range n).map (fun i => neg[i]!) = neg := by
    apply Array.ext
    · simp [n, hneg_eq]
    · intro i hi; intro hi2
      have hineg : i < neg.size := hi2
      simpa [Array.getElem_map, Array.getElem_range, get!_eq_getElem neg i hineg]

  have himpl : res n = implementation nums := by
    -- avoid unfolding `Array.foldl` itself (can be large)
    simp [res, step, n, pos, neg, implementation]

  -- predicate equalities needed to relate `pos`/`neg` back to `isPosB`/`isNegB`
  have hpred : (fun x : Int => decide (0 < x)) = isPosB := by
    funext x; rfl
  have hnpred : (fun x : Int => decide (x < 0)) = isNegB := by
    funext x; rfl

  unfold stableBySign
  constructor
  · calc
      (implementation nums).filter isPosB
          = (res n).filter isPosB := by simpa [himpl]
      _ = (Array.range n).map (fun i => pos[i]!) := hpos_final
      _ = pos := hmap_pos
      _ = nums.filter isPosB := by
            simpa [pos, hpred]
  · calc
      (implementation nums).filter isNegB
          = (res n).filter isNegB := by simpa [himpl]
      _ = (Array.range n).map (fun i => neg[i]!) := hneg_final
      _ = neg := hmap_neg
      _ = nums.filter isNegB := by
            simpa [neg, hnpred]

theorem correctness_goal_6
    (nums : Array ℤ)
    (h_precond : precondition nums)
    (halt : alternatesStartingPos (implementation nums))
    (hstable : stableBySign nums (implementation nums))
    : (implementation nums).Perm nums := by
    classical

    rcases h_precond with ⟨_hEven, hNonZero, _hCountPos, _hCountNeg⟩

    rcases hstable with ⟨hPosArr, hNegArr⟩

    have hPosList : (implementation nums).toList.filter isPosB = nums.toList.filter isPosB := by
      simpa [Array.toList_filter] using congrArg Array.toList hPosArr

    have hNegList : (implementation nums).toList.filter isNegB = nums.toList.filter isNegB := by
      simpa [Array.toList_filter] using congrArg Array.toList hNegArr

    have hBangEq : ∀ (xs : Array Int) (i : Nat) (hi : i < xs.size), xs[i]! = xs[i]'hi := by
      intro xs i hi
      have hsome : xs[i]? = some xs[i] := Array.getElem?_eq_getElem (xs := xs) hi
      calc
        xs[i]! = xs.getD i default := by
          simpa [Array.getElem!_eq_getD]
        _ = xs[i]?.getD default := by
          simpa [Array.getD_eq_getD_getElem?]
        _ = (some xs[i]).getD default := by
          simpa [hsome]
        _ = xs[i] := by
          simp
        _ = xs[i]'hi := rfl

    have h0_notmem_nums_arr : (0 : Int) ∉ nums := by
      intro hmem
      rcases Array.getElem_of_mem hmem with ⟨i, hi, hget⟩
      have hbang : nums[i]! = (0 : Int) := by
        calc
          nums[i]! = nums[i]'hi := hBangEq nums i hi
          _ = 0 := hget
      exact (hNonZero i hi) hbang

    have h0_notmem_nums : (0 : Int) ∉ nums.toList := by
      intro hmem
      exact h0_notmem_nums_arr ((Array.mem_toList).1 hmem)

    have h0_notmem_impl_arr : (0 : Int) ∉ implementation nums := by
      intro hmem
      rcases Array.getElem_of_mem hmem with ⟨i, hi, hget⟩
      have hbang : (implementation nums)[i]! = (0 : Int) := by
        calc
          (implementation nums)[i]! = (implementation nums)[i]'hi := hBangEq (implementation nums) i hi
          _ = 0 := hget

      have hAlt := halt i hi
      rcases Nat.mod_two_eq_zero_or_one i with hmod | hmod
      · have hpos : (implementation nums)[i]! > 0 := hAlt.1 hmod
        have : (0 : Int) > 0 := by simpa [hbang] using hpos
        have : (0 : Int) < 0 := by simpa [gt_iff_lt] using this
        exact (lt_irrefl (0 : Int)) this
      · have hneg : (implementation nums)[i]! < 0 := hAlt.2 hmod
        have : (0 : Int) < 0 := by simpa [hbang] using hneg
        exact (lt_irrefl (0 : Int)) this

    have h0_notmem_impl : (0 : Int) ∉ (implementation nums).toList := by
      intro hmem
      exact h0_notmem_impl_arr ((Array.mem_toList).1 hmem)

    -- reduce to lists
    rw [Array.perm_iff_toList_perm]
    -- and to element counts
    rw [List.perm_iff_count]
    intro a

    rcases lt_trichotomy a 0 with haNeg | haZero | haPos
    · -- a < 0
      have haNegB : isNegB a := by
        -- isNegB a = decide (a < 0)
        simpa [isNegB, haNeg]

      have hc₁ : List.count a ((implementation nums).toList.filter isNegB) =
          List.count a (implementation nums).toList :=
        List.count_filter (l := (implementation nums).toList) (p := isNegB) (a := a) haNegB

      have hc₂ : List.count a (nums.toList.filter isNegB) = List.count a nums.toList :=
        List.count_filter (l := nums.toList) (p := isNegB) (a := a) haNegB

      calc
        List.count a (implementation nums).toList
            = List.count a ((implementation nums).toList.filter isNegB) := by
                simpa using hc₁.symm
        _ = List.count a (nums.toList.filter isNegB) := by
                simpa [hNegList]
        _ = List.count a nums.toList := by
                simpa using hc₂

    · -- a = 0
      subst haZero
      have hcImpl : List.count (0 : Int) (implementation nums).toList = 0 :=
        List.count_eq_zero_of_not_mem (a := (0 : Int)) (l := (implementation nums).toList) h0_notmem_impl
      have hcNums : List.count (0 : Int) nums.toList = 0 :=
        List.count_eq_zero_of_not_mem (a := (0 : Int)) (l := nums.toList) h0_notmem_nums
      simpa [hcImpl, hcNums]

    · -- 0 < a
      have haGt : a > 0 := by
        simpa [gt_iff_lt] using haPos

      have haPosB : isPosB a := by
        simpa [isPosB, haGt]

      have hc₁ : List.count a ((implementation nums).toList.filter isPosB) =
          List.count a (implementation nums).toList :=
        List.count_filter (l := (implementation nums).toList) (p := isPosB) (a := a) haPosB

      have hc₂ : List.count a (nums.toList.filter isPosB) = List.count a nums.toList :=
        List.count_filter (l := nums.toList) (p := isPosB) (a := a) haPosB

      calc
        List.count a (implementation nums).toList
            = List.count a ((implementation nums).toList.filter isPosB) := by
                simpa using hc₁.symm
        _ = List.count a (nums.toList.filter isPosB) := by
                simpa [hPosList]
        _ = List.count a nums.toList := by
                simpa using hc₂

theorem correctness_goal
    (nums : Array Int)
    (h_precond : precondition nums)
    : postcondition nums (implementation nums) := by
  classical
  have hpos_size : (nums.filter (fun x => x > 0)).size = nums.size / 2 := by
    expose_names; exact (correctness_goal_0 nums h_precond)
  have hneg_size : (nums.filter (fun x => x < 0)).size = nums.size / 2 := by
    expose_names; exact (correctness_goal_1 nums h_precond)
  have hsize : (implementation nums).size = nums.size := by
    expose_names; exact (correctness_goal_2 nums h_precond hpos_size)
  have halt : alternatesStartingPos (implementation nums) := by
    expose_names; exact (correctness_goal_3 nums hpos_size hneg_size hsize)
  have hstart : (implementation nums).size > 0 → (implementation nums)[0]! > 0 := by
    expose_names; exact (correctness_goal_4 nums hsize halt)
  have hstable : stableBySign nums (implementation nums) := by
    expose_names; exact (correctness_goal_5 nums hpos_size hneg_size)
  have hperm : (implementation nums).Perm nums := by
    expose_names; exact (correctness_goal_6 nums h_precond halt hstable)
  exact ⟨hsize, hperm, halt, hstart, hstable⟩
end Proof
