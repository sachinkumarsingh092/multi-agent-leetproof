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
    MoveZeroes: Move all 0 values to the end of an integer array while preserving the relative order of non-zero elements.
    Natural language breakdown:
    1. Input is an array of integers.
    2. The output is an array of integers with the same length as the input.
    3. The output contains exactly the same multiset of values as the input (no values are lost or created).
    4. All non-zero elements appear before all zero elements in the output (zeros form a suffix).
    5. The relative order of the non-zero elements is preserved: scanning left-to-right, the sequence of non-zero values
       in the output is exactly the sequence of non-zero values in the input.
    Your algorithm should run in **O(n)** time and **O(1)** extra space (in-place).
-/

section Specs
-- Helper: count occurrences of a value in an array.
-- (Computable; used to express multiset preservation without defining a concrete implementation of MoveZeroes.)
def countVal (arr : Array Int) (v : Int) : Nat :=
  arr.foldl (fun (acc : Nat) (x : Int) => if x = v then acc + 1 else acc) 0

-- Helper: output has all zeros grouped at the end.
-- If a position is zero, everything to its right is also zero.
def zerosFormSuffix (output : Array Int) : Prop :=
  ∀ (k : Nat),
    k < output.size →
    output[k]! = 0 →
    ∀ (j : Nat), k < j → j < output.size → output[j]! = 0

-- Helper: a nonzero index predicate (kept small and decidable-looking).
def isNonZeroIndex (a : Array Int) (i : Nat) : Prop :=
  i < a.size ∧ a[i]! ≠ 0

-- Helper: the output nonzero prefix corresponds exactly to the input nonzero elements in order.
-- We use a strictly-increasing mapping f from input indices (where input[i] != 0) to output indices.
-- This expresses stability without giving an algorithm.
def preservesNonZeroOrder (input : Array Int) (output : Array Int) : Prop :=
  ∃ (f : Nat → Nat),
    (∀ (i : Nat), isNonZeroIndex input i → f i < output.size ∧ output[(f i)]! = input[i]!) ∧
    (∀ (i : Nat) (j : Nat), i < j → isNonZeroIndex input i → isNonZeroIndex input j → f i < f j) ∧
    (∀ (p : Nat), p < output.size → output[p]! ≠ 0 → ∃ (i : Nat), isNonZeroIndex input i ∧ f i = p)

-- Preconditions: none (any array is valid).
def precondition (nums : Array Int) : Prop :=
  True

-- Postcondition:
-- 1) same size
-- 2) same multiset of values (via per-value counts)
-- 3) zeros form a suffix
-- 4) stable preservation of the entire nonzero subsequence (via an order-isomorphism style mapping)
def postcondition (nums : Array Int) (result : Array Int) : Prop :=
  result.size = nums.size ∧
  (∀ (v : Int), countVal nums v = countVal result v) ∧
  zerosFormSuffix result ∧
  preservesNonZeroOrder nums result
end Specs

section Impl
method MoveZeroes (nums : Array Int)
  return (result : Array Int)
  require precondition nums
  ensures postcondition nums result
  do
    let n := nums.size

    -- First pass: compact all non-zero elements to the front (stable).
    let mut res := Array.replicate n (0 : Int)
    let mut write : Nat := 0
    let mut i : Nat := 0
    while i < n
      invariant "mz1_size" res.size = n
      invariant "mz1_bounds" write ≤ i ∧ i ≤ n
      -- Written prefix contains only nonzeros.
      invariant "mz1_prefixNonZero" (∀ (k : Nat), k < write → res[k]! ≠ (0 : Int))
      -- Unwritten suffix stays zero.
      invariant "mz1_suffixZero" (∀ (k : Nat), write ≤ k → k < n → res[k]! = (0 : Int))
      -- write equals number of nonzeros seen so far in nums[0..i).
      invariant "mz1_writeCount" write = i - countVal (nums.extract 0 i) (0 : Int)
      -- For any nonzero value, res has exactly the occurrences from nums[0..i).
      invariant "mz1_countsNonZero"
        (∀ (v : Int), v ≠ (0 : Int) → countVal res v = countVal (nums.extract 0 i) v)
      -- Stability/order for the processed prefix into res.
      invariant "mz1_order" preservesNonZeroOrder (nums.extract 0 i) res
      decreasing n - i
    do
      let x := nums[i]!
      if x = 0 then
        i := i + 1
        continue
      res := res.set! write x
      write := write + 1
      i := i + 1

    -- Second pass: fill the remainder with zeros.
    let mut j : Nat := write
    while j < n
      invariant "mz2_size" res.size = n
      invariant "mz2_bounds" write ≤ j ∧ j ≤ n
      invariant "mz2_prefixNonZero" (∀ (k : Nat), k < write → res[k]! ≠ (0 : Int))
      invariant "mz2_suffixZero" (∀ (k : Nat), write ≤ k → k < n → res[k]! = (0 : Int))
      -- Full multiset preservation expressed by per-value counts.
      invariant "mz2_counts" (∀ (v : Int), countVal nums v = countVal res v)
      -- Full stability/order property (now that all inputs have been scanned).
      invariant "mz2_order" preservesNonZeroOrder nums res
      decreasing n - j
    do
      res := res.set! j (0 : Int)
      j := j + 1

    return res
end Impl

section TestCases
-- Test case 1: Example 1
-- Input: [0,1,0,3,12]
-- Output: [1,3,12,0,0]
def test1_nums : Array Int := #[0, 1, 0, 3, 12]
def test1_Expected : Array Int := #[1, 3, 12, 0, 0]

-- Test case 2: Example 2
-- Input: [0]
-- Output: [0]
def test2_nums : Array Int := #[0]
def test2_Expected : Array Int := #[0]

-- Test case 3: Empty array
-- Input: []
-- Output: []
def test3_nums : Array Int := #[]
def test3_Expected : Array Int := #[]

-- Test case 4: No zeros
-- Input: [1,2,3]
-- Output: [1,2,3]
def test4_nums : Array Int := #[1, 2, 3]
def test4_Expected : Array Int := #[1, 2, 3]

-- Test case 5: All zeros
-- Input: [0,0,0]
-- Output: [0,0,0]
def test5_nums : Array Int := #[0, 0, 0]
def test5_Expected : Array Int := #[0, 0, 0]

-- Test case 6: Zeros already at end
-- Input: [5,0,0]
-- Output: [5,0,0]
def test6_nums : Array Int := #[5, 0, 0]
def test6_Expected : Array Int := #[5, 0, 0]

-- Test case 7: Alternating including negatives
-- Input: [0,-1,0,-2,3]
-- Output: [-1,-2,3,0,0]
def test7_nums : Array Int := #[0, -1, 0, -2, 3]
def test7_Expected : Array Int := #[-1, -2, 3, 0, 0]

-- Test case 8: Duplicates of non-zero values and multiple zeros
-- Input: [1,0,1,0,1]
-- Output: [1,1,1,0,0]
def test8_nums : Array Int := #[1, 0, 1, 0, 1]
def test8_Expected : Array Int := #[1, 1, 1, 0, 0]

-- Test case 9: Mix with repeated negatives and zeros
-- Input: [-1,0,-1,2,0]
-- Output: [-1,-1,2,0,0]
def test9_nums : Array Int := #[-1, 0, -1, 2, 0]
def test9_Expected : Array Int := #[-1, -1, 2, 0, 0]

-- Recommend to validate: MoveZeroes, precondition, postcondition
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((MoveZeroes test1_nums).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((MoveZeroes test2_nums).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((MoveZeroes test3_nums).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((MoveZeroes test4_nums).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((MoveZeroes test5_nums).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((MoveZeroes test6_nums).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((MoveZeroes test7_nums).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((MoveZeroes test8_nums).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((MoveZeroes test9_nums).run), DivM.res test9_Expected ]
end Assertions

section Pbt
velvet_plausible_test MoveZeroes (config := { maxMs := some 20000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000

theorem goal_0
    (nums : Array ℤ)
    (i : ℕ)
    (a_1 : i ≤ nums.size)
    (if_pos : i < nums.size)
    (if_pos_1 : nums[i]! = OfNat.ofNat 0)
    (a : i - countVal (nums.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0) ≤ i)
    : i - Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 1 else acc) (OfNat.ofNat 0) (nums.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0) (min i nums.size) = i + OfNat.ofNat 1 - Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 1 else acc) (OfNat.ofNat 0) (nums.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) (OfNat.ofNat 0) (min (i + OfNat.ofNat 1) nums.size) := by
  classical
  let f : Nat → ℤ → Nat := fun acc x => if x = (0 : ℤ) then acc + 1 else acc

  -- rewrite the goal to use `f`
  change i - Array.foldl f 0 (nums.extract 0 i) 0 (min i nums.size) =
      i + 1 - Array.foldl f 0 (nums.extract 0 (i + 1)) 0 (min (i + 1) nums.size)

  have hi1 : i + 1 ≤ nums.size := Nat.succ_le_of_lt if_pos

  -- simplify the `min` bounds
  simp [Nat.min_eq_left a_1, Nat.min_eq_left hi1]

  -- `get!` agrees with `getElem` in-bounds
  have hget : nums[i]! = nums[i] := by
    -- unfold `get!` into `getD`, then evaluate in-bounds
    simp [Array.getElem!_eq_getD, Array.getD, if_pos]

  have hx0 : nums[i] = (0 : ℤ) := by
    simpa [hget] using if_pos_1

  -- relate the two prefixes by pushing the i-th element
  have hextract : (nums.extract 0 i).push nums[i] = nums.extract 0 (i + 1) := by
    -- use the library lemma about `extract` and `push`
    simpa [Nat.min_eq_left (Nat.zero_le i)] using (@Array.push_extract_getElem ℤ nums 0 i if_pos)

  -- size of the i-prefix extract
  have hsize_i : (nums.extract 0 i).size = i := by
    simpa [Array.size_extract, Nat.min_eq_left a_1] using (rfl : (nums.extract 0 i).size = (nums.extract 0 i).size)

  -- show the fold count increases by 1 when we extend by a zero
  have hfold_succ :
      Array.foldl f 0 (nums.extract 0 (i + 1)) 0 (i + 1) =
        Nat.succ (Array.foldl f 0 (nums.extract 0 i) 0 i) := by
    -- rewrite `extract 0 (i+1)` as push, then as append singleton
    rw [← hextract]
    -- fold over `push` using `append singleton`
    rw [Array.push_eq_append_singleton]
    -- apply foldl over append
    have w : (i + 1) = (nums.extract 0 i).size + (#[nums[i]] : Array ℤ).size := by
      simp [hsize_i]
    have happ := (Array.foldl_append' (f := f) (b := 0) (xs := nums.extract 0 i)
        (ys := (#[nums[i]] : Array ℤ)) (stop := i + 1) w)
    -- simplify the singleton fold and use `nums[i] = 0`
    -- `xs.foldl f b` uses the default full range, which is `0 .. xs.size`.
    simpa [w, f, hx0, hsize_i, Nat.succ_eq_add_one] using happ

  -- finish by rewriting both sides as `succ` subtraction
  have hs := (Nat.succ_sub_succ_eq_sub i (Array.foldl f 0 (nums.extract 0 i) 0 i))
  -- rewrite the RHS fold using `hfold_succ`
  simpa [Nat.succ_eq_add_one, hfold_succ] using hs.symm

theorem goal_1
    (nums : Array ℤ)
    (i : ℕ)
    (res : Array ℤ)
    (invariant_mz1_countsNonZero : ∀ (v : ℤ), v ≠ OfNat.ofNat 0 → countVal res v = countVal (nums.extract (OfNat.ofNat 0) i) v)
    (if_pos : i < nums.size)
    (if_pos_1 : nums[i]! = OfNat.ofNat 0)
    : ∀ (v : ℤ), v ≠ OfNat.ofNat 0 → countVal res v = countVal (nums.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) v := by
  intro v hv

  have hx0 : nums[i]'if_pos = (0 : ℤ) := by
    simpa [getElem!_pos nums i if_pos] using if_pos_1

  have hpush : (nums.extract 0 i).push (nums[i]'if_pos) = nums.extract 0 (i + 1) := by
    simpa [Nat.min_eq_left (Nat.zero_le i)] using
      (@Array.push_extract_getElem ℤ nums 0 i if_pos)

  have hne : (0 : ℤ) ≠ v := by
    intro h
    exact hv h.symm

  have hcount_push : countVal ((nums.extract 0 i).push (nums[i]'if_pos)) v = countVal (nums.extract 0 i) v := by
    -- Move `Array.foldl` to `List.foldl` via `toList`.
    unfold countVal
    -- rewrite both sides to list folds
    simp [Array.foldl_toList, Array.push_toList, List.foldl_append, hx0, hne]

  have hcount_extract : countVal (nums.extract 0 i) v = countVal (nums.extract 0 (i + 1)) v := by
    have hpush' : nums.extract 0 (i + 1) = (nums.extract 0 i).push (nums[i]'if_pos) := by
      simpa using hpush.symm
    rw [hpush']
    simpa using hcount_push.symm

  calc
    countVal res v = countVal (nums.extract 0 i) v := by
      simpa using (invariant_mz1_countsNonZero v hv)
    _ = countVal (nums.extract 0 (i + 1)) v := by
      simpa using hcount_extract

theorem goal_2
    (nums : Array ℤ)
    (i : ℕ)
    (res : Array ℤ)
    (a_1 : i ≤ nums.size)
    (invariant_mz1_order : preservesNonZeroOrder (nums.extract (OfNat.ofNat 0) i) res)
    (if_pos : i < nums.size)
    (if_pos_1 : nums[i]! = OfNat.ofNat 0)
    (a : i - countVal (nums.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0) ≤ i)
    : preservesNonZeroOrder (nums.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) res := by
  rcases invariant_mz1_order with ⟨f, hf_ok, hf_mono, hf_surj⟩

  have hi1le : i + 1 ≤ nums.size := Nat.succ_le_of_lt if_pos

  have hsize_i : (nums.extract 0 i).size = i := by
    simpa [Array.size_extract, Nat.sub_zero, Nat.min_eq_left a_1]
  have hsize_succ : (nums.extract 0 (i + 1)).size = i + 1 := by
    simpa [Array.size_extract, Nat.sub_zero, Nat.min_eq_left hi1le]

  -- Values in a prefix extract as `get!`.
  have extract_get! : ∀ (stop : Nat) (hstop : stop ≤ nums.size) (t : Nat),
      t < stop → (nums.extract 0 stop)[t]! = nums[t]! := by
    intro stop hstop t ht
    have ht_nums : t < nums.size := lt_of_lt_of_le ht hstop
    have hleft : t < stop ∧ t < nums.size := ⟨ht, ht_nums⟩
    -- `get!` is implemented via `getD`, and for prefix extracts the bounds reduce to `t < stop ∧ t < nums.size`.
    simp [Array.getElem!_eq_getD, Array.getD, hleft, ht_nums]

  have h_i_zero : (nums.extract 0 (i + 1))[i]! = (0 : ℤ) := by
    simpa [if_pos_1] using (extract_get! (i + 1) hi1le i (Nat.lt_succ_self i))

  have lt_i_of_nz_succ : ∀ t, isNonZeroIndex (nums.extract 0 (i + 1)) t → t < i := by
    intro t ht
    have ht_lt_succ : t < i + 1 := by
      simpa [hsize_succ] using ht.1
    have ht_le : t ≤ i := Nat.lt_succ_iff.mp ht_lt_succ
    have ht_ne : t ≠ i := by
      intro hti
      apply ht.2
      simpa [hti, h_i_zero]
    exact Nat.lt_of_le_of_ne ht_le ht_ne

  refine ⟨f, ?_, ?_, ?_⟩

  · intro t ht
    have ht_lt : t < i := lt_i_of_nz_succ t ht
    have ht_lt_succ : t < i + 1 := Nat.lt_trans ht_lt (Nat.lt_succ_self i)

    have hEq : (nums.extract 0 i)[t]! = (nums.extract 0 (i + 1))[t]! := by
      calc
        (nums.extract 0 i)[t]! = nums[t]! := extract_get! i a_1 t ht_lt
        _ = (nums.extract 0 (i + 1))[t]! := (extract_get! (i + 1) hi1le t ht_lt_succ).symm

    have ht_old : isNonZeroIndex (nums.extract 0 i) t := by
      refine ⟨?_, ?_⟩
      · simpa [hsize_i] using ht_lt
      · intro h0
        apply ht.2
        have : (nums.extract 0 (i + 1))[t]! = (0 : ℤ) := by
          simpa [hEq] using h0
        simpa [this]

    rcases hf_ok t ht_old with ⟨hft, hres⟩
    refine ⟨hft, ?_⟩
    simpa [hEq] using hres

  · intro t u htu ht hu
    have ht_lt : t < i := lt_i_of_nz_succ t ht
    have hu_lt : u < i := lt_i_of_nz_succ u hu

    have ht_lt_succ : t < i + 1 := Nat.lt_trans ht_lt (Nat.lt_succ_self i)
    have hu_lt_succ : u < i + 1 := Nat.lt_trans hu_lt (Nat.lt_succ_self i)

    have hEq_t : (nums.extract 0 i)[t]! = (nums.extract 0 (i + 1))[t]! := by
      calc
        (nums.extract 0 i)[t]! = nums[t]! := extract_get! i a_1 t ht_lt
        _ = (nums.extract 0 (i + 1))[t]! := (extract_get! (i + 1) hi1le t ht_lt_succ).symm

    have hEq_u : (nums.extract 0 i)[u]! = (nums.extract 0 (i + 1))[u]! := by
      calc
        (nums.extract 0 i)[u]! = nums[u]! := extract_get! i a_1 u hu_lt
        _ = (nums.extract 0 (i + 1))[u]! := (extract_get! (i + 1) hi1le u hu_lt_succ).symm

    have ht_old : isNonZeroIndex (nums.extract 0 i) t := by
      refine ⟨?_, ?_⟩
      · simpa [hsize_i] using ht_lt
      · intro h0
        apply ht.2
        have : (nums.extract 0 (i + 1))[t]! = (0 : ℤ) := by
          simpa [hEq_t] using h0
        simpa [this]

    have hu_old : isNonZeroIndex (nums.extract 0 i) u := by
      refine ⟨?_, ?_⟩
      · simpa [hsize_i] using hu_lt
      · intro h0
        apply hu.2
        have : (nums.extract 0 (i + 1))[u]! = (0 : ℤ) := by
          simpa [hEq_u] using h0
        simpa [this]

    exact hf_mono t u htu ht_old hu_old

  · intro p hp hpnz
    rcases hf_surj p hp hpnz with ⟨t, ht_old, hfp⟩

    have ht_lt : t < i := by
      simpa [hsize_i] using ht_old.1
    have ht_lt_succ : t < i + 1 := Nat.lt_trans ht_lt (Nat.lt_succ_self i)

    have hEq : (nums.extract 0 i)[t]! = (nums.extract 0 (i + 1))[t]! := by
      calc
        (nums.extract 0 i)[t]! = nums[t]! := extract_get! i a_1 t ht_lt
        _ = (nums.extract 0 (i + 1))[t]! := (extract_get! (i + 1) hi1le t ht_lt_succ).symm

    have ht_new : isNonZeroIndex (nums.extract 0 (i + 1)) t := by
      refine ⟨?_, ?_⟩
      · simpa [hsize_succ] using ht_lt_succ
      · intro h0
        apply ht_old.2
        have : (nums.extract 0 i)[t]! = (0 : ℤ) := by
          simpa [hEq.symm] using h0
        simpa [this]

    exact ⟨t, ht_new, hfp⟩



theorem goal_3
    (nums : Array ℤ)
    (require_1 : precondition nums)
    (i : ℕ)
    (res : Array ℤ)
    (invariant_mz1_size : res.size = nums.size)
    (a_1 : i ≤ nums.size)
    (invariant_mz1_countsNonZero : ∀ (v : ℤ), v ≠ OfNat.ofNat 0 → countVal res v = countVal (nums.extract (OfNat.ofNat 0) i) v)
    (invariant_mz1_order : preservesNonZeroOrder (nums.extract (OfNat.ofNat 0) i) res)
    (if_pos : i < nums.size)
    (if_neg : ¬nums[i]! = OfNat.ofNat 0)
    (a : i - countVal (nums.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0) ≤ i)
    (invariant_mz1_prefixNonZero : ∀ k < i - countVal (nums.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0), res[k]! ≠ OfNat.ofNat 0)
    (invariant_mz1_suffixZero : ∀ (k : ℕ), i - countVal (nums.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0) ≤ k → k < nums.size → res[k]! = OfNat.ofNat 0)
    : i - Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 1 else acc) (OfNat.ofNat 0) (nums.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0) (min i nums.size) + OfNat.ofNat 1 = i + OfNat.ofNat 1 - Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 1 else acc) (OfNat.ofNat 0) (nums.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) (OfNat.ofNat 0) (min (i + OfNat.ofNat 1) nums.size) := by
    sorry

theorem goal_4
    (nums : Array ℤ)
    (require_1 : precondition nums)
    (i : ℕ)
    (res : Array ℤ)
    (invariant_mz1_size : res.size = nums.size)
    (a_1 : i ≤ nums.size)
    (invariant_mz1_countsNonZero : ∀ (v : ℤ), v ≠ OfNat.ofNat 0 → countVal res v = countVal (nums.extract (OfNat.ofNat 0) i) v)
    (invariant_mz1_order : preservesNonZeroOrder (nums.extract (OfNat.ofNat 0) i) res)
    (if_pos : i < nums.size)
    (if_neg : ¬nums[i]! = OfNat.ofNat 0)
    (a : i - countVal (nums.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0) ≤ i)
    (invariant_mz1_prefixNonZero : ∀ k < i - countVal (nums.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0), res[k]! ≠ OfNat.ofNat 0)
    (invariant_mz1_suffixZero : ∀ (k : ℕ), i - countVal (nums.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0) ≤ k → k < nums.size → res[k]! = OfNat.ofNat 0)
    : ∀ (v : ℤ), v ≠ OfNat.ofNat 0 → countVal (res.set! (i - countVal (nums.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0)) nums[i]!) v = countVal (nums.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) v := by
    sorry

theorem goal_5
    (nums : Array ℤ)
    (require_1 : precondition nums)
    (i : ℕ)
    (res : Array ℤ)
    (invariant_mz1_size : res.size = nums.size)
    (a_1 : i ≤ nums.size)
    (invariant_mz1_countsNonZero : ∀ (v : ℤ), v ≠ OfNat.ofNat 0 → countVal res v = countVal (nums.extract (OfNat.ofNat 0) i) v)
    (invariant_mz1_order : preservesNonZeroOrder (nums.extract (OfNat.ofNat 0) i) res)
    (if_pos : i < nums.size)
    (if_neg : ¬nums[i]! = OfNat.ofNat 0)
    (a : i - countVal (nums.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0) ≤ i)
    (invariant_mz1_prefixNonZero : ∀ k < i - countVal (nums.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0), res[k]! ≠ OfNat.ofNat 0)
    (invariant_mz1_suffixZero : ∀ (k : ℕ), i - countVal (nums.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0) ≤ k → k < nums.size → res[k]! = OfNat.ofNat 0)
    : preservesNonZeroOrder (nums.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) (res.setIfInBounds (i - Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 1 else acc) (OfNat.ofNat 0) (nums.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0) (min i nums.size)) nums[i]!) := by
    sorry

theorem goal_6
    (nums : Array ℤ)
    (require_1 : precondition nums)
    : ∀ (v : ℤ), v ≠ OfNat.ofNat 0 → countVal (Array.replicate nums.size (OfNat.ofNat 0)) v = countVal (nums.extract (OfNat.ofNat 0) (OfNat.ofNat 0)) v := by
    sorry

theorem goal_7
    (nums : Array ℤ)
    (require_1 : precondition nums)
    : preservesNonZeroOrder #[] (Array.replicate nums.size (OfNat.ofNat 0)) := by
    sorry

theorem goal_8
    (nums : Array ℤ)
    (require_1 : precondition nums)
    (i_1 : ℕ)
    (i_2 : Array ℤ)
    (j : ℕ)
    (res_1 : Array ℤ)
    (invariant_mz2_size : res_1.size = nums.size)
    (a_3 : j ≤ nums.size)
    (invariant_mz2_counts : ∀ (v : ℤ), countVal nums v = countVal res_1 v)
    (invariant_mz2_order : preservesNonZeroOrder nums res_1)
    (if_pos : j < nums.size)
    (a_1 : i_1 ≤ nums.size)
    (done_1 : ¬i_1 < nums.size)
    (invariant_mz1_size : i_2.size = nums.size)
    (invariant_mz1_countsNonZero : ∀ (v : ℤ), v ≠ OfNat.ofNat 0 → countVal i_2 v = countVal (nums.extract (OfNat.ofNat 0) i_1) v)
    (invariant_mz1_order : preservesNonZeroOrder (nums.extract (OfNat.ofNat 0) i_1) i_2)
    (a_2 : i_1 - countVal (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) ≤ j)
    (invariant_mz2_prefixNonZero : ∀ k < i_1 - countVal (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0), res_1[k]! ≠ OfNat.ofNat 0)
    (invariant_mz2_suffixZero : ∀ (k : ℕ), i_1 - countVal (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) ≤ k → k < nums.size → res_1[k]! = OfNat.ofNat 0)
    (a : i_1 - countVal (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) ≤ i_1)
    (invariant_mz1_prefixNonZero : ∀ k < i_1 - countVal (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0), i_2[k]! ≠ OfNat.ofNat 0)
    (invariant_mz1_suffixZero : ∀ (k : ℕ), i_1 - countVal (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) ≤ k → k < nums.size → i_2[k]! = OfNat.ofNat 0)
    : ∀ (v : ℤ), countVal nums v = countVal (res_1.set! j (OfNat.ofNat 0)) v := by
    sorry

theorem goal_9
    (nums : Array ℤ)
    (require_1 : precondition nums)
    (i_1 : ℕ)
    (i_2 : Array ℤ)
    (j : ℕ)
    (res_1 : Array ℤ)
    (invariant_mz2_size : res_1.size = nums.size)
    (a_3 : j ≤ nums.size)
    (invariant_mz2_counts : ∀ (v : ℤ), countVal nums v = countVal res_1 v)
    (invariant_mz2_order : preservesNonZeroOrder nums res_1)
    (if_pos : j < nums.size)
    (a_1 : i_1 ≤ nums.size)
    (done_1 : ¬i_1 < nums.size)
    (invariant_mz1_size : i_2.size = nums.size)
    (invariant_mz1_countsNonZero : ∀ (v : ℤ), v ≠ OfNat.ofNat 0 → countVal i_2 v = countVal (nums.extract (OfNat.ofNat 0) i_1) v)
    (invariant_mz1_order : preservesNonZeroOrder (nums.extract (OfNat.ofNat 0) i_1) i_2)
    (a_2 : i_1 - countVal (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) ≤ j)
    (invariant_mz2_prefixNonZero : ∀ k < i_1 - countVal (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0), res_1[k]! ≠ OfNat.ofNat 0)
    (invariant_mz2_suffixZero : ∀ (k : ℕ), i_1 - countVal (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) ≤ k → k < nums.size → res_1[k]! = OfNat.ofNat 0)
    (a : i_1 - countVal (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) ≤ i_1)
    (invariant_mz1_prefixNonZero : ∀ k < i_1 - countVal (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0), i_2[k]! ≠ OfNat.ofNat 0)
    (invariant_mz1_suffixZero : ∀ (k : ℕ), i_1 - countVal (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) ≤ k → k < nums.size → i_2[k]! = OfNat.ofNat 0)
    : preservesNonZeroOrder nums (res_1.setIfInBounds j (OfNat.ofNat 0)) := by
    sorry

theorem goal_10
    (nums : Array ℤ)
    (require_1 : precondition nums)
    (i_1 : ℕ)
    (i_2 : Array ℤ)
    (a_1 : i_1 ≤ nums.size)
    (done_1 : ¬i_1 < nums.size)
    (invariant_mz1_size : i_2.size = nums.size)
    (invariant_mz1_countsNonZero : ∀ (v : ℤ), v ≠ OfNat.ofNat 0 → countVal i_2 v = countVal (nums.extract (OfNat.ofNat 0) i_1) v)
    (invariant_mz1_order : preservesNonZeroOrder (nums.extract (OfNat.ofNat 0) i_1) i_2)
    (a : i_1 - countVal (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) ≤ i_1)
    (invariant_mz1_prefixNonZero : ∀ k < i_1 - countVal (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0), i_2[k]! ≠ OfNat.ofNat 0)
    (invariant_mz1_suffixZero : ∀ (k : ℕ), i_1 - countVal (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) ≤ k → k < nums.size → i_2[k]! = OfNat.ofNat 0)
    : ∀ (v : ℤ), countVal nums v = countVal i_2 v := by
    sorry

theorem goal_11
    (nums : Array ℤ)
    (require_1 : precondition nums)
    (i_1 : ℕ)
    (i_2 : Array ℤ)
    (a_1 : i_1 ≤ nums.size)
    (done_1 : ¬i_1 < nums.size)
    (invariant_mz1_size : i_2.size = nums.size)
    (invariant_mz1_countsNonZero : ∀ (v : ℤ), v ≠ OfNat.ofNat 0 → countVal i_2 v = countVal (nums.extract (OfNat.ofNat 0) i_1) v)
    (invariant_mz1_order : preservesNonZeroOrder (nums.extract (OfNat.ofNat 0) i_1) i_2)
    (a : i_1 - countVal (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) ≤ i_1)
    (invariant_mz1_prefixNonZero : ∀ k < i_1 - countVal (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0), i_2[k]! ≠ OfNat.ofNat 0)
    (invariant_mz1_suffixZero : ∀ (k : ℕ), i_1 - countVal (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) ≤ k → k < nums.size → i_2[k]! = OfNat.ofNat 0)
    : preservesNonZeroOrder nums i_2 := by
    sorry


set_option loom.solver "custom"

macro_rules
| `(tactic|loom_solver) => `(tactic|(
  try injections
  try subst_vars
  try grind (gen := 4)))


prove_correct MoveZeroes by
  loom_solve <;> (try injections; try subst_vars; try (conv => congr <;> simp) ; try expose_names)
  exact (goal_0 nums i a_1 if_pos if_pos_1 a)
  exact (goal_1 nums i res invariant_mz1_countsNonZero if_pos if_pos_1)
  exact (goal_2 nums i res a_1 invariant_mz1_order if_pos if_pos_1 a)
  exact (goal_3 nums require_1 i res invariant_mz1_size a_1 invariant_mz1_countsNonZero invariant_mz1_order if_pos if_neg a invariant_mz1_prefixNonZero invariant_mz1_suffixZero)
  exact (goal_4 nums require_1 i res invariant_mz1_size a_1 invariant_mz1_countsNonZero invariant_mz1_order if_pos if_neg a invariant_mz1_prefixNonZero invariant_mz1_suffixZero)
  exact (goal_5 nums require_1 i res invariant_mz1_size a_1 invariant_mz1_countsNonZero invariant_mz1_order if_pos if_neg a invariant_mz1_prefixNonZero invariant_mz1_suffixZero)
  exact (goal_6 nums require_1)
  exact (goal_7 nums require_1)
  exact (goal_8 nums require_1 i_1 i_2 j res_1 invariant_mz2_size a_3 invariant_mz2_counts invariant_mz2_order if_pos a_1 done_1 invariant_mz1_size invariant_mz1_countsNonZero invariant_mz1_order a_2 invariant_mz2_prefixNonZero invariant_mz2_suffixZero a invariant_mz1_prefixNonZero invariant_mz1_suffixZero)
  exact (goal_9 nums require_1 i_1 i_2 j res_1 invariant_mz2_size a_3 invariant_mz2_counts invariant_mz2_order if_pos a_1 done_1 invariant_mz1_size invariant_mz1_countsNonZero invariant_mz1_order a_2 invariant_mz2_prefixNonZero invariant_mz2_suffixZero a invariant_mz1_prefixNonZero invariant_mz1_suffixZero)
  exact (goal_10 nums require_1 i_1 i_2 a_1 done_1 invariant_mz1_size invariant_mz1_countsNonZero invariant_mz1_order a invariant_mz1_prefixNonZero invariant_mz1_suffixZero)
  exact (goal_11 nums require_1 i_1 i_2 a_1 done_1 invariant_mz1_size invariant_mz1_countsNonZero invariant_mz1_order a invariant_mz1_prefixNonZero invariant_mz1_suffixZero)
end Proof
