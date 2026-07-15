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
    ProductOfArrayExceptSelf: for each index i, return the product of all input elements except the one at i.
    **Important: complexity should be O(n) time and O(n) space**
    Natural language breakdown:
    1. Input is an array of integers `nums`.
    2. Output is an array `answer` of the same length as `nums`.
    3. For every valid index i, `answer[i]` equals the product of all `nums[j]` with j ≠ i.
    4. The relative order of indices is preserved: output position i corresponds to input position i.
    5. Multiplication uses the integer multiplicative identity 1 for the excluded element.
    6. Edge cases:
       - If the array is empty, the output is empty.
       - If the array has one element, the only output value is 1 (product over an empty set).
       - Zeros and negative values must be handled correctly.
    7. The problem statement guarantees that any prefix or suffix product fits in a 32-bit signed integer; we capture this as an input precondition.
    8. The algorithmic requirement “no division” is an implementation constraint; the mathematical result is uniquely determined by the product definition.
-/

section Specs
-- Signed 32-bit integer bounds expressed as Int.
def int32Min : Int := (-2147483648)
def int32Max : Int := (2147483647)

def InInt32 (z : Int) : Prop := int32Min ≤ z ∧ z ≤ int32Max

-- Product of the first k elements (a prefix), where k is intended to satisfy k ≤ nums.size.
def prefixProd (nums : Array Int) (k : Nat) : Int :=
  (Finset.range k).prod (fun (j : Nat) => nums[j]!)

-- Product of the suffix starting at index k, where k is intended to satisfy k ≤ nums.size.
def suffixProd (nums : Array Int) (k : Nat) : Int :=
  (Finset.range (nums.size - k)).prod (fun (t : Nat) => nums[k + t]!)

-- Product of all elements except the element at index i.
def prodExcept (nums : Array Int) (i : Nat) : Int :=
  (Finset.range nums.size).prod (fun (j : Nat) => if j = i then (1 : Int) else nums[j]!)

-- Preconditions
-- We encode the stated 32-bit safety guarantee for any prefix and suffix product.
def precondition (nums : Array Int) : Prop :=
  (∀ (k : Nat), k ≤ nums.size → InInt32 (prefixProd nums k)) ∧
  (∀ (k : Nat), k ≤ nums.size → InInt32 (suffixProd nums k))

-- Postconditions
-- 1) Output length matches input length.
-- 2) For each valid index i, result[i] is the product of all input elements except nums[i].
def postcondition (nums : Array Int) (answer : Array Int) : Prop :=
  answer.size = nums.size ∧
  (∀ (i : Nat), i < nums.size → answer[i]! = prodExcept nums i)
end Specs

section Impl
method ProductOfArrayExceptSelf (nums : Array Int)
  return (answer : Array Int)
  require precondition nums
  ensures postcondition nums answer
  do
  let n := nums.size
  -- First pass: compute prefix products into answer
  let mut ans := Array.replicate n (1 : Int)
  let mut i : Nat := 0
  let mut pref : Int := 1
  while i < n
    -- ans has fixed length n
    invariant "p1_size" ans.size = n
    -- i stays within bounds
    invariant "p1_i_bounds" i ≤ n
    -- pref equals product of nums[0..i)
    invariant "p1_pref" pref = prefixProd nums i
    -- computed prefix products stored in ans[0..i)
    invariant "p1_ans_prefix" (∀ k : Nat, k < i → ans[k]! = prefixProd nums k)
    decreasing n - i
  do
    ans := ans.set! i pref
    pref := pref * nums[i]!
    i := i + 1

  -- Second pass: multiply by suffix products
  let mut j : Nat := n
  let mut suff : Int := 1
  while j > 0
    -- ans has fixed length n
    invariant "p2_size" ans.size = n
    -- j stays within bounds
    invariant "p2_j_bounds" j ≤ n
    -- suff equals product of nums[j..n)
    invariant "p2_suff" suff = suffixProd nums j
    -- indices before j still hold prefix products
    invariant "p2_prefix_part" (∀ k : Nat, k < j → ans[k]! = prefixProd nums k)
    -- indices from j to end already have final product-except-self values
    invariant "p2_done_part" (∀ k : Nat, j ≤ k ∧ k < n → ans[k]! = prodExcept nums k)
    decreasing j
  do
    j := j - 1
    ans := ans.set! j (ans[j]! * suff)
    suff := suff * nums[j]!

  return ans
end Impl

section TestCases
-- Test case 1: Example 1
def test1_nums : Array Int := #[1, 2, 3, 4]
def test1_Expected : Array Int := #[24, 12, 8, 6]

-- Test case 2: Example 2
def test2_nums : Array Int := #[-1, 1, 0, -3, 3]
def test2_Expected : Array Int := #[0, 0, 9, 0, 0]

-- Test case 3: Empty array
def test3_nums : Array Int := (#[] : Array Int)
def test3_Expected : Array Int := (#[] : Array Int)

-- Test case 4: Singleton array
def test4_nums : Array Int := #[7]
def test4_Expected : Array Int := #[1]

-- Test case 5: Two elements
def test5_nums : Array Int := #[5, 6]
def test5_Expected : Array Int := #[6, 5]

-- Test case 6: Contains exactly one zero
def test6_nums : Array Int := #[0, 2, 3, 4]
def test6_Expected : Array Int := #[24, 0, 0, 0]

-- Test case 7: Contains two zeros
def test7_nums : Array Int := #[0, 2, 0, 4]
def test7_Expected : Array Int := #[0, 0, 0, 0]

-- Test case 8: All negative values
def test8_nums : Array Int := #[-1, -2, -3]
def test8_Expected : Array Int := #[6, 3, 2]

-- Test case 9: Mixed signs, no zeros
def test9_nums : Array Int := #[-2, 3, -4, 5]
def test9_Expected : Array Int := #[-60, 40, -30, 24]
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((ProductOfArrayExceptSelf test1_nums).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((ProductOfArrayExceptSelf test2_nums).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((ProductOfArrayExceptSelf test3_nums).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((ProductOfArrayExceptSelf test4_nums).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((ProductOfArrayExceptSelf test5_nums).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((ProductOfArrayExceptSelf test6_nums).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((ProductOfArrayExceptSelf test7_nums).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((ProductOfArrayExceptSelf test8_nums).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((ProductOfArrayExceptSelf test9_nums).run), DivM.res test9_Expected ]
end Assertions

section Pbt
velvet_plausible_test ProductOfArrayExceptSelf (config := { maxMs := some 20000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000

theorem goal_0
    (nums : Array ℤ)
    (ans : Array ℤ)
    (invariant_p1_size : ans.size = nums.size)
    : ans.size = nums.size := by
    intros; expose_names; try simp_all; try grind

theorem goal_1
    (nums : Array ℤ)
    (i : ℕ)
    : (∏ j ∈ Finset.range i, nums[j]!) * nums[i]! = ∏ j ∈ Finset.range (i + OfNat.ofNat 1), nums[j]! := by
    intros; expose_names; exact Eq.symm (Finset.prod_range_succ (getElem! nums) i)

theorem goal_2
    (nums : Array ℤ)
    (ans_1 : Array ℤ)
    (invariant_p2_size : ans_1.size = nums.size)
    : ans_1.size = nums.size := by
    intros; expose_names; try simp_all; try grind

theorem goal_3
    (nums : Array ℤ)
    (i_1 : Array ℤ)
    (i_2 : ℕ)
    (j : ℕ)
    (invariant_p2_j_bounds : j ≤ nums.size)
    (invariant_p1_size : i_1.size = nums.size)
    (invariant_p1_i_bounds : i_2 ≤ nums.size)
    (if_pos : OfNat.ofNat 0 < j)
    (done_1 : nums.size ≤ i_2)
    : (∏ t ∈ Finset.range (nums.size - j), nums[j + t]!) * nums[j - OfNat.ofNat 1]! = ∏ t ∈ Finset.range (nums.size - (j - OfNat.ofNat 1)), nums[j - OfNat.ofNat 1 + t]! := by
  set n : Nat := nums.size

  have hj0 : j ≠ 0 := Nat.ne_of_gt (by simpa using if_pos)
  have hjpred : j - 1 + 1 = j := by
    simpa using Nat.sub_one_add_one hj0
  have hjpred2 : 1 + (j - 1) = j := by
    simpa [Nat.add_comm] using hjpred

  have hjle : j ≤ n := by
    simpa [n] using invariant_p2_j_bounds
  have hjm1_lt_n : j - 1 < n := by
    omega

  have hsubpos : 0 < n - (j - 1) := Nat.sub_pos_of_lt hjm1_lt_n
  have hsubne : n - (j - 1) ≠ 0 := Nat.ne_of_gt hsubpos

  have hn : n - (j - 1) = (n - j) + 1 := by
    have hstep : n - (j - 1) = (n - (j - 1) - 1) + 1 := by
      simpa using (Nat.sub_one_add_one hsubne).symm
    have hsub : n - (j - 1) - 1 = n - ((j - 1) + 1) := by
      simpa [Nat.add_assoc] using (Nat.sub_sub n (j - 1) 1)
    calc
      n - (j - 1) = (n - ((j - 1) + 1)) + 1 := by simpa [hsub] using hstep
      _ = (n - j) + 1 := by simpa [hjpred]

  have hprod :
      (∏ t ∈ Finset.range (n - j), nums[j + t]!) * nums[j - 1]! =
        ∏ t ∈ Finset.range ((n - j) + 1), nums[(j - 1) + t]! := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, hjpred, hjpred2] using
      (Finset.prod_range_succ' (f := fun t => nums[(j - 1) + t]!) (n := n - j)).symm

  simpa [n, hn] using hprod

theorem goal_4
    (nums : Array ℤ)
    (ans_1 : Array ℤ)
    (j : ℕ)
    (invariant_p2_size : ans_1.size = nums.size)
    (invariant_p2_j_bounds : j ≤ nums.size)
    (invariant_p2_prefix_part : ∀ k < j, ans_1[k]! = ∏ j ∈ Finset.range k, nums[j]!)
    (invariant_p2_done_part : ∀ (k : ℕ), j ≤ k → k < nums.size → ans_1[k]! = ∏ j ∈ Finset.range nums.size, if j = k then OfNat.ofNat 1 else nums[j]!)
    (if_pos : OfNat.ofNat 0 < j)
    : ∀ (k : ℕ), j ≤ k + OfNat.ofNat 1 → k < nums.size → (ans_1.setIfInBounds (j - OfNat.ofNat 1) (ans_1[j - OfNat.ofNat 1]! * ∏ t ∈ Finset.range (nums.size - j), nums[j + t]!))[k]! = ∏ j ∈ Finset.range nums.size, if j = k then OfNat.ofNat 1 else nums[j]! := by
  intro k hjk hk
  classical
  set idx : Nat := j - 1
  set val : ℤ := ans_1[idx]! * ∏ t ∈ Finset.range (nums.size - j), nums[j + t]!

  have hj0 : 0 < j := if_pos

  have hidx_lt_j : idx < j := by
    have : Nat.pred j < j := Nat.pred_lt (Nat.ne_of_gt hj0)
    simpa [idx, Nat.pred_eq_sub_one] using this

  have hidx_lt_nums : idx < nums.size := lt_of_lt_of_le hidx_lt_j invariant_p2_j_bounds

  have hidx_lt_ans : idx < ans_1.size := by
    simpa [invariant_p2_size] using hidx_lt_nums

  have hidx_le_of_hjk : idx ≤ k := by
    exact (Nat.sub_le_iff_le_add).2 (by
      simpa [idx, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hjk)

  by_cases hkj : j ≤ k
  · -- k ≥ j, index is unchanged
    have hne : idx ≠ k := by
      have hlt : idx < k := lt_of_lt_of_le hidx_lt_j hkj
      exact Nat.ne_of_lt hlt

    have hset : (ans_1.setIfInBounds idx val)[k]! = ans_1[k]! := by
      simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne hne]

    simpa [hset] using invariant_p2_done_part k hkj hk

  · -- must be k = j - 1
    have hklt : k < j := Nat.lt_of_not_ge hkj
    have hk_le_idx : k ≤ idx := Nat.le_pred_of_lt hklt
    have hk_eq : k = idx := Nat.le_antisymm hk_le_idx hidx_le_of_hjk
    subst hk_eq

    have hset : (ans_1.setIfInBounds idx val)[idx]! = val := by
      simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, hidx_lt_ans, idx, val]

    have hpref : ans_1[idx]! = ∏ r ∈ Finset.range idx, nums[r]! := by
      simpa [idx] using invariant_p2_prefix_part idx hidx_lt_j

    have hsplitProd :
        (∏ r ∈ Finset.range nums.size, (if r = idx then (1 : ℤ) else nums[r]!))
          = (∏ r ∈ Finset.range idx, nums[r]!) * (∏ t ∈ Finset.range (nums.size - j), nums[j + t]!) := by
      classical
      let f : Nat → ℤ := fun r => if r = idx then (1 : ℤ) else nums[r]!
      have hidx_le_nums : idx ≤ nums.size := Nat.le_of_lt hidx_lt_nums

      have hmain : (∏ r ∈ Finset.range nums.size, f r)
          = (∏ r ∈ Finset.range idx, f r) * (∏ x ∈ Finset.range (nums.size - idx), f (idx + x)) := by
        simpa [Nat.add_sub_of_le hidx_le_nums] using (Finset.prod_range_add f idx (nums.size - idx))

      have hfirst : (∏ r ∈ Finset.range idx, f r) = ∏ r ∈ Finset.range idx, nums[r]! := by
        refine Finset.prod_congr rfl ?_
        intro r hr
        have hlt : r < idx := Finset.mem_range.mp hr
        have hne : r ≠ idx := hlt.ne
        simp [f, hne]

      have hidx_succ : idx + 1 = j := by
        have : j - 1 + 1 = j := Nat.sub_add_cancel (Nat.succ_le_of_lt hj0)
        simpa [idx, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

      have hmpos : 0 < nums.size - idx := Nat.sub_pos_of_lt hidx_lt_nums
      have hm1 : 1 ≤ nums.size - idx := Nat.succ_le_of_lt hmpos

      have hrestLen : nums.size - idx - 1 = nums.size - j := by
        have : nums.size - idx - 1 = nums.size - (idx + 1) := by
          simpa [Nat.sub_sub, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (Nat.sub_sub nums.size idx 1)
        simpa [hidx_succ] using this

      have hlen2 : 1 + (nums.size - j) = nums.size - idx := by
        have hm : (nums.size - idx) - 1 + 1 = nums.size - idx := Nat.sub_add_cancel hm1
        have : (nums.size - j) + 1 = nums.size - idx := by
          simpa [hrestLen] using hm
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this

      have hsecond : (∏ x ∈ Finset.range (nums.size - idx), f (idx + x))
            = ∏ t ∈ Finset.range (nums.size - j), nums[j + t]! := by
        have hsplit :
            (∏ x ∈ Finset.range (1 + (nums.size - j)), f (idx + x))
              = (∏ x ∈ Finset.range 1, f (idx + x)) * (∏ t ∈ Finset.range (nums.size - j), f (idx + (1 + t))) := by
          simpa [Nat.add_assoc] using
            (Finset.prod_range_add (fun x => f (idx + x)) 1 (nums.size - j))

        have hsplit' :
            (∏ x ∈ Finset.range (nums.size - idx), f (idx + x))
              = (∏ x ∈ Finset.range 1, f (idx + x)) * (∏ t ∈ Finset.range (nums.size - j), f (idx + (1 + t))) := by
          simpa [hlen2] using hsplit

        calc
          (∏ x ∈ Finset.range (nums.size - idx), f (idx + x))
              = (∏ x ∈ Finset.range 1, f (idx + x)) * (∏ t ∈ Finset.range (nums.size - j), f (idx + (1 + t))) := hsplit'
          _ = (1 : ℤ) * (∏ t ∈ Finset.range (nums.size - j), f (idx + (1 + t))) := by
                simp [f]
          _ = (∏ t ∈ Finset.range (nums.size - j), f (idx + (1 + t))) := by
                simp
          _ = (∏ t ∈ Finset.range (nums.size - j), nums[j + t]!) := by
                refine Finset.prod_congr rfl ?_
                intro t ht
                have hidx1 : idx + (1 + t) = j + t := by
                  calc
                    idx + (1 + t) = (idx + 1) + t := by
                      simp [Nat.add_assoc]
                    _ = j + t := by
                      simp [hidx_succ]
                have hgt : idx < j + t := by
                  have hjle : j ≤ j + t := Nat.le_add_right j t
                  exact lt_of_lt_of_le hidx_lt_j hjle
                have hne : (j + t) ≠ idx := Nat.ne_of_gt hgt
                simp [f, hidx1, hne]

      calc
        (∏ r ∈ Finset.range nums.size, (if r = idx then (1 : ℤ) else nums[r]!))
            = (∏ r ∈ Finset.range nums.size, f r) := by rfl
        _ = (∏ r ∈ Finset.range idx, f r) * (∏ x ∈ Finset.range (nums.size - idx), f (idx + x)) := hmain
        _ = (∏ r ∈ Finset.range idx, nums[r]!) * (∏ t ∈ Finset.range (nums.size - j), nums[j + t]!) := by
              simp [hfirst, hsecond]

    calc
      (ans_1.setIfInBounds idx val)[idx]!
          = val := hset
      _ = (∏ r ∈ Finset.range idx, nums[r]!) * (∏ t ∈ Finset.range (nums.size - j), nums[j + t]!) := by
            simp [val, hpref, mul_assoc]
      _ = ∏ r ∈ Finset.range nums.size, if r = idx then (1 : ℤ) else nums[r]! := by
            simpa using hsplitProd.symm
      _ = ∏ r ∈ Finset.range nums.size, if r = idx then OfNat.ofNat 1 else nums[r]! := by
            simp

theorem goal_5
    (nums : Array ℤ)
    (i_4 : Array ℤ)
    (i_5 : ℕ)
    (invariant_p2_size : i_4.size = nums.size)
    (invariant_p2_done_part : ∀ (k : ℕ), i_5 ≤ k → k < nums.size → i_4[k]! = ∏ j ∈ Finset.range nums.size, if j = k then OfNat.ofNat 1 else nums[j]!)
    (done_2 : i_5 = OfNat.ofNat 0)
    : postcondition nums i_4 := by
    intros; expose_names; try simp_all; try grind

set_option loom.solver "custom"

macro_rules
| `(tactic|loom_solver) => `(tactic|(
  try injections
  try subst_vars
  try grind (gen := 1)))


prove_correct ProductOfArrayExceptSelf by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at *); try (conv => congr <;> simp) ; try expose_names)
  exact (goal_0 nums ans invariant_p1_size)
  exact (goal_1 nums i)
  exact (goal_2 nums ans_1 invariant_p2_size)
  exact (goal_3 nums i_1 i_2 j invariant_p2_j_bounds invariant_p1_size invariant_p1_i_bounds if_pos done_1)
  exact (goal_4 nums ans_1 j invariant_p2_size invariant_p2_j_bounds invariant_p2_prefix_part invariant_p2_done_part if_pos)
  exact (goal_5 nums i_4 i_5 invariant_p2_size invariant_p2_done_part done_2)
end Proof
