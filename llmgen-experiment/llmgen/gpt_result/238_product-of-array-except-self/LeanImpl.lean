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
def implementation (nums : Array Int) : Array Int :=
  let n := nums.size
  -- Build prefix products: pref[i] = product of nums[0..i-1], with pref[0] = 1
  let pref :=
    (nums.foldl
      (fun (acc : Int × Array Int) (x : Int) =>
        let p := acc.1
        let arr := acc.2
        (p * x, arr.push p))
      ((1 : Int), (#[] : Array Int))).2
  -- Build suffix products from the right: suffRev[i] corresponds to suffix product after index (n-1-i)
  -- Invariant: at each step, we push current suffix product (product of elements strictly to the right).
  let suffRev :=
    ((nums.foldr
      (fun (x : Int) (acc : Int × Array Int) =>
        let s := acc.1
        let arr := acc.2
        (x * s, arr.push s))
      ((1 : Int), (#[] : Array Int))).2)
  -- Combine: answer[i] = pref[i] * suff[n-1-i]
  Array.ofFn (fun i : Fin n =>
    pref[i.1]! * suffRev[(n - 1 - i.1)]!)
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
    (i : ℕ)
    (hi : i < nums.size)
    : (Array.foldl
        (fun acc x =>
          let p := acc.1;
          let arr := acc.2;
          (p * x, arr.push p))
        (1, #[]) nums).2[i]! =
  prefixProd nums i := by
  classical
  set step : (Int × Array Int) → Int → (Int × Array Int) := fun acc x =>
    let p := acc.1
    let arr := acc.2
    (p * x, arr.push p)

  have array_get!_eq_list_get! (xs : Array Int) (k : Nat) : xs[k]! = xs.toList[k]! := by
    have hta : xs.toList.toArray = xs := Array.toArray_toList (xs := xs)
    have hk : (xs.toList.toArray)[k]! = xs[k]! := congrArg (fun a : Array Int => a[k]!) hta
    calc
      xs[k]! = (xs.toList.toArray)[k]! := by simpa using hk.symm
      _ = xs.toList[k]! := by
        simpa using (List.getElem!_toArray (xs := xs.toList) (i := k))

  have list_get!_take (xs : List Int) (n k : Nat) (hk : k < n) : (xs.take n)[k]! = xs[k]! := by
    simp [List.getElem!_eq_getElem?_getD, List.getElem?_take, hk]

  have foldl_step_toList :
      ∀ (l : List Int) (p : Int) (arr : Array Int),
        (l.foldl step (p, arr)).2.toList =
          arr.toList ++ (List.scanl (fun q x => q * x) p l).take l.length := by
    intro l
    induction l with
    | nil =>
        intro p arr
        simp [List.scanl_nil, step]
    | cons a l ih =>
        intro p arr
        simp [List.foldl_cons, step, ih, List.scanl_cons, Array.push_toList, List.take, List.append_assoc]

  set l : List Int := nums.toList
  have hlen : l.length = nums.size := by
    simpa [l] using (Array.length_toList (xs := nums))

  have hpref_toList :
      (nums.foldl step (1, (#[] : Array Int))).2.toList =
        (List.scanl (fun q x => q * x) 1 l).take l.length := by
    let init : Int × Array Int := (1, (#[] : Array Int))
    have hfold_list : l.foldl step init = nums.foldl step init := by
      -- `foldl_toList` gives `nums.toList.foldl = nums.foldl`
      simpa [l, init] using (Array.foldl_toList (f := step) (init := init) (xs := nums))
    -- transport along equality and apply the list lemma
    have hto : (nums.foldl step init).2.toList = (l.foldl step init).2.toList := by
      simpa [hfold_list] using (congrArg (fun t : Int × Array Int => t.2.toList) hfold_list.symm)
    -- now use the lemma for `l`
    -- `foldl_step_toList` gives `(l.foldl ...).2.toList = ...`.
    calc
      (nums.foldl step init).2.toList = (l.foldl step init).2.toList := hto
      _ = (List.scanl (fun q x => q * x) 1 l).take l.length := by
        simpa [init] using (foldl_step_toList l 1 (#[] : Array Int))

  set pref : Array Int := (nums.foldl step (1, (#[] : Array Int))).2

  have hpref_get : pref[i]! = ((List.scanl (fun q x => q * x) 1 l).take l.length)[i]! := by
    have : pref.toList = (List.scanl (fun q x => q * x) 1 l).take l.length := by
      simpa [pref] using hpref_toList
    calc
      pref[i]! = pref.toList[i]! := by simpa using (array_get!_eq_list_get! pref i)
      _ = ((List.scanl (fun q x => q * x) 1 l).take l.length)[i]! := by simpa [this]

  have hi' : i < l.length := by
    simpa [hlen] using hi

  have hscanl_take : ((List.scanl (fun q x => q * x) 1 l).take l.length)[i]! =
      (List.scanl (fun q x => q * x) 1 l)[i]! := by
    simpa using (list_get!_take (xs := List.scanl (fun q x => q * x) 1 l) (n := l.length) (k := i) hi')

  have scanl_get_succ (l : List Int) (b : Int) (k : Nat) (hk : k < l.length) :
      (List.scanl (fun q x => q * x) b l)[k.succ]! =
        (List.scanl (fun q x => q * x) b l)[k]! * l[k]! := by
    -- Induction on l.
    induction l generalizing b k with
    | nil =>
        cases Nat.not_lt_zero _ hk
    | cons a l ih =>
        cases k with
        | zero =>
            simp [List.scanl_cons]
        | succ k =>
            have hk' : k < l.length := by
              simpa using (Nat.lt_of_succ_lt_succ hk)
            -- unfold `scanl` and use IH
            -- unfolding `get!` to `get?` helps simp reduce indices.
            simpa [List.scanl_cons, List.getElem!_eq_getElem?_getD] using (ih (b := b * a) (k := k) hk')

  have scanl_get_eq_prod_range :
      ∀ (l : List Int) (b : Int) (k : Nat), k ≤ l.length →
        (List.scanl (fun q x => q * x) b l)[k]! =
          b * (Finset.range k).prod (fun j => l[j]!) := by
    intro l b k hk
    induction k generalizing l b with
    | zero =>
        simp
    | succ k ih =>
        have hklt : k < l.length := Nat.lt_of_succ_le hk
        have hk' : k ≤ l.length := Nat.le_of_succ_le hk
        have ih' : (List.scanl (fun q x => q * x) b l)[k]! = b * (Finset.range k).prod (fun j => l[j]!) :=
          ih (l := l) (b := b) hk'
        calc
          (List.scanl (fun q x => q * x) b l)[k.succ]! =
              (List.scanl (fun q x => q * x) b l)[k]! * l[k]! :=
                scanl_get_succ l b k hklt
          _ = (b * (Finset.range k).prod (fun j => l[j]!)) * l[k]! := by
                simpa [ih']
          _ = b * ((Finset.range k).prod (fun j => l[j]!) * l[k]!) := by
                simp [mul_assoc]
          _ = b * (Finset.range k.succ).prod (fun j => l[j]!) := by
                simpa [Finset.prod_range_succ, mul_assoc]

  have hscanl_prod : (List.scanl (fun q x => q * x) 1 l)[i]! =
      (Finset.range i).prod (fun j => l[j]!) := by
    have hi_le : i ≤ l.length := Nat.le_of_lt hi'
    simpa using (scanl_get_eq_prod_range (l := l) (b := 1) (k := i) hi_le)

  have hget_nums_list : ∀ j : Nat, nums[j]! = l[j]! := by
    intro j
    have hta : l.toArray = nums := by
      simpa [l] using (Array.toArray_toList (xs := nums)).symm
    have hj : (l.toArray)[j]! = nums[j]! := congrArg (fun a : Array Int => a[j]!) hta
    simpa [List.getElem!_toArray] using hj.symm

  have hprod : (Finset.range i).prod (fun j => l[j]!) = prefixProd nums i := by
    unfold prefixProd
    refine Finset.prod_congr rfl ?_
    intro j hj
    simpa [hget_nums_list j]

  calc
    (nums.foldl step (1, (#[] : Array Int))).2[i]! = pref[i]! := by simp [pref]
    _ = ((List.scanl (fun q x => q * x) 1 l).take l.length)[i]! := hpref_get
    _ = (List.scanl (fun q x => q * x) 1 l)[i]! := hscanl_take
    _ = (Finset.range i).prod (fun j => l[j]!) := hscanl_prod
    _ = prefixProd nums i := hprod

theorem correctness_goal_1
    (nums : Array ℤ)
    (i : ℕ)
    (hi : i < nums.size)
    : (Array.foldr
        (fun x acc =>
          let s := acc.1;
          let arr := acc.2;
          (x * s, arr.push s))
        (1, #[]) nums).2[nums.size - 1 - i]! =
  suffixProd nums (i + 1) := by
  classical

  -- folding functions
  let fr : ℤ → (ℤ × Array ℤ) → (ℤ × Array ℤ) :=
    fun x acc =>
      let s := acc.1
      let arr := acc.2
      (x * s, arr.push s)
  let fl : (ℤ × Array ℤ) → ℤ → (ℤ × Array ℤ) :=
    fun acc x =>
      let p := acc.1
      let arr := acc.2
      (p * x, arr.push p)

  -- `fr`-based foldl is the same as `fl`, by commutativity
  have hfl : (fun acc x => fr x acc) = fl := by
    funext acc x
    cases acc with
    | mk s arr =>
      simp [fr, fl, mul_comm]

  -- foldr-to-foldl(reverse)
  have hfold : nums.foldr fr (1, (#[] : Array ℤ)) =
      nums.reverse.foldl (fun acc x => fr x acc) (1, (#[] : Array ℤ)) := by
    simpa using (Array.foldr_eq_foldl_reverse (xs := nums) (f := fr) (b := (1, (#[] : Array ℤ))))

  -- index is valid for the fold-produced array
  have hklt : nums.size - 1 - i < nums.reverse.size := by
    have : nums.size - 1 - i < nums.size := by
      simpa using Nat.sub_one_sub_lt_of_lt hi
    simpa [Array.size_reverse] using this

  -- prefix lemma on `nums.reverse`
  have hpref_rev :
      (nums.reverse.foldl fl (1, (#[] : Array ℤ))).2[nums.size - 1 - i]! =
        prefixProd nums.reverse (nums.size - 1 - i) := by
    simpa using correctness_goal_0 (nums := nums.reverse) (i := (nums.size - 1 - i)) hklt

  -- prefix product of reverse = suffix product of original
  have hprod :
      prefixProd nums.reverse (nums.size - 1 - i) = suffixProd nums (i + 1) := by
    set n : Nat := nums.size
    have hk : n - 1 - i = n - (i + 1) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (Nat.sub_sub n 1 i)
    set k : Nat := n - (i + 1)
    have hk' : n - 1 - i = k := by simpa [k] using hk
    have hk_le : k ≤ n := Nat.sub_le _ _
    have hn_eq : k + (i + 1) = n := by
      have : n - (i + 1) + (i + 1) = n := Nat.sub_add_cancel (Nat.succ_le_of_lt (by simpa [n] using hi))
      simpa [k, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this

    -- reverse access at the level of `getElem!`
    have hrev_get : ∀ j, j < n → nums.reverse[j]! = nums[n - 1 - j]! := by
      intro j hj
      simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
        Array.getElem?_reverse (xs := nums) (i := j) (by simpa [n] using hj), n]

    have h1 : prefixProd nums.reverse k = (Finset.range k).prod (fun j => nums[n - 1 - j]!) := by
      unfold prefixProd
      refine Finset.prod_congr rfl ?_
      intro j hj
      have hjk : j < k := Finset.mem_range.mp hj
      have hjn : j < n := lt_of_lt_of_le hjk hk_le
      simpa [hrev_get j hjn]

    have h2 : (Finset.range k).prod (fun j => nums[n - 1 - j]!) =
        (Finset.range k).prod (fun j => nums[(i + 1) + (k - 1 - j)]!) := by
      refine Finset.prod_congr rfl ?_
      intro j hj
      have hjk : j < k := Finset.mem_range.mp hj
      have hidx : n - 1 - j = (i + 1) + (k - 1 - j) := by
        omega
      exact congrArg (fun t => nums[t]!) hidx

    have h3 : (Finset.range k).prod (fun j => nums[(i + 1) + (k - 1 - j)]!) =
        (Finset.range k).prod (fun j => nums[(i + 1) + j]!) := by
      simpa using (Finset.prod_range_reflect (fun t => nums[(i + 1) + t]!) k)

    calc
      prefixProd nums.reverse (n - 1 - i)
          = prefixProd nums.reverse k := by simpa [hk', n]
      _ = (Finset.range k).prod (fun j => nums[n - 1 - j]!) := h1
      _ = (Finset.range k).prod (fun j => nums[(i + 1) + (k - 1 - j)]!) := h2
      _ = (Finset.range k).prod (fun j => nums[(i + 1) + j]!) := h3
      _ = suffixProd nums (i + 1) := by
        simp [suffixProd, n, k]

  -- combine all rewrites
  have hfold_idx :
      (nums.foldr fr (1, (#[] : Array ℤ))).2[nums.size - 1 - i]! =
        (nums.reverse.foldl (fun acc x => fr x acc) (1, (#[] : Array ℤ))).2[nums.size - 1 - i]! :=
    congrArg (fun p => p.2[nums.size - 1 - i]!) hfold

  calc
    (Array.foldr fr (1, (#[] : Array ℤ)) nums).2[nums.size - 1 - i]!
        = (nums.foldr fr (1, (#[] : Array ℤ))).2[nums.size - 1 - i]! := rfl
    _ = (nums.reverse.foldl (fun acc x => fr x acc) (1, (#[] : Array ℤ))).2[nums.size - 1 - i]! :=
          hfold_idx
    _ = (nums.reverse.foldl fl (1, (#[] : Array ℤ))).2[nums.size - 1 - i]! := by
          simp [hfl]
    _ = prefixProd nums.reverse (nums.size - 1 - i) := hpref_rev
    _ = suffixProd nums (i + 1) := hprod

theorem correctness_goal_2
    (nums : Array ℤ)
    (i : ℕ)
    (hi : i < nums.size)
    : prodExcept nums i = prefixProd nums i * suffixProd nums (i + 1) := by
  classical
  -- The precondition and fold-related hypotheses are not needed for this arithmetic identity.
  set n : Nat := nums.size with hn
  let g : Nat → Int := fun j => if j = i then 1 else nums[j]!

  have hle : i + 1 ≤ n := by
    have : i < n := by simpa [hn] using hi
    exact Nat.succ_le_of_lt this

  have hn' : n = (i + 1) + (n - (i + 1)) := by
    exact (Nat.add_sub_of_le hle).symm

  have hleft0 : (∏ j ∈ Finset.range i, g j) = (∏ j ∈ Finset.range i, nums[j]!) := by
    refine Finset.prod_congr rfl ?_
    intro j hj
    have hjlt : j < i := Finset.mem_range.mp hj
    have hjne : j ≠ i := Nat.ne_of_lt hjlt
    simp [g, hjne]

  have hleft : (∏ j ∈ Finset.range (i + 1), g j) = prefixProd nums i := by
    calc
      (∏ j ∈ Finset.range (i + 1), g j)
          = (∏ j ∈ Finset.range i, g j) * g i := by
              simpa using (Finset.prod_range_succ (f := g) i)
      _ = (∏ j ∈ Finset.range i, nums[j]!) * 1 := by
              simp [hleft0, g]
      _ = prefixProd nums i := by
              simp [prefixProd]

  have hright0 :
      (∏ t ∈ Finset.range (n - (i + 1)), g ((i + 1) + t))
        = (∏ t ∈ Finset.range (n - (i + 1)), nums[(i + 1) + t]!) := by
    refine Finset.prod_congr rfl ?_
    intro t ht
    have hne : (i + 1) + t ≠ i := by
      have hlt : i < (i + 1) + t := by
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self i) (Nat.le_add_right (i + 1) t)
      exact (Nat.ne_of_lt hlt).symm
    simp [g, hne]

  have hright : (∏ t ∈ Finset.range (n - (i + 1)), g ((i + 1) + t)) = suffixProd nums (i + 1) := by
    simpa [suffixProd] using hright0

  have hsplit : (∏ j ∈ Finset.range n, g j) =
      (∏ j ∈ Finset.range (i + 1), g j) * (∏ t ∈ Finset.range (n - (i + 1)), g ((i + 1) + t)) := by
    -- Rewrite `n` as `(i+1) + (n-(i+1))` and apply `Finset.prod_range_add`.
    have hcongr : (∏ j ∈ Finset.range n, g j) = (∏ j ∈ Finset.range ((i + 1) + (n - (i + 1))), g j) := by
      exact congrArg (fun N => (∏ j ∈ Finset.range N, g j)) hn'
    -- Now use `prod_range_add` on the right-hand side.
    calc
      (∏ j ∈ Finset.range n, g j)
          = (∏ j ∈ Finset.range ((i + 1) + (n - (i + 1))), g j) := hcongr
      _ = (∏ j ∈ Finset.range (i + 1), g j) * (∏ t ∈ Finset.range (n - (i + 1)), g ((i + 1) + t)) := by
            simpa using
              (Finset.prod_range_add (f := g) (n := i + 1) (m := n - (i + 1)))

  calc
    prodExcept nums i
        = (∏ j ∈ Finset.range n, g j) := by
            simp [prodExcept, g, n, hn]
    _ = (∏ j ∈ Finset.range (i + 1), g j) * (∏ t ∈ Finset.range (n - (i + 1)), g ((i + 1) + t)) := by
            simpa using hsplit
    _ = prefixProd nums i * suffixProd nums (i + 1) := by
            rw [hleft, hright]

theorem correctness_goal
    (nums : Array Int)
    : postcondition nums (implementation nums) := by
  unfold postcondition
  constructor
  · unfold implementation
    simp [Array.size_ofFn]
  · intro i hi
    have h_pref :
        ((nums.foldl
            (fun (acc : Int × Array Int) (x : Int) =>
              let p := acc.1
              let arr := acc.2
              (p * x, arr.push p))
            ((1 : Int), (#[] : Array Int))).2)[i]! = prefixProd nums i := by
      expose_names; exact (correctness_goal_0 nums i hi)
    have h_suff :
        ((nums.foldr
            (fun (x : Int) (acc : Int × Array Int) =>
              let s := acc.1
              let arr := acc.2
              (x * s, arr.push s))
            ((1 : Int), (#[] : Array Int))).2)[(nums.size - 1 - i)]! =
          suffixProd nums (i+1) := by
      expose_names; exact (correctness_goal_1 nums i hi)
    have h_prod : prodExcept nums i = prefixProd nums i * suffixProd nums (i+1) := by
      expose_names; exact (correctness_goal_2 nums i hi)

    have h_get : (implementation nums)[i]! =
        ((nums.foldl
            (fun (acc : Int × Array Int) (x : Int) =>
              let p := acc.1
              let arr := acc.2
              (p * x, arr.push p))
            ((1 : Int), (#[] : Array Int))).2)[i]! *
        ((nums.foldr
            (fun (x : Int) (acc : Int × Array Int) =>
              let s := acc.1
              let arr := acc.2
              (x * s, arr.push s))
            ((1 : Int), (#[] : Array Int))).2)[(nums.size - 1 - i)]! := by
      unfold implementation
      simp [Array.get!_eq_getD_getElem?, Array.getElem?_ofFn, hi, Array.size_ofFn]

    calc
      (implementation nums)[i]! = prefixProd nums i * suffixProd nums (i+1) := by
        -- expand to pref*suff, then rewrite each part
        simpa [h_get, h_pref, h_suff]
      _ = prodExcept nums i := by
        simpa [h_prod] using h_prod.symm
end Proof
