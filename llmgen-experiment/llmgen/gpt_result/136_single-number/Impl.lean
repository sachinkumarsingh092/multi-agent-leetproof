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
set_option linter.unnecessarySimpa false

/- Problem Description
    SingleNumber: in a non-empty array of integers, every element appears exactly twice except for one element that appears once; return that single element.
    **Important: complexity should be O(n) time and O(1) space**
    Natural language breakdown:
    1. The input is an array `nums` of integers and it is non-empty.
    2. There exists an integer `s` that occurs in `nums` exactly once.
    3. Every other integer occurring in `nums` occurs in `nums` exactly twice.
    4. The output must be the unique integer that occurs exactly once.
-/

section Specs
-- Helper predicate: an element occurs exactly once in an array.
def occursOnce (nums : Array Int) (x : Int) : Prop :=
  nums.count x = 1

-- Helper predicate: an element occurs exactly twice in an array.
def occursTwice (nums : Array Int) (x : Int) : Prop :=
  nums.count x = 2

-- Precondition: the array is non-empty and has exactly one element with count 1,
-- and all other elements appearing in the array have count 2.
def precondition (nums : Array Int) : Prop :=
  nums.size > 0 ∧
  (∃ s : Int,
    s ∈ nums ∧
    occursOnce nums s ∧
    (∀ y : Int, y ∈ nums → y ≠ s → occursTwice nums y))

-- Postcondition: result is the unique element that occurs once.
def postcondition (nums : Array Int) (result : Int) : Prop :=
  result ∈ nums ∧
  occursOnce nums result ∧
  (∀ y : Int, y ∈ nums → occursOnce nums y → y = result)
end Specs

section Impl
method SingleNumber (nums : Array Int)
  return (result : Int)
  require precondition nums
  ensures postcondition nums result
  do
  -- O(n) / O(1) solution:
  -- Encode each `Int` into a `Nat` using a bijection Int ↔ Nat, then XOR all codes.
  -- Pairs cancel out under XOR, leaving the code of the unique element; decode it back.
  let mut i : Nat := 0
  let mut acc : Nat := 0

  while i < nums.size
    -- i is an index into nums; needed for safe access nums[i]!
    invariant "inv_i_le_size" i ≤ nums.size
    -- Convenient normalization: since i ≤ nums.size, min i nums.size = i.
    invariant "inv_min" min i nums.size = i
    -- acc tracks the XOR-fold of the encoding over the first i elements.
    -- We state it using `extract 0 i` to match the VC shape that appears at loop exit.
    invariant "inv_acc_extract"
      acc = Array.foldl (fun (a : Nat) (z : Int) =>
        Nat.xor a (if 0 ≤ z then
          2 * (Int.toNat z)
        else
          2 * (Int.toNat ((-z) - 1)) + 1)) 0 (nums.extract 0 i) 0 (min i nums.size)
    done_with i = nums.size
    decreasing nums.size - i
  do
    let z : Int := nums[i]!

    -- Encode `z : Int` into `Nat`:
    --   encode(n)       = 2*n            for n ≥ 0
    --   encode(-n-1)    = 2*n + 1
    let code : Nat :=
      if 0 ≤ z then
        2 * (Int.toNat z)
      else
        2 * (Int.toNat ((-z) - 1)) + 1

    acc := Nat.xor acc code
    i := i + 1

  -- Decode `acc : Nat` back into `Int`.
  let res : Int :=
    if acc % 2 = 0 then
      Int.ofNat (acc / 2)
    else
      Int.negSucc (acc / 2)

  return res
end Impl

section TestCases
-- Test case 1: Example 1
-- Input: nums = [2,2,1]
-- Output: 1

def test1_nums : Array Int := #[ (2 : Int), (2 : Int), (1 : Int) ]
def test1_Expected : Int := (1 : Int)

-- Test case 2: Example 2

def test2_nums : Array Int := #[ (4 : Int), (1 : Int), (2 : Int), (1 : Int), (2 : Int) ]
def test2_Expected : Int := (4 : Int)

-- Test case 3: Example 3 (singleton array)

def test3_nums : Array Int := #[ (1 : Int) ]
def test3_Expected : Int := (1 : Int)

-- Test case 4: includes 0 (edge value) with unique 1

def test4_nums : Array Int := #[ (0 : Int), (1 : Int), (0 : Int) ]
def test4_Expected : Int := (1 : Int)

-- Test case 5: includes negative number as the unique element

def test5_nums : Array Int := #[ (-1 : Int), (2 : Int), (2 : Int) ]
def test5_Expected : Int := (-1 : Int)

-- Test case 6: unique element in the middle, multiple pairs

def test6_nums : Array Int := #[ (5 : Int), (5 : Int), (6 : Int), (7 : Int), (7 : Int) ]
def test6_Expected : Int := (6 : Int)

-- Test case 7: larger odd length, unique element at end

def test7_nums : Array Int := #[ (1 : Int), (1 : Int), (2 : Int), (2 : Int), (3 : Int), (3 : Int), (4 : Int) ]
def test7_Expected : Int := (4 : Int)

-- Test case 8: unique element at start

def test8_nums : Array Int := #[ (9 : Int), (8 : Int), (8 : Int), (7 : Int), (7 : Int) ]
def test8_Expected : Int := (9 : Int)

-- Test case 9: singleton array containing 0

def test9_nums : Array Int := #[ (0 : Int) ]
def test9_Expected : Int := (0 : Int)
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((SingleNumber test1_nums).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((SingleNumber test2_nums).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((SingleNumber test3_nums).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((SingleNumber test4_nums).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((SingleNumber test5_nums).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((SingleNumber test6_nums).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((SingleNumber test7_nums).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((SingleNumber test8_nums).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((SingleNumber test9_nums).run), DivM.res test9_Expected ]
end Assertions

section Pbt
velvet_plausible_test SingleNumber (config := { maxMs := some 20000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000

theorem goal_0
    (nums : Array ℤ)
    (i : ℕ)
    (invariant_inv_i_le_size : i ≤ nums.size)
    (if_pos : i < nums.size)
    : (Array.foldl (fun (a : ℕ) (z : ℤ) => a.xor (if OfNat.ofNat 0 ≤ z then OfNat.ofNat 2 * z.toNat else OfNat.ofNat 2 * ((-z).toNat - OfNat.ofNat 1) + OfNat.ofNat 1)) (OfNat.ofNat 0) (nums.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0) (min i nums.size)).xor (if OfNat.ofNat 0 ≤ nums[i]! then OfNat.ofNat 2 * nums[i]!.toNat else OfNat.ofNat 2 * ((-nums[i]!).toNat - OfNat.ofNat 1) + OfNat.ofNat 1) = Array.foldl (fun (a : ℕ) (z : ℤ) => a.xor (if OfNat.ofNat 0 ≤ z then OfNat.ofNat 2 * z.toNat else OfNat.ofNat 2 * ((-z).toNat - OfNat.ofNat 1) + OfNat.ofNat 1)) (OfNat.ofNat 0) (nums.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) (OfNat.ofNat 0) (min (i + OfNat.ofNat 1) nums.size) := by
  classical

  let enc : ℤ → ℕ := fun z =>
    if (0 : ℤ) ≤ z then
      2 * z.toNat
    else
      2 * ((-z).toNat - 1) + 1

  have hmin_i : min i nums.size = i := by
    simpa using (Nat.min_eq_left invariant_inv_i_le_size)
  have hmin_succ : min (i + 1) nums.size = i + 1 := by
    apply Nat.min_eq_left
    exact Nat.succ_le_of_lt if_pos

  -- simplify mins and the fold function
  simp [enc, hmin_i, hmin_succ]

  -- rewrite the bang-get using the in-bounds proof
  have hget : nums[i]! = nums[i]'if_pos := by
    simpa using (getElem!_pos (c := nums) (i := i) (h := if_pos))
  simp [enc, hget]

  -- rewrite the RHS extract as a push
  have hextract : nums.extract 0 (i + 1) = (nums.extract 0 i).push (nums[i]'if_pos) := by
    simpa using (show (nums.extract 0 i).push (nums[i]'if_pos) = nums.extract 0 (i + 1) from
      (@Array.push_extract_getElem ℤ nums 0 i if_pos)).symm
  rw [hextract]

  -- push is append of singleton
  have hpush : (nums.extract 0 i).push (nums[i]'if_pos) = (nums.extract 0 i) ++ #[nums[i]'if_pos] := by
    simp
  rw [hpush]

  -- size of the extracted prefix
  have hsize_extract' : (nums.extract 0 i).size = min i nums.size := by
    simp
  have hsize_extract : (nums.extract 0 i).size = i := by
    simpa [hmin_i] using hsize_extract'

  have hstop : i + 1 = (nums.extract 0 i).size + (#[nums[i]'if_pos]).size := by
    simp [hsize_extract]

  -- fold over append
  have happ :=
    (Array.foldl_append' (f := fun (a : ℕ) (z : ℤ) => a.xor (enc z)) (b := (0 : ℕ))
      (xs := nums.extract 0 i) (ys := #[nums[i]'if_pos]) (stop := i + 1) hstop)

  -- simplify the singleton fold and discharge
  simpa [enc, hsize_extract] using happ.symm

theorem decode_encode_trial (z : Int) :
    (if
        (if (0 : Int) ≤ z then (2 : Nat) * z.toNat
        else (2 : Nat) * ((-z).toNat - (1 : Nat)) + (1 : Nat)) % (2 : Nat) =
          (0 : Nat)
      then
        ((if (0 : Int) ≤ z then (2 : Nat) * z.toNat
          else (2 : Nat) * ((-z).toNat - (1 : Nat)) + (1 : Nat))).cast / (2 : Int)
      else
        Int.negSucc
          ((if (0 : Int) ≤ z then (2 : Nat) * z.toNat
            else (2 : Nat) * ((-z).toNat - (1 : Nat)) + (1 : Nat)) / (2 : Nat))) =
      z := by
  cases z with
  | ofNat n =>
    simp
  | negSucc n =>
    have hdiv : (2 * n + 1) / 2 = n := by
      omega
    simp [hdiv]


theorem goal_1_0
    (nums : Array ℤ)
    (invariant_inv_i_le_size : True)
    (invariant_inv_min : True)
    (hsize : OfNat.ofNat 0 < nums.size)
    (s : ℤ)
    (hs_mem : s ∈ nums)
    (hs_count : Array.count s nums = OfNat.ofNat 1)
    (htwice : ∀ y ∈ nums, ¬y = s → Array.count y nums = OfNat.ofNat 2)
    : Array.foldl (fun a z => a.xor (if 0 ≤ z then 2 * z.toNat else 2 * ((-z).toNat - 1) + 1)) 0 nums =
  if 0 ≤ s then 2 * s.toNat else 2 * ((-s).toNat - 1) + 1 := by
  classical
  clear invariant_inv_i_le_size invariant_inv_min hsize hs_mem

  let encode : ℤ → Nat := fun z => if 0 ≤ z then 2 * z.toNat else 2 * ((-z).toNat - 1) + 1
  let f : Nat → ℤ → Nat := fun acc z => acc ^^^ (encode z)

  -- Right-commutativity needed for permutation invariance of foldl.
  have rcomm_f : RightCommutative f := by
    refine ⟨?_⟩
    intro x y z
    unfold f
    calc
      (x ^^^ encode y) ^^^ encode z = x ^^^ (encode y ^^^ encode z) := by
        simp [Nat.xor_assoc]
      _ = x ^^^ (encode z ^^^ encode y) := by
        simp [Nat.xor_comm]
      _ = (x ^^^ encode z) ^^^ encode y := by
        simp [Nat.xor_assoc]
  letI : RightCommutative f := rcomm_f

  -- foldl with XOR can be split as `init xor (foldl from 0)`
  have foldl_xor_init : ∀ (l : List ℤ) (init : Nat), l.foldl f init = init ^^^ (l.foldl f 0) := by
    intro l init
    induction l generalizing init with
    | nil =>
      simp [f]
    | cons x xs ih =>
      have h_init : xs.foldl f (init ^^^ encode x) = (init ^^^ encode x) ^^^ xs.foldl f 0 := by
        simpa [f] using (ih (init := init ^^^ encode x))
      have h_enc : xs.foldl f (encode x) = (encode x) ^^^ xs.foldl f 0 := by
        simpa [f] using (ih (init := encode x))
      calc
        List.foldl f init (x :: xs)
            = List.foldl f (init ^^^ encode x) xs := by
                simp [List.foldl, f]
        _   = (init ^^^ encode x) ^^^ (List.foldl f 0 xs) := h_init
        _   = init ^^^ (encode x ^^^ (List.foldl f 0 xs)) := by
                simp [Nat.xor_assoc]
        _   = init ^^^ (List.foldl f (encode x) xs) := by
                simpa [h_enc, Nat.xor_assoc]
        _   = init ^^^ (List.foldl f 0 (x :: xs)) := by
                simp [List.foldl, f, Nat.zero_xor]

  -- erasing a present element strictly decreases length
  have length_erase_lt_of_mem : ∀ {a : ℤ} {l : List ℤ}, a ∈ l → (l.erase a).length < l.length := by
    intro a l ha
    induction l with
    | nil => simpa using ha
    | cons b tl ih =>
      simp at ha
      cases ha with
      | inl hba =>
        subst hba
        simp
      | inr hmem =>
        by_cases hba : b = a
        · subst hba
          simp
        ·
          have : (tl.erase a).length < tl.length := ih hmem
          simpa [List.erase_cons, hba] using Nat.succ_lt_succ this

  -- If every element appears exactly twice, XOR-fold is 0.
  have foldl_allTwice_len : ∀ n : Nat,
      (∀ l : List ℤ, l.length = n → (∀ y, y ∈ l → l.count y = 2) → l.foldl f 0 = 0) := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih l hlen hall
    cases l with
    | nil =>
      simp
    | cons x xs =>
      have hx_count : (x :: xs).count x = 2 := hall x (by simp)
      have hxs_count : xs.count x = 1 := by
        have : xs.count x + 1 = 2 := by
          simpa [List.count_cons] using hx_count
        omega
      have hx_mem : x ∈ xs := by
        by_contra hn
        have : xs.count x = 0 := (List.count_eq_zero).2 hn
        simpa [hxs_count] using this

      let rest : List ℤ := xs.erase x

      have p1 : List.Perm xs (x :: rest) := by
        simpa [rest] using (List.perm_cons_erase hx_mem)
      have p : List.Perm (x :: xs) (x :: x :: rest) := List.Perm.cons x p1

      have hperm : (x :: xs).foldl f 0 = (x :: x :: rest).foldl f 0 := by
        simpa using (List.Perm.foldl_eq (f := f) p 0)

      have hx_cancel : (0 ^^^ encode x) ^^^ encode x = 0 := by
        simp [Nat.zero_xor, Nat.xor_self]

      have hcancel : (x :: x :: rest).foldl f 0 = rest.foldl f 0 := by
        simp [List.foldl, f, hx_cancel]

      have hall_rest : ∀ y, y ∈ rest → rest.count y = 2 := by
        intro y hy
        have hy_xs : y ∈ xs := List.mem_of_mem_erase (by simpa [rest] using hy)
        have hy_ne_x : y ≠ x := by
          intro hyx
          subst y
          have hcount0 : rest.count x = 0 := by
            simpa [rest, hxs_count] using (List.count_erase_self (a := x) (l := xs))
          have hnot : x ∉ rest := (List.count_eq_zero).1 hcount0
          exact hnot (by simpa using hy)
        have hy_ne_x' : x ≠ y := by
          intro hxy; exact hy_ne_x hxy.symm
        have hy_count_l : (x :: xs).count y = 2 := hall y (by simp [hy_xs])
        have hy_count_xs : xs.count y = 2 := by
          simpa [List.count_cons, hy_ne_x'] using hy_count_l
        simpa [rest, List.count_erase_of_ne hy_ne_x] using hy_count_xs

      have hlen_rest : rest.length < n := by
        have hxsn : xs.length.succ = n := by
          simpa using (show (x :: xs).length = n from hlen)
        have hxsn' : xs.length + 1 = n := by
          simpa [Nat.succ_eq_add_one] using hxsn
        have : rest.length < xs.length + 1 := by
          have : rest.length < xs.length := by
            simpa [rest] using (length_erase_lt_of_mem (a := x) (l := xs) hx_mem)
          exact Nat.lt_trans this (Nat.lt_succ_self xs.length)
        simpa [hxsn'] using this

      have ih_rest : rest.foldl f 0 = 0 := by
        have := ih rest.length hlen_rest rest rfl hall_rest
        simpa using this

      calc
        (x :: xs).foldl f 0 = (x :: x :: rest).foldl f 0 := hperm
        _ = rest.foldl f 0 := hcancel
        _ = 0 := ih_rest

  have foldl_allTwice : ∀ l : List ℤ, (∀ y, y ∈ l → l.count y = 2) → l.foldl f 0 = 0 := by
    intro l hall
    exact foldl_allTwice_len l.length l rfl hall

  -- Main lemma: if exactly one element is unique and the rest appear twice, XOR-fold is its encoding.
  have foldl_unique_len : ∀ n : Nat,
      (∀ l : List ℤ, l.length = n → l.count s = 1 →
        (∀ y, y ∈ l → y ≠ s → l.count y = 2) → l.foldl f 0 = encode s) := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih l hlen hs htw
    cases l with
    | nil =>
      simp at hs
    | cons x xs =>
      by_cases hx : x = s
      · subst s
        have hs_tail0 : xs.count x = 0 := by
          have : xs.count x + 1 = 1 := by
            simpa [List.count_cons] using hs
          omega
        have hall_tail : ∀ y, y ∈ xs → xs.count y = 2 := by
          intro y hy
          have hy_ne_x : y ≠ x := by
            intro hyx
            subst y
            have hnot : x ∉ xs := (List.count_eq_zero).1 hs_tail0
            exact hnot hy
          have hy_count : (x :: xs).count y = 2 := htw y (by simp [hy]) hy_ne_x
          have hy_ne_x' : x ≠ y := by
            intro hxy; exact hy_ne_x hxy.symm
          simpa [List.count_cons, hy_ne_x'] using hy_count
        have htail0 : xs.foldl f 0 = 0 := foldl_allTwice xs hall_tail
        have hfold_enc : xs.foldl f (encode x) = encode x := by
          have := foldl_xor_init xs (encode x)
          simpa [htail0, Nat.xor_zero] using this
        simpa [List.foldl, f, Nat.zero_xor] using hfold_enc
      ·
        have hx_count : (x :: xs).count x = 2 := htw x (by simp) (by simpa [hx])
        have hxs_count : xs.count x = 1 := by
          have : xs.count x + 1 = 2 := by
            simpa [List.count_cons] using hx_count
          omega
        have hx_mem : x ∈ xs := by
          by_contra hn
          have : xs.count x = 0 := (List.count_eq_zero).2 hn
          simpa [hxs_count] using this

        let rest : List ℤ := xs.erase x

        have p1 : List.Perm xs (x :: rest) := by
          simpa [rest] using (List.perm_cons_erase hx_mem)
        have p : List.Perm (x :: xs) (x :: x :: rest) := List.Perm.cons x p1

        have hperm : (x :: xs).foldl f 0 = (x :: x :: rest).foldl f 0 := by
          simpa using (List.Perm.foldl_eq (f := f) p 0)

        have hx_cancel : (0 ^^^ encode x) ^^^ encode x = 0 := by
          simp [Nat.zero_xor, Nat.xor_self]

        have hcancel : (x :: x :: rest).foldl f 0 = rest.foldl f 0 := by
          simp [List.foldl, f, hx_cancel]

        have hs_rest : rest.count s = 1 := by
          have hs_xs : xs.count s = 1 := by
            simpa [List.count_cons, hx] using hs
          have hs_ne_x : s ≠ x := by
            intro h; exact hx h.symm
          have : rest.count s = xs.count s := by
            simpa [rest] using (List.count_erase_of_ne (a := s) (b := x) hs_ne_x (l := xs))
          simpa [this, hs_xs]

        have htw_rest : ∀ y, y ∈ rest → y ≠ s → rest.count y = 2 := by
          intro y hy hy_ne_s
          have hy_xs : y ∈ xs := List.mem_of_mem_erase (by simpa [rest] using hy)
          have hy_ne_x : y ≠ x := by
            intro hyx
            subst y
            have hcount0 : rest.count x = 0 := by
              simpa [rest, hxs_count] using (List.count_erase_self (a := x) (l := xs))
            have hnot : x ∉ rest := (List.count_eq_zero).1 hcount0
            exact hnot (by simpa using hy)
          have hy_ne_x' : x ≠ y := by
            intro hxy; exact hy_ne_x hxy.symm
          have hy_count_l : (x :: xs).count y = 2 := htw y (by simp [hy_xs]) hy_ne_s
          have hy_count_xs : xs.count y = 2 := by
            simpa [List.count_cons, hy_ne_x'] using hy_count_l
          simpa [rest, List.count_erase_of_ne hy_ne_x] using hy_count_xs

        have hlen_rest : rest.length < n := by
          have hxsn : xs.length.succ = n := by
            simpa using (show (x :: xs).length = n from hlen)
          have hxsn' : xs.length + 1 = n := by
            simpa [Nat.succ_eq_add_one] using hxsn
          have : rest.length < xs.length + 1 := by
            have : rest.length < xs.length := by
              simpa [rest] using (length_erase_lt_of_mem (a := x) (l := xs) hx_mem)
            exact Nat.lt_trans this (Nat.lt_succ_self xs.length)
          simpa [hxsn'] using this

        have ih_rest : rest.foldl f 0 = encode s := by
          have := ih rest.length hlen_rest rest rfl hs_rest htw_rest
          simpa using this

        calc
          (x :: xs).foldl f 0 = (x :: x :: rest).foldl f 0 := hperm
          _ = rest.foldl f 0 := hcancel
          _ = encode s := ih_rest

  have foldl_unique : ∀ l : List ℤ, l.count s = 1 →
        (∀ y, y ∈ l → y ≠ s → l.count y = 2) → l.foldl f 0 = encode s := by
    intro l hs htw
    exact foldl_unique_len l.length l rfl hs htw

  -- Transfer assumptions to `List`.
  have hs_countL : nums.toList.count s = 1 := by
    simpa [Array.count_toList] using hs_count

  have htwiceL : ∀ y, y ∈ nums.toList → y ≠ s → nums.toList.count y = 2 := by
    intro y hy hy_ne
    have hyA : y ∈ nums := (Array.mem_toList).1 hy
    have := htwice y hyA (by simpa using hy_ne)
    simpa [Array.count_toList] using this

  have hlist : nums.toList.foldl f 0 = encode s := foldl_unique nums.toList hs_countL htwiceL

  have htoList : nums.toList.foldl f 0 = nums.foldl f 0 :=
    Array.foldl_toList (f := f) (init := 0) (xs := nums)

  have harr : nums.foldl f 0 = encode s := by
    simpa [htoList] using hlist

  -- unfold `f` and `encode` back to the goal
  simpa [f, encode] using harr

theorem goal_1
    (nums : Array ℤ)
    (require_1 : OfNat.ofNat 0 < nums.size ∧ ∃ s ∈ nums, Array.count s nums = OfNat.ofNat 1 ∧ ∀ y ∈ nums, ¬y = s → Array.count y nums = OfNat.ofNat 2)
    (invariant_inv_i_le_size : True)
    (invariant_inv_min : True)
    : postcondition nums (if Array.foldl (fun (a : ℕ) (z : ℤ) => a.xor (if OfNat.ofNat 0 ≤ z then OfNat.ofNat 2 * z.toNat else OfNat.ofNat 2 * ((-z).toNat - OfNat.ofNat 1) + OfNat.ofNat 1)) (OfNat.ofNat 0) nums % OfNat.ofNat 2 = OfNat.ofNat 0 then (Array.foldl (fun (a : ℕ) (z : ℤ) => a.xor (if OfNat.ofNat 0 ≤ z then OfNat.ofNat 2 * z.toNat else OfNat.ofNat 2 * ((-z).toNat - OfNat.ofNat 1) + OfNat.ofNat 1)) (OfNat.ofNat 0) nums).cast / OfNat.ofNat 2 else Int.negSucc (Array.foldl (fun (a : ℕ) (z : ℤ) => a.xor (if OfNat.ofNat 0 ≤ z then OfNat.ofNat 2 * z.toNat else OfNat.ofNat 2 * ((-z).toNat - OfNat.ofNat 1) + OfNat.ofNat 1)) (OfNat.ofNat 0) nums / OfNat.ofNat 2)) := by
  classical
  rcases require_1 with ⟨hsize, ⟨s, hs_mem, hs_count, htwice⟩⟩

  -- The main XOR cancellation lemma: the fold yields the code of the unique element.
  have hacc :
      Array.foldl
          (fun (a : ℕ) (z : ℤ) =>
            Nat.xor a
              (if (0 : Int) ≤ z then (2 : Nat) * z.toNat
              else (2 : Nat) * ((-z).toNat - (1 : Nat)) + (1 : Nat)))
          (0 : Nat) nums =
        (if (0 : Int) ≤ s then (2 : Nat) * s.toNat
        else (2 : Nat) * ((-s).toNat - (1 : Nat)) + (1 : Nat)) := by
    expose_names; exact (goal_1_0 nums invariant_inv_i_le_size invariant_inv_min hsize s hs_mem hs_count htwice)

  have hres :
      (if Array.foldl (fun (a : ℕ) (z : ℤ) => a.xor (if OfNat.ofNat 0 ≤ z then OfNat.ofNat 2 * z.toNat else OfNat.ofNat 2 * ((-z).toNat - OfNat.ofNat 1) + OfNat.ofNat 1)) (OfNat.ofNat 0) nums % OfNat.ofNat 2 = OfNat.ofNat 0 then (Array.foldl (fun (a : ℕ) (z : ℤ) => a.xor (if OfNat.ofNat 0 ≤ z then OfNat.ofNat 2 * z.toNat else OfNat.ofNat 2 * ((-z).toNat - OfNat.ofNat 1) + OfNat.ofNat 1)) (OfNat.ofNat 0) nums).cast / OfNat.ofNat 2 else Int.negSucc (Array.foldl (fun (a : ℕ) (z : ℤ) => a.xor (if OfNat.ofNat 0 ≤ z then OfNat.ofNat 2 * z.toNat else OfNat.ofNat 2 * ((-z).toNat - OfNat.ofNat 1) + OfNat.ofNat 1)) (OfNat.ofNat 0) nums / OfNat.ofNat 2)) = s := by
    -- rewrite to the explicitly-typed encoding/decoding statement
    -- and finish using `decode_encode_trial s`.
    -- (This works because the result expression is exactly `decode (encode s)`.
    simpa [hacc] using (decode_encode_trial s)

  refine And.intro ?_ (And.intro ?_ ?_)
  · simpa [hres] using hs_mem
  · simpa [occursOnce, hres] using hs_count
  · intro y hy_mem hy_once
    have hy_count : Array.count y nums = 1 := by
      simpa [occursOnce] using hy_once
    have : y = s := by
      by_contra hne_s
      have hy_two : Array.count y nums = 2 := htwice y hy_mem hne_s
      have : (1 : Nat) = 2 := by simpa [hy_count] using hy_two.symm
      exact (by decide : (1 : Nat) ≠ 2) this
    simpa [hres, this]


prove_correct SingleNumber by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at *); try (conv => congr <;> simp) ; try expose_names)
  exact (goal_0 nums i invariant_inv_i_le_size if_pos)
  exact (goal_1 nums require_1 invariant_inv_i_le_size invariant_inv_min)
end Proof
