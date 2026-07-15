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
    2161. Partition Array According to Given Pivot: Rearrange an integer array into < pivot, = pivot, > pivot, stably.
    **Important: complexity should be O(n)** time and **O(n)** extra space.
    Natural language breakdown:
    1. We are given an input array `nums` of integers and an integer `pivot`.
    2. The output is an array `result` with the same length as `nums`.
    3. Every element of `result` that is less than `pivot` must appear before every element greater than `pivot`.
    4. Every element equal to `pivot` must appear between the less-than elements and the greater-than elements.
    5. The multiset of elements is preserved: `result` contains exactly the same elements with the same multiplicities as `nums`.
-/

section Specs
-- Helper functions for group sizes

def countLt (nums : Array Int) (pivot : Int) : Nat :=
  nums.countP (fun x => x < pivot)

def countEq (nums : Array Int) (pivot : Int) : Nat :=
  nums.countP (fun x => x = pivot)

def countGt (nums : Array Int) (pivot : Int) : Nat :=
  nums.countP (fun x => pivot < x)

-- Helper predicate: result is partitioned into three consecutive blocks: < pivot, = pivot, > pivot.
-- The block boundaries are defined by the counts in the input.

def isThreeBlockPartition (nums : Array Int) (pivot : Int) (result : Array Int) : Prop :=
  let cL : Nat := countLt nums pivot
  let cE : Nat := countEq nums pivot
  result.size = nums.size ∧
  (∀ (i : Nat), i < result.size →
      (i < cL → result[i]! < pivot) ∧
      ((cL ≤ i ∧ i < cL + cE) → result[i]! = pivot) ∧
      (cL + cE ≤ i → pivot < result[i]!))

-- Helper predicate: element multiplicities are preserved.
-- We express this via the `count` observation for every integer value.

def sameElementCounts (nums : Array Int) (result : Array Int) : Prop :=
  ∀ (x : Int), result.count x = nums.count x

def precondition (nums : Array Int) (pivot : Int) : Prop :=
  True

def postcondition (nums : Array Int) (pivot : Int) (result : Array Int) : Prop :=
  isThreeBlockPartition nums pivot result ∧
  sameElementCounts nums result
end Specs

section Impl
method PartitionArrayAccordingToPivot (nums : Array Int) (pivot : Int)
  return (result : Array Int)
  require precondition nums pivot
  ensures postcondition nums pivot result
  do
  let mut lt : Array Int := #[]
  let mut eq : Array Int := #[]
  let mut gt : Array Int := #[]

  let mut i : Nat := 0
  while i < nums.size
    -- i stays within bounds, so nums[i]! is safe.
    -- Init: i = 0. Preserved: loop increments i by 1 and guard enforces i < nums.size.
    invariant "inv_bounds" i ≤ nums.size
    -- Accounting invariant: every processed element ends up in exactly one bucket.
    -- Init: 0+0+0=0. Preserved: exactly one of lt/eq/gt is push'ed each iteration.
    invariant "inv_size" lt.size + eq.size + gt.size = i
    -- Classification invariants for each bucket.
    -- Init: vacuous since buckets empty. Preserved: only elements satisfying the test are pushed.
    invariant "inv_lt_all" (∀ k : Nat, k < lt.size → lt[k]! < pivot)
    invariant "inv_eq_all" (∀ k : Nat, k < eq.size → eq[k]! = pivot)
    invariant "inv_gt_all" (∀ k : Nat, k < gt.size → pivot < gt[k]!)
    -- Content preservation for the processed prefix (expressed via element counts).
    -- Init: both sides are counts of the empty arrays. Preserved: pushing x corresponds to
    -- extending the prefix by nums[i]!, and counts update consistently.
    invariant "inv_counts" (∀ x : Int, (lt ++ eq ++ gt).count x = (nums.extract 0 i).count x)
    -- Termination: distance to end of array.
    decreasing nums.size - i
  do
    let x := nums[i]!
    if x < pivot then
      lt := lt.push x
    else
      if x = pivot then
        eq := eq.push x
      else
        gt := gt.push x
    i := i + 1

  let resultArr := (lt ++ eq) ++ gt
  return resultArr
end Impl

section TestCases
-- Test case 1: Example 1
def test1_nums : Array Int := #[9, 12, 5, 10, 14, 3, 10]
def test1_pivot : Int := 10
def test1_Expected : Array Int := #[9, 5, 3, 10, 10, 12, 14]

-- Test case 2: Example 2
def test2_nums : Array Int := #[-3, 4, 3, 2]
def test2_pivot : Int := 2
def test2_Expected : Array Int := #[-3, 2, 4, 3]

-- Test case 3: Empty array
def test3_nums : Array Int := #[]
def test3_pivot : Int := 0
def test3_Expected : Array Int := #[]

-- Test case 4: Single element equal to pivot
def test4_nums : Array Int := #[7]
def test4_pivot : Int := 7
def test4_Expected : Array Int := #[7]

-- Test case 5: All elements less than pivot (result should equal input)
def test5_nums : Array Int := #[-5, -2, 0, 1]
def test5_pivot : Int := 10
def test5_Expected : Array Int := #[-5, -2, 0, 1]

-- Test case 6: All elements greater than pivot (result should equal input)
def test6_nums : Array Int := #[3, 4, 5]
def test6_pivot : Int := 2
def test6_Expected : Array Int := #[3, 4, 5]

-- Test case 7: All elements equal to pivot
def test7_nums : Array Int := #[2, 2, 2, 2]
def test7_pivot : Int := 2
def test7_Expected : Array Int := #[2, 2, 2, 2]

-- Test case 8: Mixed with duplicates across groups
def test8_nums : Array Int := #[1, 4, 2, 4, 3, 2, 5]
def test8_pivot : Int := 3
def test8_Expected : Array Int := #[1, 2, 2, 3, 4, 4, 5]

-- Test case 9: Pivot appears at ends and in middle
def test9_nums : Array Int := #[5, 1, 5, 2, 5, 3]
def test9_pivot : Int := 5
def test9_Expected : Array Int := #[1, 2, 3, 5, 5, 5]
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((PartitionArrayAccordingToPivot test1_nums test1_pivot).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((PartitionArrayAccordingToPivot test2_nums test2_pivot).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((PartitionArrayAccordingToPivot test3_nums test3_pivot).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((PartitionArrayAccordingToPivot test4_nums test4_pivot).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((PartitionArrayAccordingToPivot test5_nums test5_pivot).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((PartitionArrayAccordingToPivot test6_nums test6_pivot).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((PartitionArrayAccordingToPivot test7_nums test7_pivot).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((PartitionArrayAccordingToPivot test8_nums test8_pivot).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((PartitionArrayAccordingToPivot test9_nums test9_pivot).run), DivM.res test9_Expected ]
end Assertions

section Pbt
velvet_plausible_test PartitionArrayAccordingToPivot (config := { maxMs := some 20000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000

theorem goal_0
    (nums : Array ℤ)
    (eq : Array ℤ)
    (gt : Array ℤ)
    (lt : Array ℤ)
    (if_pos : lt.size + eq.size + gt.size < nums.size)
    (invariant_inv_counts : ∀ (x : ℤ), Array.count x lt + (Array.count x eq + Array.count x gt) = Array.count x (nums.extract (OfNat.ofNat 0) (lt.size + eq.size + gt.size)))
    : ∀ (x : ℤ), Array.count x (lt.push nums[lt.size + eq.size + gt.size]!) + (Array.count x eq + Array.count x gt) = Array.count x (nums.extract (OfNat.ofNat 0) (lt.size + eq.size + gt.size + OfNat.ofNat 1)) := by
  intro x
  set j : Nat := lt.size + eq.size + gt.size with hjdef
  have hj : j < nums.size := by
    simpa [j] using if_pos

  -- relate `getElem!` and `getElem` (in-bounds)
  have hgetD : nums.getD j default = nums[j] := by
    have hopt : nums[j]? = some nums[j] := by
      simpa using (Array.getElem?_eq_getElem (xs := nums) (i := j) hj)
    simp [Array.getD_eq_getD_getElem?, hopt]

  have hget! : nums[j]! = nums[j] := by
    calc
      nums[j]! = nums.getD j default := by
        simpa [Array.getElem!_eq_getD]
      _ = nums[j] := hgetD

  -- extract extended by one element is push of the next element
  have hextract : nums.extract 0 (j + 1) = (nums.extract 0 j).push nums[j]! := by
    have w : 0 < j + 1 := by
      simpa [Nat.succ_eq_add_one] using (Nat.succ_pos j)
    have hextract0 : nums.extract 0 (j + 1) = (nums.extract 0 j).push nums[j] := by
      simpa using (Array.extract_succ_right (i := 0) (j := j) w hj)
    -- rewrite `nums[j]!` to `nums[j]` using `hget!`
    simpa [hget!] using hextract0

  have hinv : Array.count x lt + (Array.count x eq + Array.count x gt) = Array.count x (nums.extract 0 j) := by
    simpa [j] using (invariant_inv_counts x)

  have hadd :
      (Array.count x lt + (if nums[j]! == x then 1 else 0)) + (Array.count x eq + Array.count x gt)
        = (Array.count x lt + (Array.count x eq + Array.count x gt)) + (if nums[j]! == x then 1 else 0) := by
    calc
      (Array.count x lt + (if nums[j]! == x then 1 else 0)) + (Array.count x eq + Array.count x gt)
          = Array.count x lt + ((if nums[j]! == x then 1 else 0) + (Array.count x eq + Array.count x gt)) := by
              simp [Nat.add_assoc]
      _ = Array.count x lt + ((Array.count x eq + Array.count x gt) + (if nums[j]! == x then 1 else 0)) := by
              simp [Nat.add_comm, Nat.add_assoc]
      _ = (Array.count x lt + (Array.count x eq + Array.count x gt)) + (if nums[j]! == x then 1 else 0) := by
              simp [Nat.add_assoc]

  calc
    Array.count x (lt.push nums[j]!) + (Array.count x eq + Array.count x gt)
        = (Array.count x lt + (if nums[j]! == x then 1 else 0)) + (Array.count x eq + Array.count x gt) := by
            simp [Array.count_push, Nat.add_assoc]
    _ = (Array.count x lt + (Array.count x eq + Array.count x gt)) + (if nums[j]! == x then 1 else 0) := hadd
    _ = Array.count x (nums.extract 0 j) + (if nums[j]! == x then 1 else 0) := by
            simpa [hinv, Nat.add_assoc]
    _ = Array.count x ((nums.extract 0 j).push nums[j]!) := by
            simp [Array.count_push, Nat.add_assoc]
    _ = Array.count x (nums.extract 0 (j + 1)) := by
            simpa [hextract]

theorem goal_1
    (nums : Array ℤ)
    (eq : Array ℤ)
    (gt : Array ℤ)
    (lt : Array ℤ)
    (if_pos : lt.size + eq.size + gt.size < nums.size)
    (invariant_inv_counts : ∀ (x : ℤ), Array.count x lt + (Array.count x eq + Array.count x gt) = Array.count x (nums.extract (OfNat.ofNat 0) (lt.size + eq.size + gt.size)))
    : ∀ (x : ℤ), Array.count x lt + (Array.count x (eq.push nums[lt.size + eq.size + gt.size]!) + Array.count x gt) = Array.count x (nums.extract (OfNat.ofNat 0) (lt.size + eq.size + gt.size + OfNat.ofNat 1)) := by
  intro x
  have if_pos' : eq.size + lt.size + gt.size < nums.size := by
    simpa [add_assoc, add_left_comm, add_comm] using if_pos
  have inv' : ∀ (x : ℤ),
      Array.count x eq + (Array.count x lt + Array.count x gt) =
        Array.count x (nums.extract 0 (eq.size + lt.size + gt.size)) := by
    intro x
    simpa [add_assoc, add_left_comm, add_comm] using (invariant_inv_counts x)
  have h := (goal_0 (nums := nums) (eq := lt) (gt := gt) (lt := eq) if_pos' inv') x
  simpa [add_assoc, add_left_comm, add_comm] using h

theorem goal_2
    (nums : Array ℤ)
    (eq : Array ℤ)
    (gt : Array ℤ)
    (lt : Array ℤ)
    (if_pos : lt.size + eq.size + gt.size < nums.size)
    (invariant_inv_counts : ∀ (x : ℤ), Array.count x lt + (Array.count x eq + Array.count x gt) = Array.count x (nums.extract (OfNat.ofNat 0) (lt.size + eq.size + gt.size)))
    : ∀ (x : ℤ), Array.count x lt + (Array.count x eq + Array.count x (gt.push nums[lt.size + eq.size + gt.size]!)) = Array.count x (nums.extract (OfNat.ofNat 0) (lt.size + eq.size + gt.size + OfNat.ofNat 1)) := by
  classical
  intro x
  set j : Nat := lt.size + eq.size + gt.size
  have hj : j < nums.size := by
    simpa [j] using if_pos

  have inv' : Array.count x lt + (Array.count x eq + Array.count x gt) = Array.count x (nums.extract 0 j) := by
    simpa [j] using invariant_inv_counts x

  have hextract : (nums.extract 0 j).push nums[j]! = nums.extract 0 (j + 1) := by
    have h' := (@Array.push_extract_getElem ℤ nums 0 j hj)
    have h'' : (nums.extract 0 j).push nums[j] = nums.extract 0 (j + 1) := by
      simpa [Nat.min_eq_left (Nat.zero_le j)] using h'
    have hget : nums[j] = nums[j]! := by
      simp [Array.getElem!_eq_getD, Array.getD, hj]
    -- rewrite the pushed element
    simpa [hget] using h''

  calc
    Array.count x lt + (Array.count x eq + Array.count x (gt.push nums[j]!))
        = Array.count x lt + (Array.count x eq + (Array.count x gt + if nums[j]! == x then 1 else 0)) := by
            simp [Array.count_push]
    _ = (Array.count x lt + (Array.count x eq + Array.count x gt)) + (if nums[j]! == x then 1 else 0) := by
          simp [Nat.add_assoc]
    _ = Array.count x (nums.extract 0 j) + (if nums[j]! == x then 1 else 0) := by
          simpa [inv']
    _ = Array.count x ((nums.extract 0 j).push nums[j]!) := by
          symm
          simp [Array.count_push, Nat.add_assoc]
    _ = Array.count x (nums.extract 0 (j + 1)) := by
          simpa [hextract]
    _ = Array.count x (nums.extract (OfNat.ofNat 0) (j + OfNat.ofNat 1)) := by
          simp

theorem goal_3_0
    (nums : Array ℤ)
    (pivot : ℤ)
    (i_1 : Array ℤ)
    (i_2 : Array ℤ)
    (lt_1 : Array ℤ)
    (invariant_inv_eq_all : ∀ k < i_1.size, i_1[k]! = pivot)
    (invariant_inv_gt_all : ∀ k < i_2.size, pivot < i_2[k]!)
    (invariant_inv_lt_all : ∀ k < lt_1.size, lt_1[k]! < pivot)
    (hSame : sameElementCounts nums (lt_1 ++ (i_1 ++ i_2)))
    : countLt nums pivot = lt_1.size := by
  classical

  -- For an in-bounds index, `xs[i]!` agrees with `xs[i]` with a proof.
  have getBang_eq_get (xs : Array ℤ) (i : Nat) (hi : i < xs.size) : xs[i]! = xs[i]'hi := by
    simp [Array.get!, hi]

  -- From `sameElementCounts`, we get a permutation of the underlying lists.
  have hperm : List.Perm nums.toList (lt_1 ++ (i_1 ++ i_2)).toList := by
    refine (List.perm_iff_count).2 ?_
    intro x
    simpa [Array.count_toList] using (hSame x).symm

  have hCountLt_eq : countLt nums pivot = countLt (lt_1 ++ (i_1 ++ i_2)) pivot := by
    have hcountP_list : nums.toList.countP (fun x : ℤ => decide (x < pivot)) =
        (lt_1 ++ (i_1 ++ i_2)).toList.countP (fun x : ℤ => decide (x < pivot)) :=
      List.Perm.countP_eq (p := fun x : ℤ => decide (x < pivot)) hperm
    simpa [countLt, Array.countP_toList] using hcountP_list

  -- Predicate facts for `countP_eq_size` / `countP_eq_zero`.
  have hLt_all_mem : ∀ a : ℤ, a ∈ lt_1 → decide (a < pivot) = true := by
    intro a ha
    rcases (Array.mem_iff_getElem).1 ha with ⟨i, hi, rfl⟩
    have h := invariant_inv_lt_all i hi
    have h' : lt_1[i]'hi < pivot := by
      simpa [getBang_eq_get lt_1 i hi] using h
    -- convert Prop to `decide ... = true`
    simpa [decide_eq_true_eq] using h'

  have hEq_all_mem : ∀ a : ℤ, a ∈ i_1 → a = pivot := by
    intro a ha
    rcases (Array.mem_iff_getElem).1 ha with ⟨i, hi, rfl⟩
    have h := invariant_inv_eq_all i hi
    have : i_1[i]'hi = pivot := by
      simpa [getBang_eq_get i_1 i hi] using h
    simpa using this

  have hGt_all_mem : ∀ a : ℤ, a ∈ i_2 → pivot < a := by
    intro a ha
    rcases (Array.mem_iff_getElem).1 ha with ⟨i, hi, rfl⟩
    have h := invariant_inv_gt_all i hi
    have : pivot < i_2[i]'hi := by
      simpa [getBang_eq_get i_2 i hi] using h
    simpa using this

  have hcountP_lt_1 : lt_1.countP (fun x : ℤ => decide (x < pivot)) = lt_1.size := by
    exact (Array.countP_eq_size (xs := lt_1) (p := fun x : ℤ => decide (x < pivot))).2 hLt_all_mem

  have hcountP_i1 : i_1.countP (fun x : ℤ => decide (x < pivot)) = 0 := by
    have hnot : ∀ a : ℤ, a ∈ i_1 → ¬ decide (a < pivot) = true := by
      intro a ha
      have ha' : a = pivot := hEq_all_mem a ha
      -- rewrite `a` to `pivot`
      cases ha'
      have : ¬ pivot < pivot := lt_irrefl pivot
      simpa [decide_eq_true_eq] using this
    exact (Array.countP_eq_zero (xs := i_1) (p := fun x : ℤ => decide (x < pivot))).2 hnot

  have hcountP_i2 : i_2.countP (fun x : ℤ => decide (x < pivot)) = 0 := by
    have hnot : ∀ a : ℤ, a ∈ i_2 → ¬ decide (a < pivot) = true := by
      intro a ha
      have hpa : pivot < a := hGt_all_mem a ha
      have : ¬ a < pivot := not_lt_of_ge (le_of_lt hpa)
      simpa [decide_eq_true_eq] using this
    exact (Array.countP_eq_zero (xs := i_2) (p := fun x : ℤ => decide (x < pivot))).2 hnot

  have hcountP_i1i2 : (i_1 ++ i_2).countP (fun x : ℤ => decide (x < pivot)) = 0 := by
    calc
      (i_1 ++ i_2).countP (fun x : ℤ => decide (x < pivot))
          = i_1.countP (fun x : ℤ => decide (x < pivot)) +
              i_2.countP (fun x : ℤ => decide (x < pivot)) := by
                simpa using (Array.countP_append (xs := i_1) (ys := i_2)
                  (p := fun x : ℤ => decide (x < pivot)))
      _ = 0 := by simp [hcountP_i1, hcountP_i2]

  have hCountLt_concat : countLt (lt_1 ++ (i_1 ++ i_2)) pivot = lt_1.size := by
    have : (lt_1 ++ (i_1 ++ i_2)).countP (fun x : ℤ => decide (x < pivot)) = lt_1.size := by
      calc
        (lt_1 ++ (i_1 ++ i_2)).countP (fun x : ℤ => decide (x < pivot))
            = lt_1.countP (fun x : ℤ => decide (x < pivot)) +
                (i_1 ++ i_2).countP (fun x : ℤ => decide (x < pivot)) := by
                  simpa using (Array.countP_append (xs := lt_1) (ys := (i_1 ++ i_2))
                    (p := fun x : ℤ => decide (x < pivot)))
        _ = lt_1.size + 0 := by simp [hcountP_lt_1, hcountP_i1i2]
        _ = lt_1.size := by simp
    simpa [countLt] using this

  calc
    countLt nums pivot = countLt (lt_1 ++ (i_1 ++ i_2)) pivot := hCountLt_eq
    _ = lt_1.size := hCountLt_concat

theorem goal_3_1_0
    (pivot : ℤ)
    (lt_1 : Array ℤ)
    (invariant_inv_lt_all : ∀ k < lt_1.size, lt_1[k]! < pivot)
    : Array.count pivot lt_1 = 0 := by
  have hnotmem : pivot ∉ lt_1 := by
    intro hmem
    rcases Array.getElem_of_mem hmem with ⟨i, hi, hget⟩
    have hbang : lt_1[i]! = lt_1[i]'hi := by
      -- `getElem!` is `getD` and reduces to `getElem` when in bounds.
      simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getD_getElem?, hi]
    have hget' : lt_1[i]! = pivot := by
      simpa [hbang] using hget
    have hlt : lt_1[i]! < pivot := invariant_inv_lt_all i hi
    have : pivot < pivot := by
      simpa [hget'] using hlt
    exact (lt_irrefl pivot) this
  exact (Array.count_eq_zero).2 hnotmem

theorem goal_3_1_1
    (pivot : ℤ)
    (i_2 : Array ℤ)
    (invariant_inv_gt_all : ∀ k < i_2.size, pivot < i_2[k]!)
    : Array.count pivot i_2 = 0 := by
  have hnotmem : pivot ∉ i_2 := by
    intro hmem
    rcases Array.getElem?_of_mem (xs := i_2) (a := pivot) hmem with ⟨i, hiopt⟩
    have hiLt : i < i_2.size := by
      rcases (Array.getElem?_eq_some_iff (xs := i_2) (i := i) (b := pivot)).1 hiopt with ⟨hiLt, _⟩
      exact hiLt
    have hgt : pivot < i_2[i]! := invariant_inv_gt_all i hiLt
    have hget : i_2[i]! = pivot := by
      simpa [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, hiopt]
    exact lt_irrefl pivot (by simpa [hget] using hgt)
  exact (Array.count_eq_zero (a := pivot) (xs := i_2)).2 hnotmem

theorem goal_3_1_2
    (pivot : ℤ)
    (i_1 : Array ℤ)
    (invariant_inv_eq_all : ∀ k < i_1.size, i_1[k]! = pivot)
    : Array.count pivot i_1 = i_1.size := by
    classical
    -- Use the characterization of `count = size` via membership.
    apply (Array.count_eq_size (a := pivot) (xs := i_1)).2
    intro b hb
    rcases Array.getElem_of_mem (xs := i_1) (a := b) hb with ⟨i, hi, hib⟩
    -- Relate `getElem!` (used in the invariant) to `getElem` (from membership).
    have hGet : i_1[i]! = i_1[i]'hi := by
      calc
        i_1[i]! = i_1.getD i default := by
          simpa using (Array.getElem!_eq_getD (xs := i_1) (i := i))
        _ = i_1[i]?.getD default := by
          simpa using (Array.getD_eq_getD_getElem? (xs := i_1) (i := i) (d := (default : ℤ)))
        _ = i_1[i]'hi := by
          have hg : i_1[i]? = some (i_1[i]'hi) := by
            simpa using (Array.getElem?_lt (xs := i_1) (i := i) hi)
          simp [hg]
    have hBang : i_1[i]! = pivot := invariant_inv_eq_all i hi
    have hElem : i_1[i]'hi = pivot := by
      simpa [hGet] using hBang
    calc
      pivot = i_1[i]'hi := by
        simpa using hElem.symm
      _ = b := by
        simpa using hib

theorem goal_3_1
    (nums : Array ℤ)
    (pivot : ℤ)
    (i_1 : Array ℤ)
    (i_2 : Array ℤ)
    (lt_1 : Array ℤ)
    (invariant_inv_eq_all : ∀ k < i_1.size, i_1[k]! = pivot)
    (invariant_inv_gt_all : ∀ k < i_2.size, pivot < i_2[k]!)
    (invariant_inv_lt_all : ∀ k < lt_1.size, lt_1[k]! < pivot)
    (invariant_inv_counts : ∀ (x : ℤ),
  Array.count x lt_1 + (Array.count x i_1 + Array.count x i_2) =
    Array.count x (nums.extract (OfNat.ofNat 0) (lt_1.size + i_1.size + i_2.size)))
    (hn : lt_1.size + i_1.size + i_2.size = nums.size)
    (hSame : sameElementCounts nums (lt_1 ++ (i_1 ++ i_2)))
    (hcL : countLt nums pivot = lt_1.size)
    : countEq nums pivot = i_1.size := by
    classical

    have hlt0 : lt_1.count pivot = 0 := by
      expose_names; exact (goal_3_1_0 pivot lt_1 invariant_inv_lt_all)

    have hgt0 : i_2.count pivot = 0 := by
      expose_names; exact (goal_3_1_1 pivot i_2 invariant_inv_gt_all)

    have heq : i_1.count pivot = i_1.size := by
      expose_names; exact (goal_3_1_2 pivot i_1 invariant_inv_eq_all)

    have hnumscount : nums.count pivot = i_1.size := by
      calc
        nums.count pivot = (lt_1 ++ (i_1 ++ i_2)).count pivot := by
          simpa using (Eq.symm (hSame pivot))
        _ = i_1.size := by
          -- compute the count in the concatenation
          simp [Array.count_append, hlt0, hgt0, heq, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

    have hEqCount : countEq nums pivot = nums.count pivot := by
      expose_names; intros; expose_names; try simp_all; try grind

    calc
      countEq nums pivot = nums.count pivot := hEqCount
      _ = i_1.size := hnumscount

theorem goal_3_2
    (nums : Array ℤ)
    (pivot : ℤ)
    (i_1 : Array ℤ)
    (i_2 : Array ℤ)
    (lt_1 : Array ℤ)
    (invariant_inv_eq_all : ∀ k < i_1.size, i_1[k]! = pivot)
    (invariant_inv_gt_all : ∀ k < i_2.size, pivot < i_2[k]!)
    (invariant_inv_lt_all : ∀ k < lt_1.size, lt_1[k]! < pivot)
    (hn : lt_1.size + i_1.size + i_2.size = nums.size)
    (hcL : countLt nums pivot = lt_1.size)
    (hcE : countEq nums pivot = i_1.size)
    : isThreeBlockPartition nums pivot (lt_1 ++ (i_1 ++ i_2)) := by
  classical

  -- Normalize the count equalities to the unfolded form that appears after `dsimp`.
  have hcL' : Array.countP (fun x => decide (x < pivot)) nums = lt_1.size := by
    simpa [countLt] using hcL
  have hcE' : Array.countP (fun x => decide (x = pivot)) nums = i_1.size := by
    simpa [countEq] using hcE

  -- Helper: in-bounds `get!` agrees with `getElem`.
  have getBang_eq_getElem {α} [Inhabited α] (xs : Array α) (i : Nat) (h : i < xs.size) :
      xs[i]! = xs[i]'h := by
    rw [Array.getElem!_eq_getD]
    rw [Array.getD_eq_getD_getElem?]
    rw [Array.getD_getElem?]
    have hp : i < xs.size := h
    simp [hp]

  dsimp [isThreeBlockPartition]
  constructor
  · -- size equality
    calc
      (lt_1 ++ (i_1 ++ i_2)).size
          = lt_1.size + ((i_1 ++ i_2).size) := by
              simpa [Array.size_append]
      _   = lt_1.size + (i_1.size + i_2.size) := by
              simp [Array.size_append, Nat.add_assoc]
      _   = nums.size := by
              simpa [Nat.add_assoc] using hn
  · intro i hi
    constructor
    · intro hltCount
      have hilt : i < lt_1.size := by
        simpa [hcL'] using hltCount
      have hget : (lt_1 ++ (i_1 ++ i_2))[i]'hi = lt_1[i]'hilt := by
        simpa using
          (Array.getElem_append_left (xs := lt_1) (ys := (i_1 ++ i_2)) (i := i)
            (h := hi) hilt)
      have inv : lt_1[i]! < pivot := invariant_inv_lt_all i hilt
      have hbang_lt : lt_1[i]! = lt_1[i]'hilt := getBang_eq_getElem lt_1 i hilt
      -- rewrite the invariant into the `getElem` form
      have inv' : lt_1[i]'hilt < pivot := by
        simpa [hbang_lt] using inv
      have hres' : (lt_1 ++ (i_1 ++ i_2))[i]'hi < pivot := by
        simpa [hget] using inv'
      have hbang_res : (lt_1 ++ (i_1 ++ i_2))[i]! = (lt_1 ++ (i_1 ++ i_2))[i]'hi :=
        getBang_eq_getElem (lt_1 ++ (i_1 ++ i_2)) i hi
      -- rewrite the goal to `getElem`
      simpa [hbang_res] using hres'
    · constructor
      · intro hRange
        have hle : lt_1.size ≤ i := by
          have := hRange.1
          simpa [hcL'] using this
        have hlt : i < lt_1.size + i_1.size := by
          have := hRange.2
          simpa [hcL', hcE', Nat.add_assoc] using this

        let j : Nat := i - lt_1.size
        have hj_lt_i1 : j < i_1.size := by
          have : i - lt_1.size < i_1.size :=
            Nat.sub_lt_left_of_lt_add hle (by simpa [Nat.add_assoc] using hlt)
          simpa [j] using this

        have hi_sum : i < lt_1.size + (i_1 ++ i_2).size := by
          simpa [Array.size_append] using hi
        have hj_lt_inner : j < (i_1 ++ i_2).size := by
          have : i - lt_1.size < (i_1 ++ i_2).size := Nat.sub_lt_left_of_lt_add hle hi_sum
          simpa [j] using this

        -- outer append (right side)
        have hj0 : i - lt_1.size < (i_1 ++ i_2).size := Nat.sub_lt_left_of_lt_add hle hi_sum
        have hget_outer : (lt_1 ++ (i_1 ++ i_2))[i]'hi = (i_1 ++ i_2)[j]'hj_lt_inner := by
          -- the lemma gives the same access with a (definitional) proof term; rewrite proofs away
          have hget0 : (lt_1 ++ (i_1 ++ i_2))[i]'hi = (i_1 ++ i_2)[i - lt_1.size]'hj0 := by
            simpa using
              (Array.getElem_append_right (xs := lt_1) (ys := (i_1 ++ i_2)) (i := i) (h := hi) hle)
          -- `j` is definitional `i - lt_1.size`
          simpa [j] using hget0

        -- inner append (left side)
        have hget_inner : (i_1 ++ i_2)[j]'hj_lt_inner = i_1[j]'hj_lt_i1 := by
          simpa using
            (Array.getElem_append_left (xs := i_1) (ys := i_2) (i := j)
              (h := (by simpa [Array.size_append] using hj_lt_inner)) hj_lt_i1)

        have inv : i_1[j]! = pivot := invariant_inv_eq_all j hj_lt_i1
        have hbang_i1 : i_1[j]! = i_1[j]'hj_lt_i1 := getBang_eq_getElem i_1 j hj_lt_i1
        have inv' : i_1[j]'hj_lt_i1 = pivot := by
          simpa [hbang_i1] using inv

        have hres' : (lt_1 ++ (i_1 ++ i_2))[i]'hi = pivot := by
          simpa [hget_outer, hget_inner] using inv'

        have hbang_res : (lt_1 ++ (i_1 ++ i_2))[i]! = (lt_1 ++ (i_1 ++ i_2))[i]'hi :=
          getBang_eq_getElem (lt_1 ++ (i_1 ++ i_2)) i hi
        simpa [hbang_res] using hres'

      · intro hGe
        have hige : lt_1.size + i_1.size ≤ i := by
          simpa [hcL', hcE', Nat.add_assoc] using hGe
        have hle_outer : lt_1.size ≤ i :=
          le_trans (Nat.le_add_right lt_1.size i_1.size) hige

        let j : Nat := i - lt_1.size
        have hi_sum : i < lt_1.size + (i_1 ++ i_2).size := by
          simpa [Array.size_append] using hi
        have hj_lt_inner : j < (i_1 ++ i_2).size := by
          have : i - lt_1.size < (i_1 ++ i_2).size := Nat.sub_lt_left_of_lt_add hle_outer hi_sum
          simpa [j] using this

        have hj0 : i - lt_1.size < (i_1 ++ i_2).size := Nat.sub_lt_left_of_lt_add hle_outer hi_sum
        have hget_outer : (lt_1 ++ (i_1 ++ i_2))[i]'hi = (i_1 ++ i_2)[j]'hj_lt_inner := by
          have hget0 : (lt_1 ++ (i_1 ++ i_2))[i]'hi = (i_1 ++ i_2)[i - lt_1.size]'hj0 := by
            simpa using
              (Array.getElem_append_right (xs := lt_1) (ys := (i_1 ++ i_2)) (i := i) (h := hi) hle_outer)
          simpa [j] using hget0

        have hle_inner : i_1.size ≤ j := by
          have := Nat.sub_le_sub_right hige lt_1.size
          have : i_1.size ≤ i - lt_1.size := by
            simpa [Nat.add_sub_cancel_left] using this
          simpa [j] using this

        let k : Nat := j - i_1.size
        have hj_lt_sum : j < i_1.size + i_2.size := by
          simpa [Array.size_append] using hj_lt_inner
        have hk_lt_i2 : k < i_2.size := by
          have : j - i_1.size < i_2.size :=
            Nat.sub_lt_left_of_lt_add hle_inner (by simpa [Nat.add_assoc] using hj_lt_sum)
          simpa [k] using this

        -- inner append (right side)
        have hk0 : j - i_1.size < i_2.size :=
          Nat.sub_lt_left_of_lt_add hle_inner (by simpa [Nat.add_assoc] using hj_lt_sum)
        have hget_inner : (i_1 ++ i_2)[j]'hj_lt_inner = i_2[k]'hk_lt_i2 := by
          have hget0 : (i_1 ++ i_2)[j]'hj_lt_inner = i_2[j - i_1.size]'hk0 := by
            simpa using
              (Array.getElem_append_right (xs := i_1) (ys := i_2) (i := j)
                (h := (by simpa [Array.size_append] using hj_lt_inner)) hle_inner)
          simpa [k] using hget0

        have inv : pivot < i_2[k]! := invariant_inv_gt_all k hk_lt_i2
        have hbang_i2 : i_2[k]! = i_2[k]'hk_lt_i2 := getBang_eq_getElem i_2 k hk_lt_i2
        have inv' : pivot < i_2[k]'hk_lt_i2 := by
          simpa [hbang_i2] using inv

        have hres' : pivot < (lt_1 ++ (i_1 ++ i_2))[i]'hi := by
          simpa [hget_outer, hget_inner] using inv'

        have hbang_res : (lt_1 ++ (i_1 ++ i_2))[i]! = (lt_1 ++ (i_1 ++ i_2))[i]'hi :=
          getBang_eq_getElem (lt_1 ++ (i_1 ++ i_2)) i hi
        simpa [hbang_res] using hres'

theorem goal_3
    (nums : Array ℤ)
    (pivot : ℤ)
    (i_1 : Array ℤ)
    (i_2 : Array ℤ)
    (lt_1 : Array ℤ)
    (invariant_inv_eq_all : ∀ k < i_1.size, i_1[k]! = pivot)
    (invariant_inv_gt_all : ∀ k < i_2.size, pivot < i_2[k]!)
    (invariant_inv_lt_all : ∀ k < lt_1.size, lt_1[k]! < pivot)
    (invariant_inv_bounds : lt_1.size + i_1.size + i_2.size ≤ nums.size)
    (done_1 : nums.size ≤ lt_1.size + i_1.size + i_2.size)
    (invariant_inv_counts : ∀ (x : ℤ), Array.count x lt_1 + (Array.count x i_1 + Array.count x i_2) = Array.count x (nums.extract (OfNat.ofNat 0) (lt_1.size + i_1.size + i_2.size)))
    : postcondition nums pivot (lt_1 ++ (i_1 ++ i_2)) := by
  classical
  have hn : lt_1.size + i_1.size + i_2.size = nums.size := by
    expose_names; intros; expose_names; try simp_all; try grind
  have hSame : sameElementCounts nums (lt_1 ++ (i_1 ++ i_2)) := by
    expose_names; intros; expose_names; try simp_all; try grind
  have hcL : countLt nums pivot = lt_1.size := by
    expose_names; exact (goal_3_0 nums pivot i_1 i_2 lt_1 invariant_inv_eq_all invariant_inv_gt_all invariant_inv_lt_all hSame)
  have hcE : countEq nums pivot = i_1.size := by
    expose_names; exact (goal_3_1 nums pivot i_1 i_2 lt_1 invariant_inv_eq_all invariant_inv_gt_all invariant_inv_lt_all invariant_inv_counts hn hSame hcL)
  have hPart : isThreeBlockPartition nums pivot (lt_1 ++ (i_1 ++ i_2)) := by
    expose_names; exact (goal_3_2 nums pivot i_1 i_2 lt_1 invariant_inv_eq_all invariant_inv_gt_all invariant_inv_lt_all hn hcL hcE)
  exact And.intro hPart hSame


prove_correct PartitionArrayAccordingToPivot by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at *); try (conv => congr <;> simp) ; try expose_names)
  exact (goal_0 nums eq gt lt if_pos invariant_inv_counts)
  exact (goal_1 nums eq gt lt if_pos invariant_inv_counts)
  exact (goal_2 nums eq gt lt if_pos invariant_inv_counts)
  exact (goal_3 nums pivot i_1 i_2 lt_1 invariant_inv_eq_all invariant_inv_gt_all invariant_inv_lt_all invariant_inv_bounds done_1 invariant_inv_counts)
end Proof
