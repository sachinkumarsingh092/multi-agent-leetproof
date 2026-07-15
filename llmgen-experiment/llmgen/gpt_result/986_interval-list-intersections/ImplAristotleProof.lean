import Mathlib.Tactic

-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false

/- Problem Description
    IntervalListIntersections: Intersect two sorted, pairwise-disjoint lists of closed integer intervals.
    Natural language breakdown:
    1. Each interval is a pair (start, end) representing the closed set of integers {x | start ≤ x ∧ x ≤ end}.
    2. Each input list is sorted by start ascending.
    3. Intervals in the same list are pairwise disjoint (non-overlapping); because they are closed, disjointness means the end of one is strictly less than the start of the next.
    4. The output is the list of all non-empty intersections between an interval from the first list and an interval from the second list.
    5. Each intersection of two closed intervals is either empty or a closed interval [max starts, min ends].
    6. The output list should be sorted and pairwise disjoint.
    7. Semantically, the union of the output intervals equals the set intersection of the unions of the input interval sets.
    Your algorithm should run in **O(m+n)** time and **O(1)** extra space, where m and n are the sizes of the two input lists.
-/

section Specs
-- An interval is represented as a pair (start, end).
abbrev Interval := Int × Int

-- Convert an interval to the set of integers it denotes.
def intervalSet (iv : Interval) : Set Int :=
  Set.Icc iv.1 iv.2

-- The interval is well-formed.
def isValidInterval (iv : Interval) : Prop :=
  iv.1 ≤ iv.2

-- Array is sorted by starts (nondecreasing).
def sortedByStart (a : Array Interval) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < a.size → a[i]!.1 ≤ a[j]!.1

-- Array is pairwise disjoint in the strong closed-interval sense.
-- This implies that whenever i < j, the i-th interval ends strictly before the j-th interval begins.
def pairwiseDisjointClosed (a : Array Interval) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < a.size → a[i]!.2 < a[j]!.1

-- The union of all interval sets represented by an array.
def unionIntervalSets (a : Array Interval) : Set Int :=
  {x : Int | ∃ (i : Nat), i < a.size ∧ x ∈ intervalSet a[i]!}

-- Precondition: both lists contain only valid intervals and are sorted/disjoint.
def precondition (firstList : Array Interval) (secondList : Array Interval) : Prop :=
  (∀ (i : Nat), i < firstList.size → isValidInterval firstList[i]!) ∧
  (∀ (i : Nat), i < secondList.size → isValidInterval secondList[i]!) ∧
  sortedByStart firstList ∧
  sortedByStart secondList ∧
  pairwiseDisjointClosed firstList ∧
  pairwiseDisjointClosed secondList

-- Postcondition: output is a valid sorted/disjoint interval list whose union equals the set intersection
-- of the unions of input lists.
def postcondition (firstList : Array Interval) (secondList : Array Interval)
  (result : Array Interval) : Prop :=
  (∀ (k : Nat), k < result.size → isValidInterval result[k]!) ∧
  sortedByStart result ∧
  pairwiseDisjointClosed result ∧
  unionIntervalSets result = (unionIntervalSets firstList ∩ unionIntervalSets secondList)
end Specs

section TestCases
-- Test case 1: Example 1 from the prompt
-- firstList = [[0,2],[5,10],[13,23],[24,25]]
-- secondList = [[1,5],[8,12],[15,24],[25,26]]
-- expected = [[1,2],[5,5],[8,10],[15,23],[24,24],[25,25]]
def test1_firstList : Array Interval := #[(0,2),(5,10),(13,23),(24,25)]
def test1_secondList : Array Interval := #[(1,5),(8,12),(15,24),(25,26)]
def test1_Expected : Array Interval := #[(1,2),(5,5),(8,10),(15,23),(24,24),(25,25)]

-- Test case 2: Example 2 from the prompt (second list empty)
def test2_firstList : Array Interval := #[(1,3),(5,9)]
def test2_secondList : Array Interval := #[]
def test2_Expected : Array Interval := #[]

-- Test case 3: first list empty

def test3_firstList : Array Interval := #[]
def test3_secondList : Array Interval := #[(1,2)]
def test3_Expected : Array Interval := #[]

-- Test case 4: both lists empty

def test4_firstList : Array Interval := #[]
def test4_secondList : Array Interval := #[]
def test4_Expected : Array Interval := #[]

-- Test case 5: single interval overlaps producing a non-degenerate intersection

def test5_firstList : Array Interval := #[(1,5)]
def test5_secondList : Array Interval := #[(2,3)]
def test5_Expected : Array Interval := #[(2,3)]

-- Test case 6: single interval intersection is a point

def test6_firstList : Array Interval := #[(1,2)]
def test6_secondList : Array Interval := #[(2,4)]
def test6_Expected : Array Interval := #[(2,2)]

-- Test case 7: no overlaps at all

def test7_firstList : Array Interval := #[(1,2)]
def test7_secondList : Array Interval := #[(3,4)]
def test7_Expected : Array Interval := #[]

-- Test case 8: negative numbers and multiple intersections

def test8_firstList : Array Interval := #[(-5,-3),(-1,2),(4,4)]
def test8_secondList : Array Interval := #[(-4,-2),(0,0),(3,5)]
def test8_Expected : Array Interval := #[(-4,-3),(0,0),(4,4)]

-- Test case 9: intersections where one interval from second overlaps two from first (due to disjointness, this can happen)

def test9_firstList : Array Interval := #[(0,1),(3,5),(7,9)]
def test9_secondList : Array Interval := #[(1,7)]
def test9_Expected : Array Interval := #[(1,1),(3,5),(7,7)]
end TestCases

section Proof

/-
PROVIDED SOLUTION
This is similar in structure to goal_6 and goal_7 which were already proved. The key difference is that here we DO add an intersection interval to the output (out.push ...) and advance j.

Strategy: Use ext to reduce to element membership. For the forward direction, take x in the LHS. If x came from an old element of out (index < out.size), use invariant_inv_semantic to place it in the RHS. If x came from the newly pushed element (index = out.size), then x is in the intersection of firstList[i] and secondList[j], which means x is in firstList[i] (so in the full firstList union) and x is in secondList[j] (index j, which is < j+1), so x is in the right side of the union on the RHS.

For the backward direction, take x in the RHS. If x came from the left side of the union (processed first-list intervals intersected with all of second list), use invariant_inv_semantic backwards to find x in out, then x is also in out.push. If x came from the right side (all first-list intervals intersected with processed second-list intervals up to j+1), check if the second-list witness l is < j or = j. If l < j, use invariant_inv_semantic backwards. If l = j, then x is in firstList[k] ∩ secondList[j]. If k = i, x is in the pushed interval. If k < i, x is in firstList.extract 0 i ∩ secondList, so by invariant_inv_semantic it's in out. If k > i, we need to show x is in the pushed interval — but actually k > i means firstList[k].1 > firstList[i].2 ≥ secondList[j].2 ≥ x (using pairwise disjointness and if_neg), contradiction.

Key lemmas to use: Array.getElem_push, Array.size_push, Array.getElem_extract. Use split_ifs to handle the min/max conditions. Use omega for natural number arithmetic and Int.le_antisymm or linarith for integer inequalities.
-/
theorem goal_5 (firstList : Array Interval) (secondList : Array Interval) (require_1 : (∀ i < firstList.size, firstList[i]!.1 ≤ firstList[i]!.2) ∧ (∀ i < secondList.size, secondList[i]!.1 ≤ secondList[i]!.2) ∧ (∀ (i j : ℕ), i < j → j < firstList.size → firstList[i]!.1 ≤ firstList[j]!.1) ∧ (∀ (i j : ℕ), i < j → j < secondList.size → secondList[i]!.1 ≤ secondList[j]!.1) ∧ (∀ (i j : ℕ), i < j → j < firstList.size → firstList[i]!.2 < firstList[j]!.1) ∧ ∀ (i j : ℕ), i < j → j < secondList.size → secondList[i]!.2 < secondList[j]!.1) (i : ℕ) (j : ℕ) (out : Array Interval) (a : i ≤ firstList.size) (a_1 : j ≤ secondList.size) (invariant_inv_out_valid : ∀ k < out.size, out[k]!.1 ≤ out[k]!.2) (invariant_inv_out_sorted : ∀ (i j : ℕ), i < j → j < out.size → out[i]!.1 ≤ out[j]!.1) (invariant_inv_out_disjoint : ∀ (i j : ℕ), i < j → j < out.size → out[i]!.2 < out[j]!.1) (a_2 : i < firstList.size) (a_3 : j < secondList.size) (invariant_inv_semantic : {x | ∃ i < out.size, out[i]!.1 ≤ x ∧ x ≤ out[i]!.2} = {x | ∃ i_1, (i_1 < i ∧ i_1 < firstList.size) ∧ (firstList.extract (OfNat.ofNat 0) i)[i_1]!.1 ≤ x ∧ x ≤ (firstList.extract (OfNat.ofNat 0) i)[i_1]!.2} ∩ {x | ∃ i < secondList.size, secondList[i]!.1 ≤ x ∧ x ≤ secondList[i]!.2} ∪ {x | ∃ i < firstList.size, firstList[i]!.1 ≤ x ∧ x ≤ firstList[i]!.2} ∩ {x | ∃ i, (i < j ∧ i < secondList.size) ∧ (secondList.extract (OfNat.ofNat 0) j)[i]!.1 ≤ x ∧ x ≤ (secondList.extract (OfNat.ofNat 0) j)[i]!.2}) (if_pos : (if secondList[j]!.1 ≤ firstList[i]!.1 then firstList[i]!.1 else secondList[j]!.1) ≤ if firstList[i]!.2 ≤ secondList[j]!.2 then firstList[i]!.2 else secondList[j]!.2) (if_neg : secondList[j]!.2 ≤ firstList[i]!.2) : {x | ∃ i_1 < out.size + OfNat.ofNat 1, (out.push (if secondList[j]!.1 ≤ firstList[i]!.1 then firstList[i]!.1 else secondList[j]!.1, if firstList[i]!.2 ≤ secondList[j]!.2 then firstList[i]!.2 else secondList[j]!.2))[i_1]!.1 ≤ x ∧ x ≤ (out.push (if secondList[j]!.1 ≤ firstList[i]!.1 then firstList[i]!.1 else secondList[j]!.1, if firstList[i]!.2 ≤ secondList[j]!.2 then firstList[i]!.2 else secondList[j]!.2))[i_1]!.2} = {x | ∃ i_1, (i_1 < i ∧ i_1 < firstList.size) ∧ (firstList.extract (OfNat.ofNat 0) i)[i_1]!.1 ≤ x ∧ x ≤ (firstList.extract (OfNat.ofNat 0) i)[i_1]!.2} ∩ {x | ∃ i < secondList.size, secondList[i]!.1 ≤ x ∧ x ≤ secondList[i]!.2} ∪ {x | ∃ i < firstList.size, firstList[i]!.1 ≤ x ∧ x ≤ firstList[i]!.2} ∩ {x | ∃ i, (i < j + OfNat.ofNat 1 ∧ i < secondList.size) ∧ (secondList.extract (OfNat.ofNat 0) (j + OfNat.ofNat 1))[i]!.1 ≤ x ∧ x ≤ (secondList.extract (OfNat.ofNat 0) (j + OfNat.ofNat 1))[i]!.2} := by
    ext x; simp_all +decide [ Set.ext_iff ] ;
    constructor;
    · rintro ⟨ k, hk₁, hk₂, hk₃ ⟩ ; by_cases hk₄ : k < out.size <;> simp_all +decide [ Array.push ] ;
      · specialize invariant_inv_semantic x;
        refine' invariant_inv_semantic.mp ⟨ k, hk₄, _, _ ⟩ |> Or.imp id fun h => _;
        · grind;
        · grind +ring;
        · grind +ring;
      · refine' Or.inr ⟨ _, j, ⟨ le_rfl, a_3 ⟩, _ ⟩;
        · use i;
          grind +ring;
        · grind;
    · rintro ( ⟨ ⟨ k, hk₁, hk₂, hk₃ ⟩, l, hl₁, hl₂, hl₃ ⟩ | ⟨ ⟨ k, hk₁, hk₂, hk₃ ⟩, l, hl₁, hl₂, hl₃ ⟩ ) <;> simp_all +decide [ Array.getElem_push ];
      · specialize invariant_inv_semantic x;
        simp_all +decide [ Array.push ];
        by_cases h : ∃ i < out.size, out[i]!.1 ≤ x ∧ x ≤ out[i]!.2 <;> simp_all +decide [ List.getElem?_append ];
        · grind;
        · exact absurd ( invariant_inv_semantic.1 k hk₁.1 hk₁.2 hk₂ hk₃ l hl₁ hl₂ ) ( by linarith );
      · by_cases h : k < i ∨ l < j <;> simp_all +decide [ Array.getElem_push ];
        · rcases h with ( h | h );
          · obtain ⟨ m, hm₁, hm₂, hm₃ ⟩ := invariant_inv_semantic x |>.2 ( Or.inl ⟨ ⟨ k, ⟨ h, hk₁ ⟩, by
              grind ⟩, ⟨ l, hl₁.2, by
              grind ⟩ ⟩ );
            use m; simp_all +decide [ Array.getElem_push ] ;
            grind +ring;
          · contrapose! invariant_inv_semantic;
            use x; simp_all +decide [ Array.getElem_push ] ;
            refine Or.inr ⟨ ?_, ?_ ⟩;
            · grind;
            · refine Or.inr ⟨ ⟨ k, hk₁, ?_, ?_ ⟩, ⟨ l, ⟨ h, hl₁.2 ⟩, ?_, ?_ ⟩ ⟩ <;> simp_all +decide [ Array.getElem_extract ];
        · cases h.1.eq_or_lt <;> cases h.2.eq_or_lt <;> first | linarith | simp_all +decide [ Array.getElem_push ] ;
          · use out.size; simp_all +decide [ Array.getElem_push ] ;
            grind;
          · grind +ring

/-
PROVIDED SOLUTION
This is the loop invariant update when firstList[i].2 < secondList[j].2 (if_pos) AND the intersection is empty (if_neg says hi < lo). We advance i (i becomes i+1). The output doesn't change. We need to show the semantic invariant is maintained with i+1 instead of i.

Key idea: Since the intersection of firstList[i] and secondList[j] is empty (hi < lo), and firstList[i].2 < secondList[j].2, the interval firstList[i] doesn't intersect secondList[j] or any later second-list interval either (firstList[i] ends before secondList[j] starts, or more precisely max(starts) > min(ends)). Also firstList[i] ends before secondList[j] starts essentially. So adding firstList[i] to the "processed from first list" set doesn't change the intersection with the full second list.

The set equality on the right side changes by extending firstList.extract 0 i to firstList.extract 0 (i+1), adding firstList[i]. We need to show that firstList[i] intersected with the full secondList only contributes elements already in the left side of the union, but since the intersection is empty this adds nothing.

Try ext, simp, and omega with case analysis. The key insight is that if the intersection of firstList[i] with secondList[j] is empty AND firstList[i].2 < secondList[j].2, then firstList[i] doesn't intersect any secondList interval from j onward (because they start later), and intervals before j are already accounted for.
-/
theorem goal_6 (firstList : Array Interval) (secondList : Array Interval) (require_1 : (∀ i < firstList.size, firstList[i]!.1 ≤ firstList[i]!.2) ∧ (∀ i < secondList.size, secondList[i]!.1 ≤ secondList[i]!.2) ∧ (∀ (i j : ℕ), i < j → j < firstList.size → firstList[i]!.1 ≤ firstList[j]!.1) ∧ (∀ (i j : ℕ), i < j → j < secondList.size → secondList[i]!.1 ≤ secondList[j]!.1) ∧ (∀ (i j : ℕ), i < j → j < firstList.size → firstList[i]!.2 < firstList[j]!.1) ∧ ∀ (i j : ℕ), i < j → j < secondList.size → secondList[i]!.2 < secondList[j]!.1) (i : ℕ) (j : ℕ) (out : Array Interval) (a : i ≤ firstList.size) (a_1 : j ≤ secondList.size) (invariant_inv_out_valid : ∀ k < out.size, out[k]!.1 ≤ out[k]!.2) (invariant_inv_out_sorted : ∀ (i j : ℕ), i < j → j < out.size → out[i]!.1 ≤ out[j]!.1) (invariant_inv_out_disjoint : ∀ (i j : ℕ), i < j → j < out.size → out[i]!.2 < out[j]!.1) (a_2 : i < firstList.size) (a_3 : j < secondList.size) (if_pos : firstList[i]!.2 < secondList[j]!.2) (invariant_inv_semantic : {x | ∃ i < out.size, out[i]!.1 ≤ x ∧ x ≤ out[i]!.2} = {x | ∃ i_1, (i_1 < i ∧ i_1 < firstList.size) ∧ (firstList.extract (OfNat.ofNat 0) i)[i_1]!.1 ≤ x ∧ x ≤ (firstList.extract (OfNat.ofNat 0) i)[i_1]!.2} ∩ {x | ∃ i < secondList.size, secondList[i]!.1 ≤ x ∧ x ≤ secondList[i]!.2} ∪ {x | ∃ i < firstList.size, firstList[i]!.1 ≤ x ∧ x ≤ firstList[i]!.2} ∩ {x | ∃ i, (i < j ∧ i < secondList.size) ∧ (secondList.extract (OfNat.ofNat 0) j)[i]!.1 ≤ x ∧ x ≤ (secondList.extract (OfNat.ofNat 0) j)[i]!.2}) (if_neg : (if firstList[i]!.2 ≤ secondList[j]!.2 then firstList[i]!.2 else secondList[j]!.2) < if secondList[j]!.1 ≤ firstList[i]!.1 then firstList[i]!.1 else secondList[j]!.1) : {x | ∃ i < out.size, out[i]!.1 ≤ x ∧ x ≤ out[i]!.2} = {x | ∃ i_1, (i_1 < i + OfNat.ofNat 1 ∧ i_1 < firstList.size) ∧ (firstList.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1))[i_1]!.1 ≤ x ∧ x ≤ (firstList.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1))[i_1]!.2} ∩ {x | ∃ i < secondList.size, secondList[i]!.1 ≤ x ∧ x ≤ secondList[i]!.2} ∪ {x | ∃ i < firstList.size, firstList[i]!.1 ≤ x ∧ x ≤ firstList[i]!.2} ∩ {x | ∃ i, (i < j ∧ i < secondList.size) ∧ (secondList.extract (OfNat.ofNat 0) j)[i]!.1 ≤ x ∧ x ≤ (secondList.extract (OfNat.ofNat 0) j)[i]!.2} := by
    split_ifs at if_neg <;> simp_all +decide [ Nat.lt_succ_iff ];
    · linarith [ require_1.1 i a_2 ];
    · ext x;
      constructor <;> intro h <;> rcases h with ( h | h ) <;> simp_all +decide [ Nat.lt_succ_iff ];
      · grind;
      · rcases h with ⟨ ⟨ k, ⟨ hk₁, hk₂ ⟩, hk₃, hk₄ ⟩, ⟨ l, hl₁, hl₂, hl₃ ⟩ ⟩ ; rcases lt_trichotomy k i with hk' | rfl | hk' <;> simp_all +decide [ Nat.lt_succ_iff ] ;
        · refine Or.inl ⟨ k, ⟨ hk', hk₂ ⟩, ?_, ?_ ⟩ <;> simp_all +decide [ Array.getElem_extract ];
        · by_cases hl : l < j;
          · refine Or.inr ⟨ ⟨ k, a_2, ?_, ?_ ⟩, ⟨ l, ⟨ hl, hl₁ ⟩, ?_, ?_ ⟩ ⟩ <;> aesop;
          · cases lt_or_eq_of_le ( le_of_not_gt hl ) <;> simp_all +decide [ Nat.lt_succ_iff ];
            · grind;
            · grind;
        · linarith;
    · linarith;
    · linarith [ require_1.2.1 j a_3 ]

/-
PROVIDED SOLUTION
This is the loop invariant update when the intersection is empty (if_neg) AND secondList[j].2 ≤ firstList[i].2 (if_neg_1), so we advance j (j becomes j+1). The output doesn't change. We need to show the semantic invariant is maintained with j+1 instead of j.

Key idea: Since the intersection of firstList[i] and secondList[j] is empty and secondList[j].2 ≤ firstList[i].2, the interval secondList[j] doesn't intersect firstList[i] or any later first-list interval. So adding secondList[j] to the "processed from second list" set doesn't change the intersection with the full first list.

The set equality on the right side changes by extending secondList.extract 0 j to secondList.extract 0 (j+1). We need to show that the full firstList intersected with secondList[j] is empty (already accounted for), so extending doesn't change anything.

This is symmetric to goal_6. Try ext, simp, omega with case analysis.
-/
theorem goal_7 (firstList : Array Interval) (secondList : Array Interval) (require_1 : (∀ i < firstList.size, firstList[i]!.1 ≤ firstList[i]!.2) ∧ (∀ i < secondList.size, secondList[i]!.1 ≤ secondList[i]!.2) ∧ (∀ (i j : ℕ), i < j → j < firstList.size → firstList[i]!.1 ≤ firstList[j]!.1) ∧ (∀ (i j : ℕ), i < j → j < secondList.size → secondList[i]!.1 ≤ secondList[j]!.1) ∧ (∀ (i j : ℕ), i < j → j < firstList.size → firstList[i]!.2 < firstList[j]!.1) ∧ ∀ (i j : ℕ), i < j → j < secondList.size → secondList[i]!.2 < secondList[j]!.1) (i : ℕ) (j : ℕ) (out : Array Interval) (a : i ≤ firstList.size) (a_1 : j ≤ secondList.size) (invariant_inv_out_valid : ∀ k < out.size, out[k]!.1 ≤ out[k]!.2) (invariant_inv_out_sorted : ∀ (i j : ℕ), i < j → j < out.size → out[i]!.1 ≤ out[j]!.1) (invariant_inv_out_disjoint : ∀ (i j : ℕ), i < j → j < out.size → out[i]!.2 < out[j]!.1) (a_2 : i < firstList.size) (a_3 : j < secondList.size) (invariant_inv_semantic : {x | ∃ i < out.size, out[i]!.1 ≤ x ∧ x ≤ out[i]!.2} = {x | ∃ i_1, (i_1 < i ∧ i_1 < firstList.size) ∧ (firstList.extract (OfNat.ofNat 0) i)[i_1]!.1 ≤ x ∧ x ≤ (firstList.extract (OfNat.ofNat 0) i)[i_1]!.2} ∩ {x | ∃ i < secondList.size, secondList[i]!.1 ≤ x ∧ x ≤ secondList[i]!.2} ∪ {x | ∃ i < firstList.size, firstList[i]!.1 ≤ x ∧ x ≤ firstList[i]!.2} ∩ {x | ∃ i, (i < j ∧ i < secondList.size) ∧ (secondList.extract (OfNat.ofNat 0) j)[i]!.1 ≤ x ∧ x ≤ (secondList.extract (OfNat.ofNat 0) j)[i]!.2}) (if_neg : (if firstList[i]!.2 ≤ secondList[j]!.2 then firstList[i]!.2 else secondList[j]!.2) < if secondList[j]!.1 ≤ firstList[i]!.1 then firstList[i]!.1 else secondList[j]!.1) (if_neg_1 : secondList[j]!.2 ≤ firstList[i]!.2) : {x | ∃ i < out.size, out[i]!.1 ≤ x ∧ x ≤ out[i]!.2} = {x | ∃ i_1, (i_1 < i ∧ i_1 < firstList.size) ∧ (firstList.extract (OfNat.ofNat 0) i)[i_1]!.1 ≤ x ∧ x ≤ (firstList.extract (OfNat.ofNat 0) i)[i_1]!.2} ∩ {x | ∃ i < secondList.size, secondList[i]!.1 ≤ x ∧ x ≤ secondList[i]!.2} ∪ {x | ∃ i < firstList.size, firstList[i]!.1 ≤ x ∧ x ≤ firstList[i]!.2} ∩ {x | ∃ i, (i < j + OfNat.ofNat 1 ∧ i < secondList.size) ∧ (secondList.extract (OfNat.ofNat 0) (j + OfNat.ofNat 1))[i]!.1 ≤ x ∧ x ≤ (secondList.extract (OfNat.ofNat 0) (j + OfNat.ofNat 1))[i]!.2} := by
    ext x; simp_all +decide [ Set.ext_iff ] ;
    constructor <;> intro h <;> rcases h with ( ⟨ ⟨ k, hk₁, hk₂, hk₃ ⟩, ⟨ l, hl₁, hl₂, hl₃ ⟩ ⟩ | ⟨ ⟨ k, hk₁, hk₂, hk₃ ⟩, ⟨ l, hl₁, hl₂, hl₃ ⟩ ⟩ ) <;> simp_all +decide [ Nat.lt_succ_iff ] ;
    · refine Or.inl ⟨ ⟨ k, ⟨ hk₁.1, hk₁.2 ⟩, ?_, ?_ ⟩, l, hl₁, ?_, ?_ ⟩ <;> simp_all +decide [ Array.getElem?_eq_getElem ] ;
    · refine Or.inr ⟨ ⟨ k, hk₁, ?_, ?_ ⟩, ⟨ l, ⟨ by linarith, by linarith ⟩, ?_, ?_ ⟩ ⟩;
      · grind +ring;
      · grind;
      · grind +ring;
      · grind +ring;
    · refine Or.inl ⟨ ⟨ k, hk₁, ?_, ?_ ⟩, ⟨ l, hl₁, ?_, ?_ ⟩ ⟩ <;> simp_all +decide [ Array.getElem_extract ];
    · by_cases h : k < i <;> by_cases h' : l < j <;> simp_all +decide [ Array.getElem_extract ];
      · grind;
      · grind +ring;
      · refine Or.inr ⟨ ⟨ k, hk₁, ?_, ?_ ⟩, ⟨ l, ⟨ h', hl₁.2 ⟩, ?_, ?_ ⟩ ⟩ <;> simp_all +decide [ Array.getElem_extract ];
      · cases h.eq_or_lt <;> cases h'.eq_or_lt <;> first | linarith | simp_all +decide [ Nat.lt_succ_iff ] ;
        · split_ifs at if_neg <;> linarith [ require_1.1 k hk₁, require_1.2.1 l hl₁.2 ] ;
        · grind +ring

/-
PROVIDED SOLUTION
This is the post-loop proof: when the loop terminates (i = firstList.size or j = secondList.size), prove the postcondition. The invariant gives us validity, sortedness, disjointness of out, and the semantic invariant. We need to show that the semantic invariant implies the full postcondition, particularly that unionIntervalSets result = unionIntervalSets firstList ∩ unionIntervalSets secondList.

Key idea: When i = firstList.size, firstList.extract 0 i = firstList, so the left term of the union in the invariant becomes (full firstList) ∩ (full secondList). The right term involves secondList.extract 0 j which is a subset of secondList, so its intersection with firstList is a subset of the left term. Together they give us the full intersection.

Similarly when j = secondList.size, secondList.extract 0 j = secondList, and the right term becomes (full firstList) ∩ (full secondList).

For the postcondition, unfold postcondition, unionIntervalSets, intervalSet, isValidInterval, sortedByStart, pairwiseDisjointClosed. The validity/sorted/disjoint parts come directly from the invariant. The semantic part needs the argument above.

Try: unfold postcondition unionIntervalSets intervalSet isValidInterval sortedByStart pairwiseDisjointClosed, then use the invariant hypotheses directly. For the set equality, use ext and cases on done_1, then simplify.
-/
theorem goal_8 (firstList : Array Interval) (secondList : Array Interval) (require_1 : (∀ i < firstList.size, firstList[i]!.1 ≤ firstList[i]!.2) ∧ (∀ i < secondList.size, secondList[i]!.1 ≤ secondList[i]!.2) ∧ (∀ (i j : ℕ), i < j → j < firstList.size → firstList[i]!.1 ≤ firstList[j]!.1) ∧ (∀ (i j : ℕ), i < j → j < secondList.size → secondList[i]!.1 ≤ secondList[j]!.1) ∧ (∀ (i j : ℕ), i < j → j < firstList.size → firstList[i]!.2 < firstList[j]!.1) ∧ ∀ (i j : ℕ), i < j → j < secondList.size → secondList[i]!.2 < secondList[j]!.1) (i_1 : ℕ) (i_2 : ℕ) (out_1 : Array Interval) (a : i_1 ≤ firstList.size) (a_1 : i_2 ≤ secondList.size) (done_1 : i_1 = firstList.size ∨ i_2 = secondList.size) (invariant_inv_out_valid : ∀ k < out_1.size, out_1[k]!.1 ≤ out_1[k]!.2) (invariant_inv_out_sorted : ∀ (i j : ℕ), i < j → j < out_1.size → out_1[i]!.1 ≤ out_1[j]!.1) (invariant_inv_out_disjoint : ∀ (i j : ℕ), i < j → j < out_1.size → out_1[i]!.2 < out_1[j]!.1) (invariant_inv_semantic : {x | ∃ i < out_1.size, out_1[i]!.1 ≤ x ∧ x ≤ out_1[i]!.2} = {x | ∃ i, (i < i_1 ∧ i < firstList.size) ∧ (firstList.extract (OfNat.ofNat 0) i_1)[i]!.1 ≤ x ∧ x ≤ (firstList.extract (OfNat.ofNat 0) i_1)[i]!.2} ∩ {x | ∃ i < secondList.size, secondList[i]!.1 ≤ x ∧ x ≤ secondList[i]!.2} ∪ {x | ∃ i < firstList.size, firstList[i]!.1 ≤ x ∧ x ≤ firstList[i]!.2} ∩ {x | ∃ i, (i < i_2 ∧ i < secondList.size) ∧ (secondList.extract (OfNat.ofNat 0) i_2)[i]!.1 ≤ x ∧ x ≤ (secondList.extract (OfNat.ofNat 0) i_2)[i]!.2}) : postcondition firstList secondList out_1 := by
    refine' ⟨ invariant_inv_out_valid, invariant_inv_out_sorted, invariant_inv_out_disjoint, _ ⟩;
    convert invariant_inv_semantic using 1;
    cases done_1 <;> simp_all +decide [ unionIntervalSets ];
    · ext x; simp [intervalSet];
      intro i hi₁ hi₂ hi₃ j hj₁ hj₂ hj₃ hj₄; use ⟨ i, hi₁, hi₂, hi₃ ⟩ ; use j; aesop;
    · unfold intervalSet; ext; aesop;

end Proof