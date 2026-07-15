import Lean

import Mathlib.Tactic

set_option maxHeartbeats 10000000

section Specs
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

section Impl
def implementation (firstList : Array Interval) (secondList : Array Interval) : Array Interval :=
  let rec go (i j : Nat) (acc : Array Interval) : Array Interval :=
    if i < firstList.size then
      if j < secondList.size then
        let a := firstList[i]!
        let b := secondList[j]!
        let s : Int := max a.1 b.1
        let e : Int := min a.2 b.2
        let acc := if s ≤ e then acc.push (s, e) else acc
        if a.2 < b.2 then
          go (i + 1) j acc
        else if b.2 < a.2 then
          go i (j + 1) acc
        else
          go (i + 1) (j + 1) acc
      else
        acc
    else
      acc
  go 0 0 #[]
end Impl

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

section Helpers

/-
PROBLEM
The intersection of two closed intervals is the closed interval [max starts, min ends]

PROVIDED SOLUTION
Unfold intervalSet to Set.Icc. Then use ext and simp with max_le_iff and le_min_iff to show the equivalence: max a.1 b.1 ≤ x ∧ x ≤ min a.2 b.2 ↔ a.1 ≤ x ∧ x ≤ a.2 ∧ b.1 ≤ x ∧ x ≤ b.2.
-/
lemma intervalSet_inter (a b : Interval) :
    intervalSet (max a.1 b.1, min a.2 b.2) = intervalSet a ∩ intervalSet b := by
  unfold intervalSet; ext; aesop;

/-
PROBLEM
Union of interval sets after pushing one more interval

PROVIDED SOLUTION
Unfold unionIntervalSets. Use ext. The key is that (acc.push iv)[k]! for k < acc.size equals acc[k]!, and (acc.push iv)[acc.size]! = iv. Also (acc.push iv).size = acc.size + 1. An element x is in the LHS iff there exists k < acc.size + 1 with x in intervalSet of (acc.push iv)[k]!. Split k < acc.size (in unionIntervalSets acc) or k = acc.size (in intervalSet iv).
-/
lemma unionIntervalSets_push (acc : Array Interval) (iv : Interval) :
    unionIntervalSets (acc.push iv) = unionIntervalSets acc ∪ intervalSet iv := by
  unfold unionIntervalSets;
  ext x; simp [intervalSet];
  constructor;
  · rintro ⟨ i, hi, hi' ⟩ ; cases lt_or_eq_of_le hi <;> simp_all +decide [ Array.push ] ; aesop;
  · rintro ( ⟨ i, hi, hi' ⟩ | hi );
    · use i;
      grind;
    · use acc.size; aesop;

/-
PROBLEM
Pushing an interval that starts after all previous intervals end preserves pairwise disjointness

PROVIDED SOLUTION
Unfold pairwiseDisjointClosed. We need to show for all i < j < (acc.push iv).size, (acc.push iv)[i]!.2 < (acc.push iv)[j]!.1. Note (acc.push iv).size = acc.size + 1.
Case j < acc.size: both i, j index into acc, so use h_pd.
Case j = acc.size: (acc.push iv)[j]! = iv, and i < acc.size, so (acc.push iv)[i]! = acc[i]!. Need acc[i]!.2 < iv.1.
If acc.size = 0 then i < 0 is impossible. Otherwise acc.size > 0.
By h_bound, acc[acc.size-1]!.2 < iv.1. If i = acc.size - 1, done. If i < acc.size - 1, then by h_pd (since i < acc.size-1 < acc.size), acc[i]!.2 < acc[i+1]!.1. By h_valid, acc[i+1]!.1 ≤ acc[i+1]!.2 (isValidInterval). Chaining through the pairwise disjointness and validity: acc[i]!.2 < acc[i+1]!.1 ≤ acc[i+1]!.2 < ... < acc[acc.size-1]!.2 < iv.1.
Use Array.getElem!_push and Array.size_push.
-/
lemma pairwiseDisjointClosed_push (acc : Array Interval) (iv : Interval)
    (h_pd : pairwiseDisjointClosed acc)
    (h_valid : ∀ k, k < acc.size → isValidInterval acc[k]!)
    (h_bound : acc.size > 0 → acc[acc.size - 1]!.2 < iv.1) :
    pairwiseDisjointClosed (acc.push iv) := by
  intro i j hij;
  by_cases hj : j < acc.size;
  · convert h_pd i j hij hj using 1;
    grind;
  · cases eq_or_lt_of_le ( Nat.le_of_not_lt hj ) <;> simp_all +decide [ Array.getElem_push ];
    have := h_bound ( pos_of_gt hij ) ; rcases j with ( _ | _ | j ) <;> simp_all +decide [ Array.push ] ;
    · grind;
    · aesop;
    · cases lt_or_eq_of_le ( Nat.le_of_lt_succ hij ) <;> simp_all +decide [ List.getElem?_append ];
      refine' lt_of_le_of_lt _ h_bound;
      have h_disjoint : ∀ k l : ℕ, k < l → l < acc.size → acc[k]!.2 < acc[l]!.1 := by
        exact?;
      have h_disjoint : acc[i]!.2 < acc[j + 1]!.1 := by
        exact h_disjoint _ _ ( by linarith ) ( by linarith );
      refine' le_trans _ ( h_valid _ ( by linarith ) );
      grind

/-
PROBLEM
Pairwise disjointness (with valid intervals) implies sorted by start

PROVIDED SOLUTION
Unfold sortedByStart and pairwiseDisjointClosed. For i < j < a.size, by h_pd we have a[i]!.2 < a[j]!.1. By h_valid applied to i (need i < a.size, which follows from i < j < a.size), we have a[i]!.1 ≤ a[i]!.2 (isValidInterval). So a[i]!.1 ≤ a[i]!.2 < a[j]!.1, giving a[i]!.1 ≤ a[j]!.1 (via le_of_lt of the composed inequality, or omega/linarith).
-/
lemma pd_implies_sorted (a : Array Interval)
    (h_valid : ∀ k, k < a.size → isValidInterval a[k]!)
    (h_pd : pairwiseDisjointClosed a) :
    sortedByStart a := by
  -- By definition of pairwiseDisjointClosed, if $i < j$ and $j < a.size$, then $a[i]!.2 < a[j]!.1$.
  intros i j hij hlt
  have h_disjoint : a[i]!.2 < a[j]!.1 := h_pd i j hij hlt
  have h_valid_i : a[i]!.1 ≤ a[i]!.2 := h_valid i (by linarith)
  have h_valid_j : a[j]!.1 ≤ a[j]!.2 := h_valid j (by linarith)
  linarith

end Helpers

section MainProof

/-
PROBLEM
The set-theoretic correctness invariant for go:
The union of interval sets in the output of go equals
the union of interval sets in the accumulator, plus all pairwise intersections
of intervals from fl[i..] and sl[j..].

PROVIDED SOLUTION
Prove by strong induction on `fl.size - i + (sl.size - j)` (natural number), generalizing over i, j, and acc.

Use `implementation.go.eq_def` to unfold the function definition.

Base cases: When i ≥ fl.size or j ≥ sl.size, go returns acc. The set {x | ∃ i' j', i ≤ i' ∧ j ≤ j' ∧ i' < fl.size ∧ j' < sl.size ∧ ...} is empty (since no valid i' or j' exists), so the result is unionIntervalSets acc ∪ ∅ = unionIntervalSets acc.

Inductive case: i < fl.size and j < sl.size. Let a = fl[i]!, b = sl[j]!, s = max a.1 b.1, e = min a.2 b.2.

The key set-theoretic identity: for any i' ≥ i, j' ≥ j, intervalSet fl[i']! ∩ intervalSet sl[j']! is the same as intervalSet (max fl[i']!.1 sl[j']!.1, min fl[i']!.2 sl[j']!.2), by intervalSet_inter.

Sub-case s ≤ e AND a.2 < b.2 (advance i): go returns go(i+1, j, acc.push(s,e)). By IH (fuel decreases since i increases):
  unionIntervalSets(go(i+1,j, acc.push(s,e))) = unionIntervalSets(acc.push(s,e)) ∪ {x | ∃ i'≥i+1, j'≥j, ...}
  = unionIntervalSets(acc) ∪ intervalSet(s,e) ∪ {x | ∃ i'≥i+1, j'≥j, ...}  (by unionIntervalSets_push)

Need to show: intervalSet(s,e) ∪ {x | ∃ i'≥i+1, j'≥j, ...} = {x | ∃ i'≥i, j'≥j, ...}.
- intervalSet(s,e) = intervalSet fl[i]! ∩ intervalSet sl[j]! = {x | i'=i, j'=j, ...}
- {x | ∃ i'≥i+1, j'≥j, ...} covers all pairs with i'>i.
- Missing: pairs (i, j') with j'>j. But fl[i]!.2 = a.2 < b.2 = sl[j]!.2, and by pairwiseDisjointClosed sl, sl[j]!.2 < sl[j']!.1 for j'>j. So fl[i]!.2 < sl[j']!.1, meaning intervalSet fl[i]! ∩ intervalSet sl[j']! = ∅. These pairs contribute nothing.

Sub-case s ≤ e AND b.2 < a.2 (advance j): Symmetric. go returns go(i, j+1, acc.push(s,e)). Missing pairs are (i', j) with i'>i, which are empty because sl[j]!.2 < fl[i]!.2 < fl[i']!.1.

Sub-case s ≤ e AND a.2 = b.2 (advance both): go returns go(i+1, j+1, acc.push(s,e)). Missing pairs: (i, j') with j'>j (empty because fl[i]!.2 = sl[j]!.2 < sl[j']!.1) and (i', j) with i'>i (empty because fl[i']!.1 > fl[i]!.2 = sl[j]!.2).

Sub-case s > e (no push): Similar analysis but intervalSet(s,e) = ∅ (since s > e means Icc is empty). go returns go(next_i, next_j, acc). The current pair contributes ∅, and skipped pairs also contribute ∅ by the same disjointness arguments.

For the skipping arguments, use: if fl[i]!.2 ≤ sl[j]!.2 and j < j' < sl.size, then pairwiseDisjointClosed sl gives sl[j]!.2 < sl[j']!.1, so fl[i]!.2 < sl[j']!.1, making the intersection empty. Similarly for the other direction.
-/
lemma go_union_eq (fl sl : Array Interval) (h_pre : precondition fl sl)
    (i j : Nat) (acc : Array Interval) :
    unionIntervalSets (implementation.go fl sl i j acc) =
    unionIntervalSets acc ∪ {x | ∃ i' j', i ≤ i' ∧ j ≤ j' ∧ i' < fl.size ∧ j' < sl.size ∧
      x ∈ intervalSet fl[i']! ∧ x ∈ intervalSet sl[j']!} := by
  apply Set.ext;
  intro x;
  induction' h : fl.size - i + ( sl.size - j ) using Nat.strong_induction_on with k ih generalizing i j acc x;
  by_cases hi : i < fl.size <;> by_cases hj : j < sl.size <;> simp_all +decide [ unionIntervalSets ];
  · unfold implementation.go;
    split_ifs;
    by_cases h_case : fl[i]!.2 < sl[j]!.2;
    · specialize ih ( fl.size - ( i + 1 ) + ( sl.size - j ) ) ( by omega ) ( i + 1 ) j ( if max fl[i]!.1 sl[j]!.1 ≤ min fl[i]!.2 sl[j]!.2 then acc.push ( max fl[i]!.1 sl[j]!.1, min fl[i]!.2 sl[j]!.2 ) else acc ) x ; simp_all +decide;
      constructor;
      · rintro ( ⟨ k, hk₁, hk₂ ⟩ | ⟨ i', hi', j', hj', hi'', hj'', hk₃, hk₄ ⟩ );
        · split_ifs at hk₁ hk₂ <;> simp_all +decide [ Array.getElem_push ];
          · split_ifs at hk₂ <;> simp_all +decide [ intervalSet ];
            · exact Or.inl ⟨ k, by linarith, by simp [ Array.getElem?_eq_getElem, * ] ⟩;
            · exact Or.inr ⟨ i, le_rfl, j, le_rfl, hi, hj, by aesop ⟩;
          · exact Or.inl ⟨ k, hk₁, by simpa [ Array.getElem?_eq_getElem, hk₁ ] using hk₂ ⟩;
        · exact Or.inr ⟨ i', by linarith, j', by linarith, by linarith, by linarith, hk₃, hk₄ ⟩;
      · rintro ( ⟨ i, hi, hx ⟩ | ⟨ i', hi', j', hj', hi'', hj'', hx ⟩ );
        · split_ifs <;> simp_all +decide [ Array.getElem_push ];
          · refine Or.inl ⟨ i, by linarith, ?_ ⟩;
            grind;
          · exact Or.inl ⟨ i, hi, by simpa [ show acc[i]! = acc[i] from by exact? ] using hx ⟩;
        · by_cases hi''' : i' = i;
          · by_cases hj''' : j' = j;
            · split_ifs <;> simp_all +decide [ intervalSet ];
              · refine' Or.inl ⟨ acc.size, _, _, _ ⟩ <;> simp_all +decide [ Array.push ];
              · linarith [ ‹fl[i].1 ≤ fl[i].2 → sl[j].1 ≤ fl[i].2 → fl[i].1 ≤ sl[j].2 → sl[j].2 < sl[j].1› ( by linarith ) ( by linarith ) ( by linarith ) ];
            · have h_disjoint : ∀ j' : ℕ, j < j' → j' < sl.size → sl[j]!.2 < sl[j']!.1 := by
                exact fun j' hj' hj'' => h_pre.2.2.2.2.2 j j' hj' hj'';
              simp_all +decide [ intervalSet ];
              linarith [ h_disjoint j' ( lt_of_le_of_ne hj' ( Ne.symm hj''' ) ) hj'' ];
          · exact Or.inr ⟨ i', lt_of_le_of_ne hi' ( Ne.symm hi''' ), j', hj', hi'', hj'', hx ⟩;
    · by_cases h_case2 : sl[j]!.2 < fl[i]!.2;
      · convert ih ( fl.size - i + ( sl.size - ( j + 1 ) ) ) ( by omega ) i ( j + 1 ) ( if max fl[i]!.1 sl[j]!.1 ≤ min fl[i]!.2 sl[j]!.2 then acc.push ( max fl[i]!.1 sl[j]!.1, min fl[i]!.2 sl[j]!.2 ) else acc ) x rfl using 1;
        · simp +decide [ h_case, h_case2 ];
        · constructor;
          · rintro ( ⟨ i, hi, hx ⟩ | ⟨ i', hi', j', hj', hi'', hj'', hx ⟩ );
            · split_ifs <;> simp_all +decide [ Array.getElem_push ];
              · refine Or.inl ⟨ i, by linarith, ?_ ⟩;
                grind;
              · exact Or.inl ⟨ i, hi, by simpa [ Array.getElem?_eq_getElem, hi ] using hx ⟩;
            · by_cases h_case3 : j' = j;
              · split_ifs <;> simp_all +decide [ intervalSet ];
                · refine Or.inl ⟨ acc.size, le_rfl, ?_, ?_ ⟩ <;> simp +decide [ *, Array.push ];
                  linarith [ show fl[i].1 ≤ fl[i'].1 from by
                              have := h_pre.2.2.1 i i';
                              cases lt_or_eq_of_le hi' <;> aesop ];
                · contrapose! h_case2;
                  have := h_pre.2.2.1 i i';
                  grind;
              · exact Or.inr ⟨ i', hi', j', Nat.lt_of_le_of_ne hj' ( Ne.symm h_case3 ), hi'', hj'', hx ⟩;
          · rintro ( ⟨ k, hk₁, hk₂ ⟩ | ⟨ i', hi', j', hj', hi'', hj'', hx₁, hx₂ ⟩ );
            · split_ifs at hk₁ hk₂ <;> simp_all +decide [ Array.getElem_push ];
              · split_ifs at hk₂ <;> simp_all +decide [ intervalSet ];
                · exact Or.inl ⟨ k, by linarith, by simpa [ show acc[k]! = acc[k] from by exact? ] using hk₂ ⟩;
                · exact Or.inr ⟨ i, le_rfl, j, le_rfl, hi, hj, ⟨ by simpa [ hi ] using hk₂.1.1, by simpa [ hi ] using hk₂.2.trans h_case ⟩, by simpa [ hj ] using hk₂.1.2, by simpa [ hj ] using hk₂.2 ⟩;
              · exact Or.inl ⟨ k, hk₁, by simpa [ Array.getElem?_eq_getElem, hk₁ ] using hk₂ ⟩;
            · exact Or.inr ⟨ i', hi', j', by linarith, hi'', hj'', hx₁, hx₂ ⟩;
      · convert ih ( fl.size - ( i + 1 ) + ( sl.size - ( j + 1 ) ) ) _ ( i + 1 ) ( j + 1 ) ( if max fl[i]!.1 sl[j]!.1 ≤ min fl[i]!.2 sl[j]!.2 then acc.push ( max fl[i]!.1 sl[j]!.1, min fl[i]!.2 sl[j]!.2 ) else acc ) x _ using 1;
        · grind;
        · constructor <;> intro h;
          · rcases h with ( ⟨ i, hi, hx ⟩ | ⟨ i', hi', j', hj', hi'', hj'', hx ⟩ );
            · split_ifs <;> simp_all +decide [ Array.getElem_push ];
              · refine Or.inl ⟨ i, by linarith, ?_ ⟩;
                grind;
              · exact Or.inl ⟨ i, hi, by simpa [ show acc[i]! = acc[i] from by exact? ] using hx ⟩;
            · by_cases hi''' : i' = i;
              · by_cases hj''' : j' = j;
                · split_ifs <;> simp_all +decide [ intervalSet ];
                  · refine' Or.inl ⟨ acc.size, _, _, _ ⟩ <;> simp +decide [ *, Array.push ];
                  · linarith [ ‹fl[i].1 ≤ fl[i].2 → fl[i].2 < sl[j].1› ( by linarith ) ];
                · have := h_pre.2.2.2.2.2 j j' ( lt_of_le_of_ne hj' ( Ne.symm hj''' ) ) hj''; simp_all +decide [ intervalSet ] ;
                  linarith;
              · by_cases hj''' : j' = j;
                · have := h_pre.2.2.2.2.1 i i' ( lt_of_le_of_ne hi' ( Ne.symm hi''' ) ) hi''; simp_all +decide [ intervalSet ] ;
                  linarith;
                · exact Or.inr ⟨ i', Nat.succ_le_of_lt ( lt_of_le_of_ne hi' ( Ne.symm hi''' ) ), j', Nat.succ_le_of_lt ( lt_of_le_of_ne hj' ( Ne.symm hj''' ) ), hi'', hj'', hx ⟩;
          · rcases h with ( ⟨ k, hk₁, hk₂ ⟩ | ⟨ k, hk₁, l, hl₁, hk₂, hl₂, hk₃, hl₃ ⟩ );
            · split_ifs at hk₁ hk₂ <;> simp_all +decide [ Array.getElem_push ];
              · split_ifs at hk₂ <;> simp_all +decide [ intervalSet ];
                · exact Or.inl ⟨ k, by linarith, by simpa [ show acc[k]! = acc[k] from by exact? ] using hk₂ ⟩;
                · exact Or.inr ⟨ i, le_rfl, j, le_rfl, hi, hj, ⟨ by simpa [ show fl[i]! = fl[i] from by exact? ] using hk₂.1.1, by simpa [ show fl[i]! = fl[i] from by exact? ] using hk₂.2 ⟩, by simpa [ show sl[j]! = sl[j] from by exact? ] using hk₂.1.2, by simpa [ show sl[j]! = sl[j] from by exact? ] using by linarith ⟩;
              · exact Or.inl ⟨ k, hk₁, by simpa [ Array.getElem?_eq_getElem, hk₁ ] using hk₂ ⟩;
            · exact Or.inr ⟨ k, by linarith, l, by linarith, hk₂, hl₂, hk₃, hl₃ ⟩;
        · omega;
        · rfl;
  · rw [ show implementation.go fl sl i j acc = acc from _ ];
    · grind;
    · unfold implementation.go; aesop;
  · rw [ show implementation.go fl sl i j acc = acc from _ ];
    · grind;
    · unfold implementation.go; aesop;
  · unfold implementation.go;
    grind

/-
PROBLEM
The structural invariant for go:
If the accumulator is already valid and pairwise disjoint,
and the last element of the accumulator ends before the start of any future intersection,
then the output of go is also valid and pairwise disjoint.

PROVIDED SOLUTION
Prove by strong induction on `fl.size - i + (sl.size - j)` (natural number), generalizing over i, j, and acc.

Use `implementation.go.eq_def` to unfold the function definition.

Base cases: When i ≥ fl.size or j ≥ sl.size, go returns acc. The result follows from h_acc_valid and h_acc_pd.

Inductive case: i < fl.size and j < sl.size. Let a = fl[i]!, b = sl[j]!, s = max a.1 b.1, e = min a.2 b.2.

Case s ≤ e (push): New acc' = acc.push(s, e).
- acc' is valid: old elements valid by h_acc_valid; new element (s,e) has s ≤ e so isValidInterval.
- acc' is pd: use pairwiseDisjointClosed_push. Need acc[acc.size-1]!.2 < s = max(a.1, b.1). This follows from h_acc_bound.
- New bound: acc'[acc'.size-1]!.2 = e = min(a.2, b.2).
  If advancing i (a.2 < b.2): e = a.2. Need a.2 < max fl[i+1]!.1 sl[j]!.1. By pairwiseDisjointClosed fl: a.2 = fl[i]!.2 < fl[i+1]!.1. So a.2 < fl[i+1]!.1 ≤ max(fl[i+1]!.1, sl[j]!.1).
  If advancing j (b.2 < a.2): e = b.2. Need b.2 < max fl[i]!.1 sl[j+1]!.1. By pairwiseDisjointClosed sl: b.2 = sl[j]!.2 < sl[j+1]!.1 ≤ max(fl[i]!.1, sl[j+1]!.1).
  If advancing both (a.2 = b.2): e = a.2. Need a.2 < max fl[i+1]!.1 sl[j+1]!.1. fl[i]!.2 < fl[i+1]!.1 ≤ max(...).
- Apply IH (fuel decreases since at least one pointer advances).

Case s > e (no push): acc unchanged.
- acc is still valid and pd (given).
- Bound carries forward: max(fl[next_i]!.1, sl[next_j]!.1) ≥ max(fl[i]!.1, sl[j]!.1) (by sortedByStart, since next_i ≥ i and next_j ≥ j). So h_acc_bound still holds.
- Apply IH.
-/
lemma go_structural (fl sl : Array Interval) (h_pre : precondition fl sl)
    (i j : Nat) (acc : Array Interval)
    (h_acc_valid : ∀ k, k < acc.size → isValidInterval acc[k]!)
    (h_acc_pd : pairwiseDisjointClosed acc)
    (h_acc_bound : acc.size > 0 → i < fl.size → j < sl.size →
      acc[acc.size - 1]!.2 < max fl[i]!.1 sl[j]!.1) :
    (∀ k, k < (implementation.go fl sl i j acc).size →
      isValidInterval (implementation.go fl sl i j acc)[k]!) ∧
    pairwiseDisjointClosed (implementation.go fl sl i j acc) := by
  induction' n : ( fl.size - i ) + ( sl.size - j ) using Nat.strong_induction_on with n ih generalizing i j acc;
  by_cases hi : i < fl.size <;> by_cases hj : j < sl.size;
  · -- Consider the two cases: when the intersection is non-empty and when it is empty.
    by_cases h_inter : max fl[i]!.1 sl[j]!.1 ≤ min fl[i]!.2 sl[j]!.2;
    · by_cases h_case : fl[i]!.2 < sl[j]!.2;
      · -- In this case, we push the interval (max fl[i]!.1 sl[j]!.1, min fl[i]!.2 sl[j]!.2) into the accumulator and advance i.
        have h_push : implementation.go fl sl i j acc = implementation.go fl sl (i + 1) j (acc.push (max fl[i]!.1 sl[j]!.1, min fl[i]!.2 sl[j]!.2)) := by
          rw [implementation.go];
          aesop;
        convert ih ( fl.size - ( i + 1 ) + ( sl.size - j ) ) _ ( i + 1 ) j ( acc.push ( max fl[i]!.1 sl[j]!.1, min fl[i]!.2 sl[j]!.2 ) ) _ _ _ rfl using 1;
        any_goals rw [ h_push ];
        · omega;
        · intro k hk; by_cases hk' : k < acc.size <;> simp_all +decide [ Array.getElem_push ] ;
          split_ifs <;> simp_all +decide [ isValidInterval ];
        · apply pairwiseDisjointClosed_push;
          · assumption;
          · assumption;
          · exact fun h => h_acc_bound h hi hj;
        · intro h₁ h₂ h₃; simp_all +decide [ Array.getElem_push ] ;
          have := h_pre.2.2.2.2.1 i ( i + 1 ) ; aesop;
      · by_cases h_case : sl[j]!.2 < fl[i]!.2;
        · -- Apply the induction hypothesis to the new parameters.
          have h_ind : (∀ k < (implementation.go fl sl i (j + 1) (acc.push (max fl[i]!.1 sl[j]!.1, min fl[i]!.2 sl[j]!.2))).size, isValidInterval (implementation.go fl sl i (j + 1) (acc.push (max fl[i]!.1 sl[j]!.1, min fl[i]!.2 sl[j]!.2)))[k]!) ∧ pairwiseDisjointClosed (implementation.go fl sl i (j + 1) (acc.push (max fl[i]!.1 sl[j]!.1, min fl[i]!.2 sl[j]!.2))) := by
            apply ih (fl.size - i + (sl.size - (j + 1)));
            · omega;
            · intro k hk; by_cases hk' : k < acc.size <;> simp_all +decide [ Array.getElem_push ] ;
              split_ifs <;> simp_all +decide [ isValidInterval ];
            · exact?;
            · intro h₁ h₂ h₃; simp_all +decide [ Array.push ] ;
              have := h_pre.2.2.2.2.2 j ( j + 1 ) ; aesop;
            · rfl;
          rw [ show implementation.go fl sl i j acc = implementation.go fl sl i ( j + 1 ) ( acc.push ( max fl[i]!.1 sl[j]!.1, min fl[i]!.2 sl[j]!.2 ) ) from ?_ ];
          · exact h_ind;
          · rw [implementation.go];
            grind;
        · -- Since fl[i]!.2 = sl[j]!.2, we can advance both i and j.
          have h_advance : (implementation.go fl sl i j acc) = (implementation.go fl sl (i + 1) (j + 1) (acc.push (max fl[i]!.1 sl[j]!.1, min fl[i]!.2 sl[j]!.2))) := by
            rw [implementation.go];
            grind;
          specialize ih ( fl.size - ( i + 1 ) + ( sl.size - ( j + 1 ) ) ) ( by omega ) ( i + 1 ) ( j + 1 ) ( acc.push ( max fl[i]!.1 sl[j]!.1, min fl[i]!.2 sl[j]!.2 ) ) ; simp_all +decide;
          apply ih;
          · intro k hk; by_cases hk' : k < acc.size <;> simp_all +decide [ Array.getElem_push ] ;
            split_ifs <;> simp_all +decide [ isValidInterval ];
          · apply pairwiseDisjointClosed_push;
            · assumption;
            · aesop;
            · cases acc ; aesop;
          · intro hi hj; have := h_pre.2.2.2.2.1 i ( i + 1 ) ; have := h_pre.2.2.2.2.2 j ( j + 1 ) ; aesop;
    · unfold implementation.go; simp +decide [ hi, hj, h_inter ] ;
      split_ifs;
      grind;
      · convert ih ( fl.size - ( i + 1 ) + ( sl.size - j ) ) _ ( i + 1 ) j acc h_acc_valid h_acc_pd _ _ using 1;
        · omega;
        · intro h₁ h₂ h₃; exact lt_of_lt_of_le ( h_acc_bound h₁ hi hj ) ( by
            exact max_le_max ( h_pre.2.2.1 _ _ ( Nat.lt_succ_self _ ) ( by linarith ) ) le_rfl ) ;
        · rfl;
      · grind;
      · convert ih ( fl.size - i + ( sl.size - ( j + 1 ) ) ) _ i ( j + 1 ) acc h_acc_valid h_acc_pd _ _ using 1;
        · omega;
        · intro h₁ h₂ h₃;
          refine' lt_of_lt_of_le ( h_acc_bound h₁ h₂ hj ) _;
          exact max_le_max_left _ ( h_pre.2.2.2.1 _ _ ( by linarith ) ( by linarith ) );
        · rfl;
      · grind;
      · convert ih _ _ _ _ _ h_acc_valid h_acc_pd _ rfl using 1;
        · omega;
        · intro h₁ h₂ h₃; exact lt_of_lt_of_le ( h_acc_bound h₁ hi hj ) ( by
            exact max_le_max ( h_pre.2.2.1 _ _ ( by linarith ) ( by linarith ) ) ( h_pre.2.2.2.1 _ _ ( by linarith ) ( by linarith ) ) ) ;
  · unfold implementation.go;
    grind;
  · -- Since $i \geq fl.size$, the go function returns the accumulator acc.
    have h_go_acc : implementation.go fl sl i j acc = acc := by
      unfold implementation.go; aesop;
    aesop;
  · -- Since $i \geq fl.size$ and $j \geq sl.size$, the go function returns the accumulator `acc`.
    have h_go_eq_acc : implementation.go fl sl i j acc = acc := by
      unfold implementation.go; aesop;
    aesop

theorem correctness_goal (firstList : Array Interval) (secondList : Array Interval) (h_precond : precondition firstList secondList) : postcondition firstList secondList (implementation firstList secondList) := by
  have result_eq : implementation firstList secondList =
      implementation.go firstList secondList 0 0 #[] := rfl
  have h_struct := go_structural firstList secondList h_precond 0 0 #[]
    (by intro k hk; simp [Array.size] at hk)
    (by intro i j hij hj; simp [Array.size] at hj)
    (by intro h; simp [Array.size] at h)
  have h_union := go_union_eq firstList secondList h_precond 0 0 #[]
  rw [result_eq]
  refine ⟨h_struct.1, pd_implies_sorted _ h_struct.1 h_struct.2, h_struct.2, ?_⟩
  rw [h_union]
  ext x
  simp only [Set.mem_union, unionIntervalSets, Set.mem_setOf_eq, Set.mem_inter_iff]
  constructor
  · rintro (⟨i, hi, hxi⟩ | ⟨i', j', _, _, hi', hj', hx1, hx2⟩)
    · exact absurd hi (by simp [Array.size])
    · exact ⟨⟨i', hi', hx1⟩, ⟨j', hj', hx2⟩⟩
  · rintro ⟨⟨i', hi', hx1⟩, ⟨j', hj', hx2⟩⟩
    right
    exact ⟨i', j', Nat.zero_le _, Nat.zero_le _, hi', hj', hx1, hx2⟩

end MainProof