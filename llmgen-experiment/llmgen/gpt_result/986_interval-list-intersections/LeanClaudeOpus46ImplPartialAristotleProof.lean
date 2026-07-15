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
def helper (a : Array Interval) (b : Array Interval) (i : Nat) (j : Nat) (acc : Array Interval) : Array Interval :=
  if hi : i < a.size then
    if hj : j < b.size then
      let ai := a[i]
      let bj := b[j]
      let lo := max ai.1 bj.1
      let hi' := min ai.2 bj.2
      let acc' := if lo ≤ hi' then acc.push (lo, hi') else acc
      if ai.2 ≤ bj.2 then
        helper a b (i + 1) j acc'
      else
        helper a b i (j + 1) acc'
    else acc
  else acc
termination_by a.size - i + b.size - j

def implementation (firstList : Array Interval) (secondList : Array Interval) : Array Interval :=
  helper firstList secondList 0 0 #[]
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

section Proof

/-
PROBLEM
Helper: accumulator is always a prefix of the output

PROVIDED SOLUTION
By well-founded induction on (a.size - i + b.size - j), matching the termination of helper. Unfold helper. Case 1: i ≥ a.size. Then helper returns acc, so result is acc[k]! = acc[k]!. Case 2: i < a.size but j ≥ b.size. Same. Case 3: i < a.size and j < b.size. Then helper recurses with either (i+1, j, acc') or (i, j+1, acc') where acc' is either acc.push (...) or acc. In either case, k < acc.size implies k < acc'.size (since acc'.size ≥ acc.size), so by IH, (helper a b _ _ acc')[k]! = acc'[k]!. And acc'[k]! = acc[k]! because k < acc.size and acc' is either acc or acc.push(...)  (push doesn't change existing elements).
-/
private lemma helper_acc_prefix (a b : Array Interval) (i j : Nat) (acc : Array Interval)
    (k : Nat) (hk : k < acc.size) :
    (helper a b i j acc)[k]! = acc[k]! := by
  induction' n : a.size - i + b.size - j using Nat.strong_induction_on with n ih generalizing i j acc k;
  unfold helper;
  grind

/-
PROBLEM
Helper: if x is in unionIntervalSets acc, then x is in unionIntervalSets (helper a b i j acc)

PROVIDED SOLUTION
x ∈ unionIntervalSets acc means ∃ k < acc.size, x ∈ intervalSet acc[k]!. We need ∃ k < (helper a b i j acc).size, x ∈ intervalSet (helper a b i j acc)[k]!. Take the same k. By helper_size_ge, k < acc.size ≤ (helper ...).size. By helper_acc_prefix, (helper ...)[k]! = acc[k]!. So x ∈ intervalSet (helper ...)[k]!.

x ∈ unionIntervalSets acc means ∃ k < acc.size, x ∈ intervalSet acc[k]!. We need ∃ k < (helper a b i j acc).size, x ∈ intervalSet (helper a b i j acc)[k]!. Take the same k. By helper_size_ge, k < acc.size ≤ (helper ...).size. By helper_acc_prefix, (helper ...)[k]! = acc[k]!. So x ∈ intervalSet (helper ...)[k]!.
-/
private lemma helper_acc_subset (a b : Array Interval) (i j : Nat) (acc : Array Interval)
    (x : Int) (hx : x ∈ unionIntervalSets acc) :
    x ∈ unionIntervalSets (helper a b i j acc) := by
  obtain ⟨ k, hk₁, hk₂ ⟩ := hx;
  have h_k_size : k < (helper a b i j acc).size := by
    by_contra h_contra;
    apply h_contra;
    clear hk₂ h_contra;
    induction' n : a.size - i + b.size - j using Nat.strong_induction_on with n ih generalizing i j acc;
    unfold helper;
    grind;
  exact ⟨ k, h_k_size, by simpa [ helper_acc_prefix a b i j acc k hk₁ ] using hk₂ ⟩

/-
PROBLEM
Helper: acc.size ≤ (helper a b i j acc).size

PROVIDED SOLUTION
By well-founded induction on (a.size - i + b.size - j). Unfold helper. If i ≥ a.size or j ≥ b.size, helper returns acc, so acc.size ≤ acc.size. Otherwise, helper recurses with acc' where acc'.size ≥ acc.size (it's either acc or acc.push(...)). By IH, acc'.size ≤ (helper a b _ _ acc').size. And acc.size ≤ acc'.size. So acc.size ≤ result.size.
-/
private lemma helper_size_ge (a b : Array Interval) (i j : Nat) (acc : Array Interval) :
    acc.size ≤ (helper a b i j acc).size := by
  induction' h : a.size - i + b.size - j using Nat.strong_induction_on with k ih generalizing a i b j acc;
  unfold helper;
  grind

/-
PROBLEM
Forward direction: every element in the output of helper comes from acc or from
the intersection of some pair of input intervals

PROVIDED SOLUTION
By well-founded induction on (a.size - i + b.size - j), matching helper's termination.

Unfold helper.

Case 1: i ≥ a.size. Then helper returns acc, so x ∈ unionIntervalSets acc. Left disjunct.

Case 2: j ≥ b.size. Same.

Case 3: i < a.size and j < b.size. Let ai = a[i], bj = b[j], lo = max ai.1 bj.1, hi' = min ai.2 bj.2. Let acc' = if lo ≤ hi' then acc.push (lo, hi') else acc.

The result is helper a b (i+1) j acc' or helper a b i (j+1) acc', depending on ai.2 ≤ bj.2.

By IH, x ∈ unionIntervalSets acc' ∨ (x ∈ unionIntervalSets a ∧ x ∈ unionIntervalSets b).

If x ∈ unionIntervalSets a ∧ x ∈ unionIntervalSets b, we're done (right disjunct).

If x ∈ unionIntervalSets acc', then either:
- acc' = acc (lo > hi'), so x ∈ unionIntervalSets acc. Left disjunct.
- acc' = acc.push (lo, hi'). Then x ∈ unionIntervalSets acc (if in original part) giving left disjunct, or x ∈ intervalSet (lo, hi') = intervalSet (max ai.1 bj.1, min ai.2 bj.2). In this case, ai.1 ≤ x (since max ai.1 bj.1 ≤ x), x ≤ ai.2 (since x ≤ min ai.2 bj.2 ≤ ai.2), and bj.1 ≤ x, x ≤ bj.2. So x ∈ intervalSet ai and x ∈ intervalSet bj. Since i < a.size, x ∈ unionIntervalSets a. Since j < b.size, x ∈ unionIntervalSets b. Right disjunct.
-/
private lemma helper_forward (a b : Array Interval) (i j : Nat) (acc : Array Interval) (x : Int) :
    x ∈ unionIntervalSets (helper a b i j acc) →
    x ∈ unionIntervalSets acc ∨ (x ∈ unionIntervalSets a ∧ x ∈ unionIntervalSets b) := by
  intro hx;
  induction' n : a.size - i + b.size - j using Nat.strong_induction_on with n ih generalizing i j acc;
  unfold helper at hx;
  split_ifs at hx <;> norm_num at hx;
  · split_ifs at hx;
    · contrapose! ih;
      refine' ⟨ _, _, i + 1, j, acc.push ( max a[i].1 b[j].1, min a[i].2 b[j].2 ), hx, rfl, _, _ ⟩ <;> simp_all +decide [ unionIntervalSets ];
      · omega;
      · intro k hk; by_cases hk' : k < acc.size <;> simp_all +decide [ Array.getElem_push ] ;
        split_ifs <;> simp_all +decide [ intervalSet ];
        grind;
      · exact ih.2;
    · exact ih _ ( by omega ) _ _ _ hx rfl;
    · contrapose! ih;
      refine' ⟨ _, _, i, j + 1, acc.push ( max a[i].1 b[j].1, min a[i].2 b[j].2 ), hx, rfl, _, _ ⟩ <;> simp_all +decide [ unionIntervalSets ];
      · omega;
      · intro k hk; by_cases hk' : k < acc.size <;> simp_all +decide [ Array.getElem_push ] ;
        split_ifs <;> simp_all +decide [ intervalSet ];
        exact fun _ _ _ => ih.2 i ‹_› ‹_› ‹_› j ‹_› ‹_›;
      · exact ih.2;
    · exact ih _ ( by omega ) _ _ _ hx rfl;
  · exact Or.inl hx;
  · exact Or.inl hx

/-
PROBLEM
Backward direction: if x is in a[i'] ∩ b[j'] with i ≤ i' and j ≤ j', then x is in the output
(under the preconditions that the arrays are sorted and pairwise disjoint)

Key lemma: if a[i].2 ≤ b[j].2, then a[i] doesn't intersect b[j'] for j' > j

PROVIDED SOLUTION
By well-founded induction on (a.size - i + b.size - j), matching helper's termination.

Unfold helper.

Case 1: i ≥ a.size. Then i ≤ i' < a.size contradicts i ≥ a.size (since i' ≥ i ≥ a.size > i' gives contradiction). So this case is vacuously true.

Case 2: j ≥ b.size. Similarly vacuous.

Case 3: i < a.size and j < b.size. Let ai = a[i], bj = b[j], lo = max ai.1 bj.1, hi' = min ai.2 bj.2. Let acc' = if lo ≤ hi' then acc.push (lo, hi') else acc.

Sub-case 3a: ai.2 ≤ bj.2 (advance i). Result is helper a b (i+1) j acc'.

  If i' > i (i.e., i+1 ≤ i'): By IH (with i+1, j, acc'), we get x ∈ unionIntervalSets (helper a b (i+1) j acc'). Done.

  If i' = i: We have x ∈ intervalSet a[i]! and x ∈ intervalSet b[j']!.
    - x ≤ a[i].2 ≤ b[j].2 (from hx_a and the branch condition).
    - If j' > j: By pairwiseDisjointClosed b, b[j].2 < b[j'].1. So x ≤ b[j].2 < b[j'].1 ≤ x (from hx_b). Contradiction.
    - If j' = j: Then x ∈ intervalSet a[i]! ∩ intervalSet b[j]!. This means a[i].1 ≤ x ≤ a[i].2 and b[j].1 ≤ x ≤ b[j].2. So lo = max(a[i].1, b[j].1) ≤ x ≤ min(a[i].2, b[j].2) = hi'. So lo ≤ hi', meaning acc' = acc.push (lo, hi'). And x ∈ intervalSet (lo, hi'). So x ∈ unionIntervalSets acc'. By helper_acc_subset, x ∈ unionIntervalSets (helper a b (i+1) j acc'). Done.

Sub-case 3b: ai.2 > bj.2 (advance j). Result is helper a b i (j+1) acc'. Symmetric argument:
  If j' > j: By IH.
  If j' = j: x ≤ b[j].2 < a[i].2, and x ∈ intervalSet a[i']!.
    - If i' > i: By pairwiseDisjointClosed a, a[i].2 < a[i'].1. But x ∈ intervalSet b[j]! means x ≤ b[j].2 < a[i].2 < a[i'].1 ≤ x. Contradiction.
    - If i' = i: x ∈ intervalSet a[i]! ∩ intervalSet b[j]!, so lo ≤ x ≤ hi', acc' has (lo, hi'), and by helper_acc_subset we're done.

By well-founded induction on (a.size - i + b.size - j), matching helper's termination.

Unfold helper.

Case 1: i ≥ a.size. Then i ≤ i' < a.size is impossible (since i' ≥ i ≥ a.size > i'). Contradiction with hi' and hi'_lt, so omega.

Case 2: i < a.size, j ≥ b.size. Similarly j' ≥ j ≥ b.size > j'. Contradiction with hj' and hj'_lt, so omega.

Case 3: i < a.size and j < b.size. Let ai = a[i], bj = b[j], lo = max ai.1 bj.1, hi_min = min ai.2 bj.2. Let acc' = if lo ≤ hi_min then acc.push (lo, hi_min) else acc.

Sub-case 3a: ai.2 ≤ bj.2 (advance i to i+1). Result is helper a b (i+1) j acc'.

  If i' ≥ i+1 (i.e., i' > i): By IH (with i+1, j, acc'), since a.size - (i+1) + b.size - j < a.size - i + b.size - j (because i < a.size), we get x ∈ unionIntervalSets (helper a b (i+1) j acc'). Done.

  If i' = i: We have x ∈ intervalSet a[i]! means a[i]!.1 ≤ x ≤ a[i]!.2. And a[i]!.2 ≤ b[j]!.2 from the branch condition (since ai = a[i] and ai.2 ≤ bj.2). So x ≤ a[i]!.2 ≤ b[j]!.2.

    Sub-sub-case j' > j: By h_disj_b (pairwiseDisjointClosed b), b[j]!.2 < b[j']!.1. So x ≤ b[j]!.2 < b[j']!.1, but hx_b says b[j']!.1 ≤ x. Contradiction (omega/linarith).

    Sub-sub-case j' = j: Then x ∈ intervalSet a[i]! ∩ intervalSet b[j]!. This means a[i]!.1 ≤ x ≤ a[i]!.2 and b[j]!.1 ≤ x ≤ b[j]!.2. So lo = max(a[i]!.1, b[j]!.1) ≤ x and x ≤ min(a[i]!.2, b[j]!.2) = hi_min. So lo ≤ hi_min, meaning acc' = acc.push (lo, hi_min). And x ∈ intervalSet (lo, hi_min) because lo ≤ x ≤ hi_min. The element (lo, hi_min) is at index acc.size in acc'. So x ∈ unionIntervalSets acc'. By helper_acc_subset, x ∈ unionIntervalSets (helper a b (i+1) j acc'). Done.

Sub-case 3b: ¬(ai.2 ≤ bj.2), i.e., ai.2 > bj.2 (advance j to j+1). Result is helper a b i (j+1) acc'. Symmetric argument:
  If j' ≥ j+1: By IH with (i, j+1).
  If j' = j: x ∈ intervalSet b[j]! means b[j]!.1 ≤ x ≤ b[j]!.2. Since ¬(ai.2 ≤ bj.2), bj.2 < ai.2, i.e., b[j]!.2 < a[i]!.2. So x ≤ b[j]!.2 < a[i]!.2.
    Sub-sub-case i' > i: By h_disj_a, a[i]!.2 < a[i']!.1. So x ≤ b[j]!.2 < a[i]!.2 < a[i']!.1 ≤ x (from hx_a). Contradiction.
    Sub-sub-case i' = i: Then x ∈ intervalSet a[i]! ∩ intervalSet b[j]!, so lo ≤ x ≤ hi_min, lo ≤ hi_min, acc' = acc.push (lo, hi_min). x ∈ unionIntervalSets acc'. By helper_acc_subset, done.

Key: use Nat.eq_or_lt_of_le on hi' to case split i' = i vs i' > i (and similarly for hj'). Use simp [intervalSet, Set.mem_Icc] to unfold interval membership. Use h_disj_a/h_disj_b with appropriate arguments to derive contradictions. For the acc' case, show x ∈ unionIntervalSets acc' by exhibiting witness index acc.size with Array.getElem!_push_length or similar.

By pairwiseDisjointClosed, b[j]!.2 < b[j']!.1. But x ≤ b[j]!.2 < b[j']!.1, and hx_b says b[j']!.1 ≤ x (since x ∈ intervalSet b[j']! = Set.Icc b[j']!.1 b[j']!.2). Contradiction by linarith.
-/
private lemma no_future_intersection_b (b : Array Interval) (j j' : Nat)
    (h_disj_b : pairwiseDisjointClosed b)
    (hj_lt : j < b.size) (hj' : j < j') (hj'_lt : j' < b.size)
    (x : Int) (hx_ub : x ≤ b[j]!.2) (hx_b : x ∈ intervalSet b[j']!) : False := by
  linarith [ Set.mem_Icc.mp hx_b, h_disj_b j j' hj' hj'_lt ]

/-
PROBLEM
Key lemma: if b[j].2 < a[i].2, then b[j] doesn't intersect a[i'] for i' > i

PROVIDED SOLUTION
By pairwiseDisjointClosed, a[i]!.2 < a[i']!.1. But x ≤ a[i]!.2 < a[i']!.1, and hx_a says a[i']!.1 ≤ x. Contradiction by linarith.
-/
private lemma no_future_intersection_a (a : Array Interval) (i i' : Nat)
    (h_disj_a : pairwiseDisjointClosed a)
    (hi_lt : i < a.size) (hi' : i < i') (hi'_lt : i' < a.size)
    (x : Int) (hx_ub : x ≤ a[i]!.2) (hx_a : x ∈ intervalSet a[i']!) : False := by
  exact absurd ( h_disj_a i i' hi' hi'_lt ) ( by linarith [ Set.mem_Icc.mp ( show x ∈ Set.Icc ( a[i']!.1 ) ( a[i']!.2 ) from hx_a ) ] )

/-
PROBLEM
Key lemma: x in intersection of a[i] and b[j] means x is in intervalSet (max a[i].1 b[j].1, min a[i].2 b[j].2)

PROVIDED SOLUTION
hx_a says a[i]!.1 ≤ x ≤ a[i]!.2. hx_b says b[j]!.1 ≤ x ≤ b[j]!.2. So max a[i]!.1 b[j]!.1 ≤ x (by le_max_iff and both bounds) and x ≤ min a[i]!.2 b[j]!.2 (by min_le_iff and both bounds). Use simp [intervalSet, Set.mem_Icc] at hx_a hx_b and then constructor; exact le_max_of_le_left/le_max_of_le_right and min stuff.
-/
private lemma intersection_interval_mem (a b : Array Interval) (i j : Nat)
    (hi : i < a.size) (hj : j < b.size)
    (x : Int) (hx_a : x ∈ intervalSet a[i]!) (hx_b : x ∈ intervalSet b[j]!) :
    max a[i]!.1 b[j]!.1 ≤ x ∧ x ≤ min a[i]!.2 b[j]!.2 := by
  unfold intervalSet at *; aesop;

/-
PROBLEM
If x is in intervalSet (lo, hi) and lo ≤ hi, then x is in unionIntervalSets (acc.push (lo, hi))

PROVIDED SOLUTION
By well-founded induction on (a.size - i + b.size - j).

Unfold helper.

Case i ≥ a.size: omega (since i ≤ i' < a.size).
Case j ≥ b.size: omega (since j ≤ j' < b.size).

Case i < a.size and j < b.size:
Let lo = max a[i].1 b[j].1, hi_min = min a[i].2 b[j].2.
Let acc' = if lo ≤ hi_min then acc.push (lo, hi_min) else acc.

Sub-case a[i].2 ≤ b[j].2, lo ≤ hi_min (advance i, intersection added):
  Result is helper a b (i+1) j acc'.
  Case i' > i: Apply IH with (i+1, j, acc'). termination: a.size-(i+1)+b.size-j < a.size-i+b.size-j by omega.
  Case i' = i:
    From hx_a: a[i]!.1 ≤ x ≤ a[i]!.2. Since a[i].2 ≤ b[j].2, x ≤ b[j]!.2.
    Case j' > j: exact absurd (by apply no_future_intersection_b) (not_false).
    Case j' = j: x ∈ intervalSet a[i]! ∩ intervalSet b[j]!. By intersection_interval_mem, lo ≤ x ≤ hi_min.
      So x ∈ intervalSet (lo, hi_min). acc' = acc.push (lo, hi_min). x ∈ unionIntervalSets acc' (witness: acc.size).
      By helper_acc_subset, x ∈ unionIntervalSets (helper a b (i+1) j acc').

Sub-case a[i].2 ≤ b[j].2, ¬(lo ≤ hi_min) (advance i, no intersection):
  Result is helper a b (i+1) j acc.
  Case i' > i: Apply IH.
  Case i' = i: a[i]!.1 ≤ x ≤ a[i]!.2 ≤ b[j]!.2.
    Case j' > j: no_future_intersection_b gives False.
    Case j' = j: intersection_interval_mem gives lo ≤ x ≤ hi_min, contradicting ¬(lo ≤ hi_min).

Sub-case ¬(a[i].2 ≤ b[j].2), lo ≤ hi_min (advance j, intersection added): Symmetric.
Sub-case ¬(a[i].2 ≤ b[j].2), ¬(lo ≤ hi_min) (advance j, no intersection): Symmetric.

Use rcases Nat.eq_or_lt_of_le hi' with rfl | hi'_gt to split i' = i vs i' > i (similarly for j').
For the acc membership, use ⟨acc.size, by simp, ...⟩ as the witness.
Use helper_acc_subset, no_future_intersection_a, no_future_intersection_b, intersection_interval_mem as needed.

By well-founded induction on (a.size - i + b.size - j).

Unfold helper using `unfold helper; split_ifs` to handle the 3 main cases (i ≥ a.size, j ≥ b.size, both in range).

Case i ≥ a.size: Since hi' says i ≤ i' and hi'_lt says i' < a.size, we get i ≤ i' < a.size ≤ i, contradiction by omega.
Case j ≥ b.size: Similarly omega.

Case i < a.size and j < b.size:
  Use rcases Nat.eq_or_lt_of_le hi' with rfl | hi_gt for whether i' = i or i' > i.

  Branch a[i].2 ≤ b[j].2 (advance i):
    - If i' > i: Apply IH (a.size - (i+1) + b.size - j < n by omega) with (i+1, j, acc').
    - If i' = i:
      Use rcases Nat.eq_or_lt_of_le hj' with rfl | hj_gt.
      - If j' > j: Apply no_future_intersection_b with x ≤ a[i]!.2 ≤ b[j]!.2 (from hx_a giving x ≤ a[i]!.2, and the branch condition a[i]!.2 ≤ b[j]!.2). This gives False, so exact absurd ...
      - If j' = j: Use intersection_interval_mem to get lo ≤ x ∧ x ≤ hi_min. This means lo ≤ hi_min, so acc' = acc.push (lo, hi_min). Then x ∈ intervalSet (lo, hi_min) which is in acc'. Apply helper_acc_subset.

  Branch ¬(a[i].2 ≤ b[j].2) (advance j): Symmetric.
    - If j' > j: Apply IH with (i, j+1, acc').
    - If j' = j:
      Use rcases Nat.eq_or_lt_of_le hi' with rfl | hi_gt.
      - If i' > i: Apply no_future_intersection_a with x ≤ b[j]!.2 < a[i]!.2 (from hx_b giving x ≤ b[j]!.2, and ¬(a[i]!.2 ≤ b[j]!.2) giving b[j]!.2 < a[i]!.2). This gives False.
      - If i' = i: intersection_interval_mem + helper_acc_subset as above.

IMPORTANT: To show x ∈ unionIntervalSets acc', use:
  have : x ∈ unionIntervalSets (acc.push (lo, hi_min)) := ⟨acc.size, by simp, by simp [intervalSet, Set.mem_Icc]; exact ⟨h_lo, h_hi⟩⟩
where h_lo and h_hi come from intersection_interval_mem.

For the IH call, note that `acc'` might be `acc.push (...)` or `acc`, but the IH works for any acc.

To get x ≤ a[i]!.2 from hx_a when i' = i: use (Set.mem_Icc.mp hx_a).2
To get x ≤ b[j]!.2 from hx_b when j' = j: use (Set.mem_Icc.mp hx_b).2
Note that a[i]! = a[i] when i < a.size (the ! and non-! versions should be definitionally equal with the bound proof in context).

Use witness acc.size. The pushed element is at index acc.size with acc.push.size = acc.size + 1, so acc.size < (acc.push (lo, hi)).size. And (acc.push (lo, hi))[acc.size]! = (lo, hi). So x ∈ intervalSet (lo, hi) = Set.Icc lo hi by ⟨hlo, hhi⟩.
-/
private lemma mem_push_interval (acc : Array Interval) (lo hi x : Int)
    (hlo : lo ≤ x) (hhi : x ≤ hi) :
    x ∈ unionIntervalSets (acc.push (lo, hi)) := by
  exact ⟨ acc.size, by simp +decide, by simpa [ intervalSet ] using ⟨ hlo, hhi ⟩ ⟩

/-
PROVIDED SOLUTION
By well-founded induction on (a.size - i + b.size - j).

Step 1: unfold helper; split on i < a.size and j < b.size.
- If ¬(i < a.size): omega (since hi' and hi'_lt give i ≤ i' < a.size ≤ i, contradiction).
- If ¬(j < b.size): omega (since hj' and hj'_lt give j ≤ j' < b.size ≤ j, contradiction).
- If both: continue.

Step 2: In the main case (i < a.size, j < b.size), split on a[i].2 ≤ b[j].2 (the branch condition).

Case a[i].2 ≤ b[j].2 (advance i):
  Split on whether i' = i or i' > i (use rcases Nat.eq_or_lt_of_le hi').

  Sub-case i' > i (i.e., i + 1 ≤ i'):
    Apply IH with (i+1, j, acc'). The termination measure decreases: a.size - (i+1) + b.size - j < a.size - i + b.size - j because i < a.size. The IH gives x ∈ unionIntervalSets (helper a b (i+1) j acc'). This is the goal since helper unfolds to helper a b (i+1) j acc' in this branch.

  Sub-case i' = i:
    From hx_a (which is x ∈ intervalSet a[i]! = Set.Icc a[i]!.1 a[i]!.2), get a[i]!.1 ≤ x ≤ a[i]!.2.
    Since a[i].2 ≤ b[j].2, x ≤ a[i]!.2 ≤ b[j]!.2.

    Split on whether j' = j or j' > j (use rcases Nat.eq_or_lt_of_le hj').

    Sub-sub-case j' > j:
      Apply no_future_intersection_b b j j' h_disj_b (with hj_lt from the split, hj' : j < j', hj'_lt, x, x ≤ b[j]!.2, hx_b). This gives False. Exact absurd or exfalso.

    Sub-sub-case j' = j:
      Use intersection_interval_mem to get max a[i]!.1 b[j]!.1 ≤ x ∧ x ≤ min a[i]!.2 b[j]!.2.
      So lo ≤ hi_min (since lo ≤ x ≤ hi_min). Thus acc' = acc.push (lo, hi_min).
      Apply mem_push_interval to get x ∈ unionIntervalSets acc'.
      Apply helper_acc_subset to get x ∈ unionIntervalSets (helper a b (i+1) j acc').

Case ¬(a[i].2 ≤ b[j].2) (advance j, i.e., a[i].2 > b[j].2):
  Symmetric. Split on j' = j or j' > j.

  Sub-case j' > j:
    Apply IH with (i, j+1, acc').

  Sub-case j' = j:
    From hx_b, get b[j]!.1 ≤ x ≤ b[j]!.2. Since ¬(a[i].2 ≤ b[j].2), b[j]!.2 < a[i]!.2. So x ≤ b[j]!.2 < a[i]!.2, i.e., x < a[i]!.2.
    Split on i' = i or i' > i.

    Sub-sub-case i' > i:
      Apply no_future_intersection_a a i i' h_disj_a (hi_lt, hi' : i < i', hi'_lt, x, x ≤ a[i]!.2, hx_a). False.

    Sub-sub-case i' = i:
      intersection_interval_mem + mem_push_interval + helper_acc_subset.

IMPORTANT IMPLEMENTATION NOTES:
- After `unfold helper; split_ifs`, be careful about what the hypotheses look like. The split_ifs will create hypotheses like `h : i < a.size` and `h : j < b.size`.
- When applying IH, the acc' argument might be `if lo ≤ hi' then acc.push (lo, hi') else acc`. You need to pass the correct acc' to the IH.
- Do NOT use `grind` - it tends to fail in this environment. Use `omega`, `linarith`, `simp`, `exact` instead.
- For the contradiction cases, use `exact absurd ... (not_lt.mpr ...)` or `exfalso; exact no_future_intersection_b ...`.
- When unfolding intervalSet membership, use `simp [intervalSet, Set.mem_Icc] at hx_a hx_b` or `obtain ⟨h1, h2⟩ := Set.mem_Icc.mp hx_a`.
- a[i]! and a[i] (with proof hi) should be definitionally equal.  The `!` version uses `getElem!` which panics on out-of-bounds but when simp/unfold sees hi it should match.

By well-founded induction on (a.size - i + b.size - j).

CRITICAL: Do NOT use the `grind` tactic anywhere - it will fail in this environment. Use only omega, linarith, simp, aesop, exact, apply, constructor, cases, rcases, obtain, exfalso.

Proof structure:
1. `induction' h : (a.size - i) + (b.size - j) using Nat.strong_induction_on with n ih generalizing i j acc`
2. `unfold helper`
3. `split_ifs` to handle the 3 cases: i ≥ a.size, j ≥ b.size, both in range.

For i ≥ a.size: `omega` (from hi' and hi'_lt).
For j ≥ b.size: `omega` (from hj' and hj'_lt).

Main case (i < a.size, j < b.size):
Split on `a[i].2 ≤ b[j].2` (already done by split_ifs).

When a[i].2 ≤ b[j].2:
  The helper call is `helper a b (i+1) j acc'` where `acc' = if lo ≤ hi' then acc.push (lo, hi') else acc`.

  Use `rcases Nat.eq_or_lt_of_le hi' with rfl | hi_gt`.

  Case i' = i:
    Have x ≤ a[i]!.2 from hx_a: `have hx_ub := (Set.mem_Icc.mp hx_a).2`
    Have x ≤ b[j]!.2: `have hx_ub2 : x ≤ b[j]!.2 := le_trans hx_ub ‹a[i]!.2 ≤ b[j]!.2›` (note: need to handle the naming of the split_ifs hypothesis)

    Use `rcases Nat.eq_or_lt_of_le hj' with rfl | hj_gt`.

    Case j' = j:
      Get bounds from intersection_interval_mem. Then lo ≤ x ∧ x ≤ hi_min.
      Since lo ≤ hi_min (because lo ≤ x ≤ hi_min), acc' = acc.push (lo, hi_min).
      Use mem_push_interval + helper_acc_subset.

    Case j' > j:
      `exfalso; exact no_future_intersection_b b j j' h_disj_b ‹j < b.size› hj_gt hj'_lt x hx_ub2 hx_b`

  Case i' > i (i + 1 ≤ i'):
    Apply IH: `exact ih _ (by omega) (i+1) j acc' rfl (by omega) hi'_lt hj' hj'_lt hx_a hx_b`

When ¬(a[i].2 ≤ b[j].2), i.e., b[j].2 < a[i].2:
  Symmetric: split on j' = j vs j' > j.

  Case j' = j:
    Have x ≤ b[j]!.2 from hx_b: `have hx_ub := (Set.mem_Icc.mp hx_b).2`
    Have x ≤ a[i]!.2: from hx_ub and b[j].2 < a[i].2 (by linarith).

    Split on i' = i vs i' > i.

    Case i' = i:
      intersection_interval_mem + mem_push_interval + helper_acc_subset.

    Case i' > i:
      exfalso; exact no_future_intersection_a a i i' h_disj_a ‹i < a.size› hi_gt hi'_lt x (by linarith) hx_a

  Case j' > j:
    Apply IH: `exact ih _ (by omega) i (j+1) acc' rfl hi' hi'_lt (by omega) hj'_lt hx_a hx_b`

CRITICAL: Do NOT use the `grind` tactic. It does not work in this Lean version. Use only: omega, linarith, simp, aesop, exact, apply, constructor, cases, rcases, obtain, exfalso, have, refine, convert.

CRITICAL: `a[i]!` and `a[i]` (with proof `hi : i < a.size`) are NOT definitionally equal. Use `simp [getElem!_pos, hi]` to convert between them.

By well-founded induction on (a.size - i + b.size - j).

After `induction' h : (a.size - i) + (b.size - j) using Nat.strong_induction_on with n ih generalizing i j acc`, the IH has the form:
```
ih : ∀ m < n, ∀ (i_new j_new : ℕ) (acc_new : Array Interval),
      i_new ≤ i' → j_new ≤ j' → a.size - i_new + (b.size - j_new) = m →
      x ∈ unionIntervalSets (helper a b i_new j_new acc_new)
```

After `unfold helper; split_ifs with hi_lt hj_lt`:
- Case ¬(i < a.size): `exfalso; omega` (from hi' and hi'_lt)
- Case i < a.size ∧ ¬(j < b.size): `exfalso; omega` (from hj' and hj'_lt)
- Case i < a.size ∧ j < b.size: main case.

In the main case, use `simp only []` then `by_cases h_adv : a[i].2 ≤ b[j].2`:

Case a[i].2 ≤ b[j].2 (advance i):
  `simp only [h_adv, ite_true]`
  Use `by_cases hi_eq : i = i'`:
  - If i = i': `subst hi_eq`. Now i' is gone, replaced by i.
    Use `by_cases hj_eq : j = j'`:
    - If j = j': `subst hj_eq`. Now j' is gone.
      Use intersection_interval_mem to get him.
      Since him.1 and him.2 are about `a[i]!` and `b[j]!`:
        `have hle : max a[i]!.1 b[j]!.1 ≤ min a[i]!.2 b[j]!.2 := le_trans him.1 him.2`
      Convert to a[i]/b[j]: `simp [getElem!_pos, hi_lt, hj_lt] at hle`
      `simp [hle]`
      `exact helper_acc_subset a b (i+1) j _ x (mem_push_interval acc _ _ x him.1 him.2)`
    - If j ≠ j': Since j ≤ j' and j ≠ j', j < j'.
      From hx_a (with i' = i): `have hx_ub := (Set.mem_Icc.mp hx_a).2` (gives x ≤ a[i]!.2)
      Since a[i].2 ≤ b[j].2: need x ≤ b[j]!.2.
      `have : a[i]!.2 ≤ b[j]!.2 := by simp [getElem!_pos, hi_lt, hj_lt]; exact h_adv`
      `have hx_ub_b : x ≤ b[j]!.2 := le_trans hx_ub this`
      `exfalso; exact no_future_intersection_b b j j' h_disj_b hj_lt (lt_of_le_of_ne hj' (Ne.symm hj_eq)) hj'_lt x hx_ub_b hx_b`
  - If i ≠ i': Since i ≤ i' and i ≠ i', i < i', so i + 1 ≤ i'.
    `exact ih _ (by omega) (i+1) j _ (by omega : i+1 ≤ i') hj' rfl`

Case ¬(a[i].2 ≤ b[j].2) (advance j):
  `push_neg at h_adv` or `have h_adv' : b[j].2 < a[i].2 := by omega`
  `simp only [show ¬(a[i].2 ≤ b[j].2) from by omega, ite_false]`
  Use `by_cases hj_eq : j = j'`:
  - If j = j': `subst hj_eq`.
    Use `by_cases hi_eq : i = i'`:
    - If i = i': `subst hi_eq`. intersection_interval_mem + helper_acc_subset as above.
    - If i ≠ i': i < i'.
      From hx_b (with j' = j): `have hx_ub := (Set.mem_Icc.mp hx_b).2` (gives x ≤ b[j]!.2)
      `have : b[j]!.2 ≤ a[i]!.2 := by simp [getElem!_pos, hi_lt, hj_lt]; omega`
      `have hx_ub_a : x ≤ a[i]!.2 := le_trans hx_ub this`
      `exfalso; exact no_future_intersection_a a i i' h_disj_a hi_lt (lt_of_le_of_ne hi' (Ne.symm hi_eq)) hi'_lt x hx_ub_a hx_a`
  - If j ≠ j': j < j'.
    `exact ih _ (by omega) i (j+1) _ hi' (by omega : j+1 ≤ j') rfl`
-/
set_option maxHeartbeats 40000000 in
private lemma helper_backward (a b : Array Interval) (i j : Nat) (acc : Array Interval)
    (h_disj_a : pairwiseDisjointClosed a) (h_disj_b : pairwiseDisjointClosed b)
    (x : Int) (i' j' : Nat)
    (hi' : i ≤ i') (hi'_lt : i' < a.size)
    (hj' : j ≤ j') (hj'_lt : j' < b.size)
    (hx_a : x ∈ intervalSet a[i']!) (hx_b : x ∈ intervalSet b[j']!) :
    x ∈ unionIntervalSets (helper a b i j acc) := by
  -- By induction on the size of `a` and `b`, we can show that `x` is in the.union IntervalSets of `helper a b i j acc`.
  induction' h : (a.size - i) + (b.size - j) using Nat.strong_induction_on with n ih generalizing i j acc x i' j';
  unfold helper;
  split_ifs <;> try omega;
  by_cases h_case : a[i].2 ≤ b[j].2;
  · by_cases hi_eq : i = i';
    · by_cases hj_eq : j = j';
      · simp_all +decide [ intervalSet ];
        refine' helper_acc_subset a b ( i' + 1 ) j' _ x _;
        split_ifs <;> simp_all +decide [ unionIntervalSets ];
        · refine' ⟨ acc.size, _, _ ⟩ <;> simp_all +decide [ intervalSet ];
        · linarith [ ‹a[i'].1 ≤ a[i'].2 → a[i'].2 < b[j'].1› ( by linarith ) ];
      · have hx_ub : x ≤ b[j]!.2 := by
          have hx_ub : x ≤ a[i]!.2 := by
            unfold intervalSet at hx_a; aesop;
          grind;
        exact False.elim <| no_future_intersection_b b j j' h_disj_b ‹_› ( lt_of_le_of_ne hj' hj_eq ) hj'_lt x hx_ub hx_b;
    · specialize ih ( ( a.size - ( i + 1 ) ) + ( b.size - j ) ) ( by omega ) ( i + 1 ) j ( if max a[i].1 b[j].1 ≤ min a[i].2 b[j].2 then acc.push ( max a[i].1 b[j].1, min a[i].2 b[j].2 ) else acc ) x i' j' ( by omega ) ( by omega ) ( by omega ) ( by omega ) hx_a hx_b ; aesop;
  · by_cases hj_eq : j = j' <;> simp_all +decide [ Nat.lt_succ_iff ];
    · by_cases hi_eq : i = i' <;> simp_all +decide [ Nat.lt_succ_iff ];
      · split_ifs <;> try linarith;
        · convert helper_acc_subset a b i' ( j' + 1 ) ( acc.push ( max a[i'].1 b[j'].1, min a[i'].2 b[j'].2 ) ) x _ using 1;
          exact mem_push_interval _ _ _ _ ( by cases max_cases a[i'].1 b[j'].1 <;> linarith [ Set.mem_Icc.mp hx_a, Set.mem_Icc.mp hx_b ] ) ( by cases min_cases a[i'].2 b[j'].2 <;> linarith [ Set.mem_Icc.mp hx_a, Set.mem_Icc.mp hx_b ] );
        · exact absurd ( Set.mem_Icc.mp hx_b ) ( by intros h; exact ‹¬ ( ( a[i'].1 ≤ a[i'].2 ∧ b[j'].1 ≤ a[i'].2 ) ∧ a[i'].1 ≤ b[j'].2 ∧ b[j'].1 ≤ b[j'].2 ) › ⟨ ⟨ by linarith [ Set.mem_Icc.mp hx_a ], by linarith [ Set.mem_Icc.mp hx_a ] ⟩, by linarith [ Set.mem_Icc.mp hx_a ], by linarith [ Set.mem_Icc.mp hx_a ] ⟩ );
      · have := h_disj_a i i' ( lt_of_le_of_ne hi' hi_eq ) hi'_lt; simp_all +decide [ intervalSet ] ;
        linarith [ Set.mem_Icc.mp ( show x ∈ Set.Icc ( a[i'].1 ) ( a[i'].2 ) from hx_a ) ];
    · split_ifs <;> try omega;
      · convert ih ( a.size - i + ( b.size - ( j + 1 ) ) ) ( by omega ) i ( j + 1 ) ( acc.push ( max a[i].1 b[j].1, min a[i].2 b[j].2 ) ) x i' j' hi' hi'_lt ( by omega ) hj'_lt hx_a hx_b using 1;
        aesop;
      · contrapose! ih;
        refine' ⟨ _, _, i, j + 1, acc, x, i', j', hi', hi'_lt, _, hj'_lt, hx_a, hx_b, rfl, ih ⟩ ; omega;
        exact Nat.succ_le_of_lt ( lt_of_le_of_ne hj' hj_eq )

/-
PROVIDED SOLUTION
Use Set.ext to prove set equality. For the forward direction: if x ∈ unionIntervalSets (implementation firstList secondList), use helper_forward with a=firstList, b=secondList, i=0, j=0, acc=#[] to get x ∈ unionIntervalSets #[] ∨ (x ∈ unionIntervalSets firstList ∧ x ∈ unionIntervalSets secondList). The first disjunct is impossible since #[] has size 0. So x ∈ unionIntervalSets firstList ∧ x ∈ unionIntervalSets secondList. For the backward direction: if x ∈ unionIntervalSets firstList ∩ unionIntervalSets secondList, get i' and j' such that x ∈ intervalSet firstList[i']! and x ∈ intervalSet secondList[j']!. Use helper_backward with i=0, j=0, acc=#[] and h_disj_a from h_precond.2.2.2.2.1 and h_disj_b from h_precond.2.2.2.2.2 to conclude x ∈ unionIntervalSets (helper firstList secondList 0 0 #[]). Note that implementation = helper ... 0 0 #[].
-/
theorem correctness_goal_3 (firstList : Array Interval) (secondList : Array Interval) (h_precond : precondition firstList secondList) (h1 : ∀ k < (implementation firstList secondList).size, isValidInterval (implementation firstList secondList)[k]!) (h2 : sortedByStart (implementation firstList secondList)) (h3 : pairwiseDisjointClosed (implementation firstList secondList)) : unionIntervalSets (implementation firstList secondList) = unionIntervalSets firstList ∩ unionIntervalSets secondList := by
        ext x;
        constructor;
        · intro hx;
          have := helper_forward firstList secondList 0 0 #[] x hx;
          unfold unionIntervalSets at *; aesop;
        · intro hx
          obtain ⟨i', hi', hx_i'⟩ : ∃ i', i' < firstList.size ∧ x ∈ intervalSet firstList[i']! := by
            exact hx.1
          obtain ⟨j', hj', hx_j'⟩ : ∃ j', j' < secondList.size ∧ x ∈ intervalSet secondList[j']! := by
            exact hx.2
          have h_inter : x ∈ unionIntervalSets (helper firstList secondList 0 0 #[]) := by
            apply helper_backward firstList secondList 0 0 #[] h_precond.2.2.2.2.1 h_precond.2.2.2.2.2 x i' j' (Nat.zero_le i') hi' (Nat.zero_le j') hj' hx_i' hx_j'
          exact h_inter

end Proof