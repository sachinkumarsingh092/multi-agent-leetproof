import Lean

import Mathlib.Tactic
import Mathlib.Data.Nat.Size

set_option maxHeartbeats 10000000

section Specs
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false
set_option pp.funBinderTypes true

/- Problem Description
    1552. Magnetic Force Between Two Balls: maximize the minimum distance between any two placed balls.
    **Important: complexity should be O(n log n) time and O(1) space**
    Natural language breakdown:
    1. We are given n basket positions as natural numbers in an array `position`.
    2. The input array `position` is given in ascending sorted order.
    3. We must place exactly m balls into m distinct baskets (so we choose m distinct indices).
    4. The magnetic force between two balls at positions x and y is |x - y|.
    5. For a particular placement, its score is the minimum force among all pairs of chosen baskets.
    6. The required answer is the maximum score achievable over all valid placements.
    7. Constraints imply m ≥ 2 and m ≤ n; basket positions are pairwise distinct.
-/

-- Strictly increasing indices inside an array.
def StrictlyIncreasing (idxs : Array Nat) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < idxs.size → idxs[i]! < idxs[j]!

-- All indices are within bounds of the positions array.
def IndicesInRange (pos : Array Nat) (idxs : Array Nat) : Prop :=
  ∀ (k : Nat), k < idxs.size → idxs[k]! < pos.size

-- Pairwise distance lower bound for the chosen indices.
def PairwiseDistGE (pos : Array Nat) (idxs : Array Nat) (d : Nat) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < idxs.size →
    d ≤ (pos[idxs[j]!]!) - (pos[idxs[i]!]!)

-- Feasibility predicate: there exists a selection of exactly m baskets
-- whose pairwise distances are all at least d.
def Feasible (pos : Array Nat) (m : Nat) (d : Nat) : Prop :=
  ∃ (idxs : Array Nat),
    idxs.size = m ∧
    StrictlyIncreasing idxs ∧
    IndicesInRange pos idxs ∧
    PairwiseDistGE pos idxs d

def precondition (position : Array Nat) (m : Nat) : Prop :=
  m ≥ 2 ∧ m ≤ position.size ∧ StrictlyIncreasing position

-- The result is the maximum d such that placing m balls with minimum pairwise distance ≥ d is feasible.
def postcondition (position : Array Nat) (m : Nat) (result : Nat) : Prop :=
  Feasible position m result ∧
  (∀ (d' : Nat), result < d' → ¬ Feasible position m d')
end Specs

section Impl
def implementation (position : Array Nat) (m : Nat) : Nat :=
  let n := position.size
  if n = 0 then
    0
  else
    let minPos := position[0]!
    let maxPos := position[n - 1]!

    -- Greedy feasibility check in one left-to-right pass.
    let canPlace (d : Nat) : Bool :=
      let (count, _last) :=
        position.foldl
          (fun (st : Nat × Nat) (cur : Nat) =>
            let (count, last) := st
            if count = 0 then
              (1, cur)
            else if last + d ≤ cur then
              (count + 1, cur)
            else
              (count, last))
          (0, 0)
      count ≥ m

    let hi0 := maxPos - minPos

    -- Construct the maximum feasible distance by setting bits from high to low.
    -- We use `hi0.size` bits, which is enough for unbounded `Nat`.
    let rec loop (b : Nat) (ans : Nat) : Nat :=
      match b with
      | 0 => ans
      | b' + 1 =>
        let bit : Nat := Nat.shiftLeft 1 b'
        let cand := ans + bit
        let ans' := if cand ≤ hi0 ∧ canPlace cand then cand else ans
        loop b' ans'

    loop hi0.size 0
end Impl

section TestCases
def test1_position : Array Nat := #[1, 2, 3, 4, 7]
def test1_m : Nat := 3
def test1_Expected : Nat := 3
def test2_position : Array Nat := #[1, 2, 3, 4, 5, 1000000000]
def test2_m : Nat := 2
def test2_Expected : Nat := 999999999
def test3_position : Array Nat := #[10, 20]
def test3_m : Nat := 2
def test3_Expected : Nat := 10
def test4_position : Array Nat := #[1, 6, 11, 20]
def test4_m : Nat := 4
def test4_Expected : Nat := 5
def test5_position : Array Nat := #[0, 7, 10, 19]
def test5_m : Nat := 2
def test5_Expected : Nat := 19
def test6_position : Array Nat := #[0, 1, 2, 4, 8, 10]
def test6_m : Nat := 3
def test6_Expected : Nat := 4
def test7_position : Array Nat := #[1, 9, 10, 17]
def test7_m : Nat := 3
def test7_Expected : Nat := 8
def test8_position : Array Nat := #[0, 2, 3, 5, 6]
def test8_m : Nat := 3
def test8_Expected : Nat := 3
def test9_position : Array Nat := #[0, 25, 50, 75, 100]
def test9_m : Nat := 2
def test9_Expected : Nat := 100
end TestCases

section Proof

-- The greedy step function
@[simp] def greedyStep (d : Nat) (st : Nat × Nat) (cur : Nat) : Nat × Nat :=
  if st.1 = 0 then (1, cur)
  else if st.2 + d ≤ cur then (st.1 + 1, cur)
  else st

-- Greedy fold on an array
def greedyFold (d : Nat) (position : Array Nat) : Nat × Nat :=
  position.foldl (greedyStep d) (0, 0)

-- Greedy count
def greedyCount (d : Nat) (position : Array Nat) : Nat :=
  (greedyFold d position).1

-- ============================================================
-- Feasible monotonicity
-- ============================================================
lemma feasible_mono (pos : Array Nat) (m : Nat) (d d' : Nat) (hle : d' ≤ d)
    (hfeas : Feasible pos m d) : Feasible pos m d' := by
  obtain ⟨idxs, hidxs⟩ := hfeas
  exact ⟨idxs, hidxs.1, hidxs.2.1, hidxs.2.2.1, fun i j hij hlt => le_trans hle (hidxs.2.2.2 i j hij hlt)⟩

/-
PROBLEM
============================================================
Greedy optimality (exchange argument)
============================================================

Helper: the foldl step never decreases count

PROVIDED SOLUTION
By induction on l. Base case empty list: trivial. Step: l = x :: l'. foldl (x::l') st = foldl l' (greedyStep d st x). By IH, (greedyStep d st x).1 ≤ foldl result. And greedyStep d st x has count ≥ st.1 (case analysis: if count=0 → 1 ≥ 0; if last+d≤cur → count+1 ≥ count; else → count ≥ count). So by transitivity.
-/
lemma foldl_greedyStep_count_ge (d : Nat) (l : List Nat) (st : Nat × Nat) :
    st.1 ≤ (l.foldl (greedyStep d) st).1 := by
  -- We can prove this by induction on the list $l$.
  induction' l with x l ih generalizing st <;> simp [List.foldl] at *; (
  grind);

/-
PROBLEM
Helper: for a sorted position array, after processing prefix 0..n,
last ≤ position[n] (when count > 0).
More general: foldl over a list with all elements ≤ bound keeps last ≤ bound.

PROVIDED SOLUTION
By induction on l. Base case: trivial from hst. Step: l = x :: l'. Apply to greedyStep d st x. Case analysis on greedyStep: if count=0 → (1, x), count is 1 ≠ 0, last = x ≤ bound (from hall). if last+d≤cur → (count+1, x), count+1 > 0, last = x ≤ bound. else → st unchanged, so hst still holds. In all cases, the new state satisfies .1 = 0 ∨ .2 ≤ bound. Apply IH with the remaining list (all elements still ≤ bound since x ∈ l implies forall in tail).
-/
lemma foldl_greedyStep_last_le (d : Nat) (l : List Nat) (st : Nat × Nat)
    (hst : st.1 = 0 ∨ st.2 ≤ bound)
    (hall : ∀ x ∈ l, x ≤ bound) :
    (l.foldl (greedyStep d) st).1 = 0 ∨ (l.foldl (greedyStep d) st).2 ≤ bound := by
  induction' l using List.reverseRecOn with l ih <;> aesop

/-
PROBLEM
Helper: if we append a single element cur where last + d ≤ cur (and count > 0),
the count increases by at least 1.

PROVIDED SOLUTION
Unfold greedyStep. Since hcount : st.1 > 0, st.1 ≠ 0. Since hgap : st.2 + d ≤ cur, the second branch is taken: result = (st.1 + 1, cur). So result.1 = st.1 + 1 ≥ st.1 + 1.
-/
lemma foldl_greedyStep_place (d : Nat) (st : Nat × Nat)
    (hcount : st.1 > 0) (hgap : st.2 + d ≤ cur) :
    (greedyStep d st cur).1 ≥ st.1 + 1 := by
  unfold greedyStep; aesop;

/-
PROBLEM
For a sorted position array, elements at index ≤ n have values ≤ position[n]

PROVIDED SOLUTION
For a strictly increasing array position, all elements at indices ≤ n have values ≤ position[n].

position.toList.take (n + 1) contains elements position[0], ..., position[n]. Since position is strictly increasing, position[i] < position[j] for i < j. So for any i ≤ n, position[i] ≤ position[n].

Proof: take x ∈ position.toList.take (n+1). Then x = position.toList[i] for some i ≤ n. Since i ≤ n and n < position.size, position.toList[i] = position[i]!. If i < n, position[i]! < position[n]! by h_sorted. If i = n, position[i]! = position[n]!. Either way, x ≤ position[n]!.

Use List.mem_iff_get or List.getElem_take to extract the index.
-/
lemma sorted_take_le (position : Array Nat) (n : Nat) (hn : n < position.size)
    (h_sorted : StrictlyIncreasing position) :
    ∀ x ∈ position.toList.take (n + 1), x ≤ position[n]! := by
  intro x hx;
  obtain ⟨ i, hi, rfl ⟩ := List.mem_iff_get.mp hx;
  by_cases hi' : i.val < n;
  · have := h_sorted i.val n hi';
    grind;
  · grind

/-
PROBLEM
Core inductive claim: after folding take (idxs[k]! + 1), count ≥ k + 1

PROVIDED SOLUTION
By induction on k.

Base case k = 0:
position.toList.take (idxs[0]! + 1) is non-empty (since idxs[0]! < position.size, so idxs[0]! + 1 ≥ 1).
The foldl starts with (0, 0). On the first element (count = 0), it goes to (1, first_elem). After that, count only increases or stays. So final count ≥ 1.

Inductive step k → k + 1:
By IH, after folding take (idxs[k]! + 1), count ≥ k + 1.

Split take (idxs[k+1]! + 1) = take (idxs[k]! + 1) ++ (drop (idxs[k]!+1) of take (idxs[k+1]!+1)).
Use List.foldl_append: foldl over the concatenation = foldl of suffix starting from foldl of prefix.

Let st = foldl result after take (idxs[k]! + 1). We have st.1 ≥ k + 1 > 0.

By foldl_greedyStep_last_le (using sorted_take_le to show all elements in take (idxs[k]!+1) are ≤ position[idxs[k]!]!), either st.1 = 0 (impossible since ≥ k+1) or st.2 ≤ position[idxs[k]!]!.

Now we fold the remaining elements (from index idxs[k]!+1 to idxs[k+1]!). By foldl_greedyStep_count_ge, count doesn't decrease through intermediate elements.

At the element position[idxs[k+1]!]! (the last element in the suffix), we have:
- current count ≥ k + 1 > 0
- last ≤ position[idxs[k]!]! (could have changed but only to values ≤ position[idxs[k]!]! since all intermediate elements ≤ position[idxs[k+1]!]! ... actually intermediate elements might be anything since between idxs[k] and idxs[k+1])

Wait, the intermediate elements between idxs[k]!+1 and idxs[k+1]! are position values at those array indices. Since position is sorted (strictly increasing), they are all > position[idxs[k]!]! and < position[idxs[k+1]!]! (well, ≥ and ≤ due to strict increase). Actually they could have any values between the two... no, position IS strictly increasing so position[i] < position[j] for i < j. So intermediate values are between position[idxs[k]!] and position[idxs[k+1]!].

But for the "last" tracking: after processing intermediate elements, last might have increased (if the greedy placed at an intermediate position). But even so, last is set to some position[i] where idxs[k]! < i ≤ idxs[k+1]!, so last ≤ position[idxs[k+1]!]! (since position is sorted and i ≤ idxs[k+1]!).

Wait, I need last to be ≤ some value so that last + d ≤ position[idxs[k+1]!]!. From PairwiseDistGE: d ≤ position[idxs[k+1]!]! - position[idxs[k]!]!. If last ≤ position[idxs[k]!]!, then last + d ≤ position[idxs[k]!]! + d ≤ position[idxs[k+1]!]!.

But does last ≤ position[idxs[k]!]! hold after folding the intermediate elements? Let me think... the intermediate elements are all in positions idxs[k]!+1 to idxs[k+1]!-1 of the position array. Their values are all < position[idxs[k+1]!]! (sorted). But they could be > position[idxs[k]!]! (since they're at higher indices).

Actually, when we fold elements position[idxs[k]!+1], ..., position[idxs[k+1]!], the greedy might or might not place. If it places at position[i] for some intermediate i, then last = position[i] > position[idxs[k]!]! (since i > idxs[k]!). So last > position[idxs[k]!]! and we can't directly use last + d ≤ position[idxs[k+1]!]!.

BUT: the key insight is that when we reach position[idxs[k+1]!], we need to check if last + d ≤ position[idxs[k+1]!]!. If last was set to some position[i] where idxs[k]! < i < idxs[k+1]!, then last = position[i] < position[idxs[k+1]!]! (since position is sorted). And we need last + d ≤ position[idxs[k+1]!]!. Since last < position[idxs[k+1]!]!, this is NOT guaranteed.

Hmm wait. But actually last ≤ position[idxs[k]!]! AFTER the prefix fold (by the invariant). The intermediate elements might change last. But using foldl_greedyStep_last_le: if all intermediate elements + the target element are ≤ position[idxs[k+1]!]! (which is true since position is sorted), then last after folding these stays... well, foldl_greedyStep_last_le says st.1 = 0 ∨ st.2 ≤ bound. With bound = position[idxs[k+1]!]!, last ≤ position[idxs[k+1]!]!. But this is too weak.

Actually, I should use a different bound. Let me not fold intermediate elements up to position[idxs[k+1]!]. Instead:

After folding take (idxs[k]!+1): st.1 ≥ k+1 > 0, st.2 ≤ position[idxs[k]!]!.
Then fold the remaining elements (idxs[k]!+1 to idxs[k+1]!-1): by foldl_greedyStep_last_le with bound = position[idxs[k+1]!-1]!, last stays ≤ position[idxs[k+1]!-1]! < position[idxs[k+1]!]!.
Hmm, this doesn't help either.

Actually, the simplest approach: fold ALL elements from idxs[k]!+1 to idxs[k+1]!. After folding these elements including position[idxs[k+1]!]!, the greedy WILL have placed at position[idxs[k+1]!]! or earlier. The count after processing take (idxs[k+1]!+1) is ≥ k+2.

To show this: after take (idxs[k]!+1), st.2 ≤ position[idxs[k]!]! and st.1 ≥ k+1 > 0. When we encounter position[idxs[k+1]!]! (which is the last element in the suffix), we need to show that at that point, the current last + d ≤ position[idxs[k+1]!]!.

But the current last could have increased from position[idxs[k]!]! to some higher value. However, by foldl_greedyStep_last_le applied to elements from idxs[k]!+1 to idxs[k+1]!-1 (all ≤ position[idxs[k+1]!-1]! ≤ position[idxs[k+1]!]! - 1 since position is strictly increasing), last ≤ position[idxs[k+1]!-1]! or count is still 0 (impossible).

But I need last + d ≤ position[idxs[k+1]!]!, not last ≤ position[idxs[k+1]!]!.

Hmm. Actually the key property I need is: just before processing position[idxs[k+1]!]!, the state (count, last) satisfies last + d ≤ position[idxs[k+1]!]!.

I know: after take (idxs[k]!+1), last ≤ position[idxs[k]!]!.
PairwiseDistGE gives: d ≤ position[idxs[k+1]!]! - position[idxs[k]!]!.
So position[idxs[k]!]! + d ≤ position[idxs[k+1]!]!.

But last might have increased after processing intermediate elements. The crucial insight: last ONLY increases when the greedy PLACES a ball (last becomes the current element). And the current element is some position[i] where i > idxs[k]!. Since position is sorted, position[i] > position[idxs[k]!]!. So last > position[idxs[k]!]!. Does last + d ≤ position[idxs[k+1]!]! still hold? Not necessarily.

Example: position = [1, 5, 6, 10], idxs = [0, 3], d = 4.After take 1: st = (1, 1). last = 1 = position[0].
Intermediate: position[1] = 5. 1 + 4 = 5 ≤ 5, so greedy places: st = (2, 5).
position[2] = 6. 5 + 4 = 9 > 6, skip.
position[3] = 10. 5 + 4 = 9 ≤ 10, greedy places: st = (3, 10).
Count = 3 ≥ 2 = m. ✓

So even though last increased to 5 (from 1), at position[3]=10 we have 5 + 4 = 9 ≤ 10. ✓

But if intermediate elements are closer together:
position = [1, 9, 10, 15], idxs = [0, 3], d = 5.
After take 1: st = (1, 1). last = 1.
position[1] = 9: 1 + 5 = 6 ≤ 9, places: st = (2, 9).position[2] = 10: 9 + 5 = 14 > 10, skip.position[3] = 15: 9 + 5 = 14 ≤ 15, places: st = (3, 15).Count ≥ 2 ✓.

But d = 5 and position[3] - position[0] = 14. What if d = 8?
position = [1, 9, 10, 15], idxs = [0, 3], d = 8. 15 - 1 = 14 ≥ 8. ✓After take 1: st = (1, 1).
position[1] = 9: 1 + 8 = 9 ≤ 9, places: st = (2, 9).
position[2] = 10: 9 + 8 = 17 > 10, skip.
position[3] = 15: 9 + 8 = 17 > 15. DOESN'T PLACE!

So the greedy doesn't place at idxs[1]=3! Count = 2, but we need count ≥ 2 for m=2. Count is 2. ✓ It placed at index 0 and 1 instead.

But the issue is: the greedy placed at an intermediate index (1), which "used up" the gap. It still got count ≥ m because it found other placements.

Actually, the exchange argument claim is: after processing up to idxs[k+1]!, count ≥ k+2. In the above example, after processing all of take(4), count = 2. For k=0, k+2=2. So count ≥ 2 ✓.

But my approach of showing "the greedy places at idxs[k+1]!" doesn't work because it might not place at that exact index. Instead, the greedy might have already placed at an intermediate index.

OK so the correct argument is: count can only increase or stay the same. After take (idxs[k]!+1), count ≥ k+1. After folding more elements, count ≥ k+1. But I need count ≥ k+2.

The key insight: from index idxs[k]!+1 to idxs[k+1]!, there are at least (idxs[k+1]! - idxs[k]!) elements. Among these, the last one (position[idxs[k+1]!]) has value such that position[idxs[k+1]!] - position[idxs[k]!] ≥ d. But the greedy might have placed at some intermediate element, moving last forward.

Wait, I think the correct argument is this: the greedy after processing idxs[k]!+1 elements has placed ≥ k+1 balls. We need to show that after processing up to idxs[k+1]!+1 elements, it has placed ≥ k+2 balls.

Key claim: between indices idxs[k]!+1 and idxs[k+1]! (inclusive), the greedy will place at least one more ball.

Proof of this claim: after index idxs[k]!, last ≤ position[idxs[k]!]! and count ≥ k+1 > 0.
The total range from position[idxs[k]!] to position[idxs[k+1]!] is ≥ d. So somewhere in this range, the greedy must place. Specifically, at position[idxs[k+1]!]!, even if intermediate placements happened, either:
(a) The greedy has already placed at some intermediate index (count increased by ≥ 1, done), OR
(b) No intermediate placement happened, so last is still ≤ position[idxs[k]!]!, and at position[idxs[k+1]!]!, last + d ≤ position[idxs[k]!]! + d ≤ position[idxs[k+1]!]!, so the greedy places.

In either case, count increases by at least 1. ✓

So the argument is: fold from state st (with st.1 > 0, st.2 ≤ position[idxs[k]!]!) over elements position[idxs[k]!+1] ... position[idxs[k+1]!]. Either the count increases by ≥ 1 somewhere (case a), or it doesn't increase for any of position[idxs[k]!+1] ... position[idxs[k+1]!-1], in which case last stays ≤ position[idxs[k]!]! and at position[idxs[k+1]!]!, the greedy places (case b).

More formally: if count doesn't increase for elements position[idxs[k]!+1], ..., position[idxs[k+1]!-1], then last stays ≤ position[idxs[k]!]! (since the greedy didn't place, last didn't change... wait, if the greedy DID place at an intermediate index, last changed. But I'm in the case where count didn't increase. If count doesn't increase, no placement happened, so last stays the same. Actually, the step function: if count = 0, goes to (1, cur) - count increases. If last + d ≤ cur, goes to (count+1, cur) - count increases. Else, stays (count, last) - count stays. So count not increasing means no placement, which means last stays the same.

So if no intermediate placement: last stays ≤ position[idxs[k]!]!. At position[idxs[k+1]!]!, last + d ≤ position[idxs[k]!]! + d ≤ position[idxs[k+1]!]!. Greedy places. Count increases.

If some intermediate placement: count already increased ≥ 1. Done.

So in all cases, count after folding up to idxs[k+1]! is ≥ k + 2.

This is a simple disjunction argument. Let me encode it as: the foldl of a list starting from state st where st.1 > 0 and st.2 + d ≤ max element... actually, let me just state it as a helper lemma and have the subagent prove it:

foldl_count_increases: for any list l with last element ≥ st.2 + d (and st.1 > 0),
  (l.foldl (greedyStep d) st).1 ≥ st.1 + 1.

This would be proved by: either some element in l causes a placement (in which case count increases), or no element causes a placement (meaning last stays st.2), and since the last element of l is ≥ st.2 + d, the last element causes a placement.
-/
lemma greedy_exchange_core (position : Array Nat) (d : Nat) (idxs : Array Nat) (m : Nat)
    (h_sorted : StrictlyIncreasing position)
    (hidxs_size : idxs.size = m)
    (hidxs_inc : StrictlyIncreasing idxs)
    (hidxs_range : IndicesInRange position idxs)
    (hidxs_dist : PairwiseDistGE position idxs d)
    (k : Nat) (hk : k < m) :
    k + 1 ≤ (position.toList.take (idxs[k]! + 1) |>.foldl (greedyStep d) (0, 0)).1 := by
  induction' k with k ih generalizing position d idxs m;
  · induction' n : idxs[0]! with n ih <;> simp_all +decide [ List.take_add_one ];
    · have := hidxs_range 0 ; aesop;
    · cases h : position[‹_›]? <;> simp_all +decide [ List.foldl ];
      · have := hidxs_range 0; simp_all +decide [ List.foldl ] ;
        grind;
      · grind;
  · -- By the induction hypothesis, after processing up to idxs[k]!+1, the count is at least k+1.
    have h_ind : k + 1 ≤ (List.foldl (greedyStep d) (0, 0) (List.take (idxs[k]! + 1) position.toList)).1 := by
      exact ih position d idxs m h_sorted hidxs_size hidxs_inc hidxs_range hidxs_dist ( Nat.lt_of_succ_lt hk );
    -- By the properties of the greedy algorithm, after processing up to idxs[k+1]!+1, the count is at least k+2.
    have h_count : (List.foldl (greedyStep d) (0, 0) (List.take (idxs[k+1]! + 1) position.toList)).1 ≥ (List.foldl (greedyStep d) (0, 0) (List.take (idxs[k]! + 1) position.toList)).1 + 1 := by
      have h_count : (List.foldl (greedyStep d) (List.foldl (greedyStep d) (0, 0) (List.take (idxs[k]! + 1) position.toList)) (List.drop (idxs[k]! + 1) (List.take (idxs[k+1]! + 1) position.toList))).1 ≥ (List.foldl (greedyStep d) (0, 0) (List.take (idxs[k]! + 1) position.toList)).1 + 1 := by
        -- By the properties of the greedy algorithm, processing the remaining elements (from idxs[k]!+1 to idxs[k+1]!) will increase the count by at least 1. We need to show that there exists an element in this range that causes the count to increase.
        have h_exists_element : ∃ x ∈ List.drop (idxs[k]! + 1) (List.take (idxs[k+1]! + 1) position.toList), (List.foldl (greedyStep d) (0, 0) (List.take (idxs[k]! + 1) position.toList)).2 + d ≤ x := by
          refine' ⟨ position[idxs[k+1]!]!, _, _ ⟩ <;> simp_all +decide [ List.mem_iff_get ];
          · use ⟨ idxs[k + 1] - ( idxs[k]! + 1 ), by
              simp +arith +decide [ List.length_drop, List.length_take ];
              rw [ min_eq_left ];
              · rw [ tsub_lt_tsub_iff_right ] <;> norm_num;
                convert hidxs_inc k ( k + 1 ) ( Nat.lt_succ_self k ) using 1;
                aesop;
              · have := hidxs_range ( k + 1 ) ; aesop; ⟩
            generalize_proofs at *;
            simp +decide [ add_tsub_cancel_of_le ( show idxs[k]! + 1 ≤ idxs[k + 1] from by
                                                    have := hidxs_inc k ( k + 1 ) ; aesop; ) ];
            all_goals generalize_proofs at *;
            exact?;
          · have := hidxs_dist k ( k + 1 ) ( by linarith ) ( by linarith );
            have h_last_le : (List.foldl (greedyStep d) (0, 0) (List.take (idxs[k]! + 1) position.toList)).2 ≤ position[idxs[k]!]! := by
              have h_last_le : ∀ (l : List ℕ), (∀ x ∈ l, x ≤ position[idxs[k]!]!) → (List.foldl (greedyStep d) (0, 0) l).1 = 0 ∨ (List.foldl (greedyStep d) (0, 0) l).2 ≤ position[idxs[k]!]! := by
                intros l hl; induction' l using List.reverseRecOn with l ih <;> aesop;
              specialize h_last_le (List.take (idxs[k]! + 1) position.toList);
              exact h_last_le ( fun x hx => sorted_take_le position ( idxs[k]! ) ( by
                exact hidxs_range _ ( by linarith ) ) h_sorted x hx ) |> Or.rec ( fun h => by linarith ) fun h => h;
            convert Nat.add_le_add h_last_le this using 1;
            rw [ Nat.add_sub_of_le ];
            · grind;
            · have h_pos_le : ∀ i j : ℕ, i < j → j < position.size → position[i]! ≤ position[j]! := by
                exact fun i j hij hj => le_of_lt ( h_sorted i j hij hj );
              apply h_pos_le;
              · exact hidxs_inc _ _ ( Nat.lt_succ_self _ ) ( by linarith );
              · exact hidxs_range _ ( by linarith );
        -- Since the element x in the list drop (idxs[k]! + 1) (take (idxs[k+1]! + 1) position.toList) satisfies the condition, the greedy algorithm will place a ball at x, increasing the count by 1.
        have h_place : ∀ {l : List ℕ} {st : ℕ × ℕ}, st.1 > 0 → (∃ x ∈ l, st.2 + d ≤ x) → (List.foldl (greedyStep d) st l).1 ≥ st.1 + 1 := by
          intros l st hst_pos h_exists_element; induction' l with x l ih generalizing st <;> simp_all +decide [ List.foldl ] ;
          split_ifs <;> simp_all +decide [ Nat.succ_eq_add_one ];
          · exact Nat.lt_of_succ_le ( by simpa using foldl_greedyStep_count_ge d l ( st.1 + 1, x ) );
          · exact ih _ _ hst_pos _ h_exists_element.choose_spec.1 h_exists_element.choose_spec.2;
        exact h_place ( by linarith ) h_exists_element;
      convert h_count using 1;
      rw [ ← List.take_append_drop ( idxs[k]! + 1 ) ( List.take ( idxs[k + 1]! + 1 ) position.toList ), List.foldl_append ];
      simp +decide [ List.take_take ];
      rw [ min_eq_left ];
      · rw [ List.drop_append_of_le_length ];
        · rw [ List.drop_take ] ; aesop;
        · simp +arith +decide [ hidxs_range ];
          exact hidxs_range _ ( by linarith );
      · have := hidxs_inc k ( k + 1 ) ( Nat.lt_succ_self k );
        exact le_of_lt ( this ( by linarith ) );
    linarith

-- Main exchange argument lemma
lemma greedy_optimality (position : Array Nat) (m : Nat) (d : Nat)
    (h_sorted : StrictlyIncreasing position)
    (hfeas : Feasible position m d) :
    m ≤ greedyCount d position := by
  obtain ⟨idxs, hidxs_size, hidxs_inc, hidxs_range, hidxs_dist⟩ := hfeas
  by_cases hm_pos : 0 < m
  · have hcore := greedy_exchange_core position d idxs m h_sorted hidxs_size hidxs_inc hidxs_range hidxs_dist (m - 1) (by omega)
    have hcore' : m ≤ (position.toList.take (idxs[m - 1]! + 1) |>.foldl (greedyStep d) (0, 0)).1 := by omega
    -- greedyCount = foldl on toList
    have hmono := foldl_greedyStep_count_ge d (position.toList.drop (idxs[m - 1]! + 1))
      (position.toList.take (idxs[m - 1]! + 1) |>.foldl (greedyStep d) (0, 0))
    have hconv : greedyCount d position = ((position.toList.take (idxs[m - 1]! + 1) ++ position.toList.drop (idxs[m - 1]! + 1)).foldl (greedyStep d) (0, 0)).1 := by
      simp [greedyCount, greedyFold, Array.foldl_toList, List.take_append_drop]
    rw [hconv, List.foldl_append]
    exact le_trans hcore' hmono
  · push_neg at hm_pos; omega

-- ============================================================
-- Greedy soundness
-- ============================================================

-- Helper: define greedyIndices recursively
-- greedyIndicesAux d pos idx count last = list of indices placed
def greedyIndicesAux (d : Nat) (pos : Array Nat) (idx : Nat) (count : Nat) (last : Nat) : List Nat :=
  if h : idx < pos.size then
    if count = 0 then
      idx :: greedyIndicesAux d pos (idx + 1) 1 pos[idx]
    else if last + d ≤ pos[idx] then
      idx :: greedyIndicesAux d pos (idx + 1) (count + 1) pos[idx]
    else
      greedyIndicesAux d pos (idx + 1) count last
  else []
termination_by pos.size - idx

def greedyIndices (d : Nat) (pos : Array Nat) : List Nat :=
  greedyIndicesAux d pos 0 0 0

/-
PROBLEM
Properties of greedyIndices

PROVIDED SOLUTION
Show that greedyIndices produces a list whose length equals the greedy count.

Both greedyIndicesAux and the foldl-based greedyCount process the array left-to-right with the same logic.

Define a generalized lemma: for all idx count last,
  (greedyIndicesAux d pos idx count last).length + count =
  (pos.toList.drop idx |>.foldl (greedyStep d) (count, last)).1

Prove by well-founded induction on pos.size - idx, matching the termination proof of greedyIndicesAux.

Base case: idx ≥ pos.size → greedyIndicesAux returns [], length = 0. Drop gives empty list, foldl is identity, result = count. 0 + count = count. ✓

Step: idx < pos.size. Three cases based on the greedy decision:
- count = 0: greedyIndicesAux prepends idx, recurses with (idx+1, 1, pos[idx]).
  foldl: greedyStep with count=0 gives (1, pos[idx]), then continues.
  By IH: (recursive length) + 1 = foldl of drop (idx+1) starting from (1, pos[idx]).
  Left side: (recursive length + 1) = greedyIndicesAux length. Right side: foldl of drop idx = foldl of (pos[idx] :: drop(idx+1)) = foldl of drop(idx+1) starting from greedyStep(count, last, pos[idx]).

- last + d ≤ pos[idx]: similar, prepend and recurse with count+1.
- else: don't prepend, recurse with same count.

In all cases, apply IH with idx+1.
-/
lemma greedyIndices_length_eq_count (d : Nat) (pos : Array Nat) :
    (greedyIndices d pos).length = greedyCount d pos := by
  -- Apply the generalize lemma to conclude the proof.
  have h_generalize : ∀ (idx count last : ℕ), (greedyIndicesAux d pos idx count last).length + count = (pos.toList.drop idx |>.foldl (greedyStep d) (count, last)).fst := by
    intros idx count last; induction' h : pos.size - idx with n ih generalizing idx count last <;> simp_all +arith +decide;
    · unfold greedyIndicesAux;
      split_ifs <;> simp_all +decide [ Nat.sub_eq_iff_eq_add ];
      · omega;
      · omega;
      · omega;
      · rw [ List.drop_eq_nil_of_le ] <;> aesop;
    · unfold greedyIndicesAux; simp_all +arith +decide [ List.drop ] ;
      split_ifs <;> simp_all +arith +decide [ List.drop_eq_getElem_cons ];
      · grind +ring;
      · grind +ring;
      · grind +ring;
  specialize h_generalize 0 0 0 ; aesop

/-
PROVIDED SOLUTION
The greedy algorithm processes indices in increasing order (idx always increases). Each index added to the list is strictly greater than the previous one because idx increases by 1 at each step.

Prove a generalized lemma about greedyIndicesAux: all elements in greedyIndicesAux d pos idx count last are ≥ idx, and they form a strictly increasing sequence.

More precisely: for greedyIndicesAux d pos idx count last, if the result is [i0, i1, ...], then idx ≤ i0 < i1 < i2 < ...

By well-founded induction on pos.size - idx:
- If idx ≥ pos.size: result is [], trivially true.
- If idx < pos.size:
  Case count = 0 or last + d ≤ pos[idx]: result is idx :: recursive_result. The recursive result has all elements ≥ idx+1 > idx, so idx < all recursive elements. And recursive elements are strictly increasing by IH.
  Case else: result = recursive_result with idx+1. All elements ≥ idx+1 > idx and strictly increasing by IH.
-/
lemma greedyIndices_strictMono (d : Nat) (pos : Array Nat) :
    ∀ i j, i < j → j < (greedyIndices d pos).length →
    (greedyIndices d pos)[i]! < (greedyIndices d pos)[j]! := by
  intros i j hij hj_lt_length
  have h_strict_incr : ∀ k : ℕ, k < (greedyIndices d pos).length → ∀ l : ℕ, l < (greedyIndices d pos).length → k < l → (greedyIndices d pos)[k]! < (greedyIndices d pos)[l]! := by
    -- By definition of `greedyIndices`, the indices are strictly increasing. We prove this by induction on the length of the list.
    have h_increasing : ∀ (idx : ℕ) (count : ℕ) (last : ℕ), (greedyIndicesAux d pos idx count last).Pairwise (fun x y => x < y) := by
      intro idx count last
      induction' n : (pos.size - idx) using Nat.strong_induction_on with n ih generalizing idx count last;
      unfold greedyIndicesAux;
      split_ifs <;> simp_all +decide [ List.pairwise_cons ];
      · -- By definition of `greedyIndicesAux`, the list is strictly increasing.
        have h_increasing : ∀ (idx : ℕ) (count : ℕ) (last : ℕ), (∀ a' ∈ greedyIndicesAux d pos idx count last, idx ≤ a') ∧ List.Pairwise (fun x y => x < y) (greedyIndicesAux d pos idx count last) := by
          intros idx count last; induction' n : pos.size - idx using Nat.strong_induction_on with n ih generalizing idx count last; unfold greedyIndicesAux; split_ifs <;> simp_all +decide [ List.pairwise_cons ] ;
          · grind;
          · grind;
          · grind;
        exact ⟨ fun a' ha' => lt_of_lt_of_le ( Nat.lt_succ_self _ ) ( h_increasing _ _ _ |>.1 _ ha' ), h_increasing _ _ _ |>.2 ⟩;
      · refine' ⟨ _, ih _ _ _ _ _ rfl ⟩;
        · intro a' ha';
          -- By definition of `greedyIndicesAux`, if `a'` is in the list, then `a'` must be greater than or equal to `idx + 1`.
          have h_a'_ge_idx1 : ∀ {idx count last : ℕ}, a' ∈ greedyIndicesAux d pos idx count last → idx ≤ a' := by
            intros idx count last ha'; induction' n : pos.size - idx using Nat.strong_induction_on with n ih generalizing idx count last; unfold greedyIndicesAux at ha'; split_ifs at ha' <;> simp_all +decide [ List.mem_cons ] ;
            · grind;
            · grind;
            · exact le_trans ( by linarith ) ( ih _ ( by omega ) ha' rfl );
          linarith [ h_a'_ge_idx1 ha' ];
        · omega;
      · exact ih _ ( by omega ) _ _ _ rfl;
    specialize h_increasing 0 0 0 ; simp_all +decide [ List.pairwise_iff_get ] ;
    exact fun k hk l hl hkl => h_increasing ⟨ k, hk ⟩ ⟨ l, hl ⟩ hkl;
  exact h_strict_incr i ( by linarith ) j hj_lt_length hij

/-
PROVIDED SOLUTION
All indices produced by greedyIndicesAux are < pos.size.

Prove by well-founded induction on pos.size - idx. In greedyIndicesAux, we only enter the body when idx < pos.size (the if h : idx < pos.size guard). When we prepend idx, idx < pos.size. For recursive calls with idx+1, the IH gives all those indices are < pos.size too.
-/
lemma greedyIndices_inRange (d : Nat) (pos : Array Nat) :
    ∀ k, k < (greedyIndices d pos).length →
    (greedyIndices d pos)[k]! < pos.size := by
  have h_le : ∀ (idx : Nat) (count : Nat) (last : Nat), idx ≤ pos.size → ∀ k, k < (greedyIndicesAux d pos idx count last).length → (greedyIndicesAux d pos idx count last)[k]! < pos.size := by
    intros idx count last hidx k hk_lt_length
    induction' n : pos.size - idx using Nat.strong_induction_on with n ih generalizing idx count last k;
    unfold greedyIndicesAux at hk_lt_length ⊢;
    grind;
  exact h_le 0 0 0 ( Nat.zero_le _ )

-- Combined property of greedyIndicesAux:
-- 1. When count > 0 and result non-empty, pos[head]! ≥ last + d
-- 2. Consecutive elements satisfy pos[b]! ≥ pos[a]! + d
lemma greedyIndicesAux_gap_props (d : Nat) (pos : Array Nat) (idx count last : Nat) :
    let L := greedyIndicesAux d pos idx count last
    (count > 0 → L ≠ [] → last + d ≤ pos[L.head!]!) ∧
    (∀ k, k + 1 < L.length → pos[L[k]!]! + d ≤ pos[L[k + 1]!]!) := by
  induction' h : pos.size - idx using Nat.strong_induction_on with n ih generalizing idx count last
  unfold greedyIndicesAux
  split_ifs with hidx hcount hgap
  ·
    let L' := greedyIndicesAux d pos (idx + 1) 1 pos[idx]
    have hsmall : pos.size - (idx + 1) < pos.size - idx := by
      omega
    have hsmall' : pos.size - (idx + 1) < n := by
      simpa [h] using hsmall
    have hrec := ih (pos.size - (idx + 1)) hsmall' (idx + 1) 1 pos[idx] rfl
    constructor
    · intro hpos _
      omega
    · intro k hk
      cases k with
      | zero =>
          have hL' : L' ≠ [] := by
            intro hnil
            simp [L', hnil] at hk
          have hhead := hrec.1 (by omega) hL'
          have hL'' : greedyIndicesAux d pos (idx + 1) 1 pos[idx]! ≠ [] := by
            simpa [L', Eq.symm (getElem!_pos pos idx hidx)] using hL'
          cases haux : greedyIndicesAux d pos (idx + 1) 1 pos[idx]! with
          | nil => cases (hL'' haux)
          | cons a as =>
              simp [haux, Eq.symm (getElem!_pos pos idx hidx)] at hhead ⊢
              exact hhead
      | succ k =>
          have hk' : k + 1 < L'.length := by
            simpa [L'] using hk
          have hstep := hrec.2 k hk'
          simpa [L'] using hstep
  ·
    let L' := greedyIndicesAux d pos (idx + 1) (count + 1) pos[idx]
    have hsmall : pos.size - (idx + 1) < pos.size - idx := by
      omega
    have hsmall' : pos.size - (idx + 1) < n := by
      simpa [h] using hsmall
    have hrec := ih (pos.size - (idx + 1)) hsmall' (idx + 1) (count + 1) pos[idx] rfl
    constructor
    · intro _ _
      simpa [Eq.symm (getElem!_pos pos idx hidx)] using hgap
    · intro k hk
      cases k with
      | zero =>
          have hL' : L' ≠ [] := by
            intro hnil
            simp [L', hnil] at hk
          have hhead := hrec.1 (by omega) hL'
          have hL'' : greedyIndicesAux d pos (idx + 1) (count + 1) pos[idx]! ≠ [] := by
            simpa [L', Eq.symm (getElem!_pos pos idx hidx)] using hL'
          cases haux : greedyIndicesAux d pos (idx + 1) (count + 1) pos[idx]! with
          | nil => cases (hL'' haux)
          | cons a as =>
              simp [haux, Eq.symm (getElem!_pos pos idx hidx)] at hhead ⊢
              exact hhead
      | succ k =>
          have hk' : k + 1 < L'.length := by
            simpa [L'] using hk
          have hstep := hrec.2 k hk'
          simpa [L'] using hstep
  ·
    have hsmall : pos.size - (idx + 1) < pos.size - idx := by
      omega
    have hsmall' : pos.size - (idx + 1) < n := by
      simpa [h] using hsmall
    simpa using ih (pos.size - (idx + 1)) hsmall' (idx + 1) count last rfl
  ·
    constructor
    · intro _ hnil
      cases (hnil rfl)
    · intro k hk
      simp at hk

lemma greedyIndices_pairwiseDistGE (d : Nat) (pos : Array Nat)
    (hsorted : StrictlyIncreasing pos) :
    ∀ i j, i < j → j < (greedyIndices d pos).length →
    d ≤ pos[(greedyIndices d pos)[j]!]! - pos[(greedyIndices d pos)[i]!]! := by
  intro i j hij hj
  suffices h : pos[(greedyIndices d pos)[i]!]! + d ≤ pos[(greedyIndices d pos)[j]!]! by omega
  have h_consec := (greedyIndicesAux_gap_props d pos 0 0 0).2
  have h_gap_i : pos[(greedyIndices d pos)[i]!]! + d ≤ pos[(greedyIndices d pos)[i + 1]!]! := by
    unfold greedyIndices at hj ⊢
    exact h_consec i (by omega)
  by_cases hij1 : i + 1 = j
  · subst hij1; exact h_gap_i
  · have hi1_lt_j : i + 1 < j := by omega
    have h_res_inc := greedyIndices_strictMono d pos (i + 1) j hi1_lt_j hj
    have h_res_j_range := greedyIndices_inRange d pos j hj
    have h_pos_mono := le_of_lt (hsorted _ _ h_res_inc h_res_j_range)
    omega

/-
PROBLEM
Greedy soundness: use greedyIndices to construct witness

PROVIDED SOLUTION
Given greedyCount d position ≥ m, construct Feasible.

Use the greedyIndices function. By greedyIndices_length_eq_count, greedyIndices has length = greedyCount ≥ m. Take the first m elements: (greedyIndices d position).take m, convert to Array.

Let idxs := ((greedyIndices d position).take m).toArray.

Then:
- idxs.size = m (since take m of a list of length ≥ m has length m)
- StrictlyIncreasing idxs: follows from greedyIndices_strictMono (sublists of strictly increasing lists are strictly increasing)
- IndicesInRange: follows from greedyIndices_inRange
- PairwiseDistGE: follows from greedyIndices_pairwiseDistGE (sublists preserve pairwise distances)

The key technical step is connecting List operations (take, getElem) to Array operations (size, getElem!). Use Array.toArray_toList, List.length_take, etc.
-/
lemma greedy_soundness (position : Array Nat) (m : Nat) (d : Nat)
    (h_precond : precondition position m)
    (hcount : m ≤ greedyCount d position) :
    Feasible position m d := by
  -- Let's define the array `idxs` as the first `m` elements of `greedyIndices d position`.
  set idxs : Array ℕ := ((greedyIndices d position).take m).toArray;
  refine' ⟨ idxs, _, _, _, _ ⟩;
  · have := greedyIndices_length_eq_count d position; aesop;
  · intro i j hij hj;
    have h_mono : StrictlyIncreasing (List.toArray (List.take m (greedyIndices d position))) := by
      intros i j hij hj;
      have := greedyIndices_strictMono d position i j hij;
      grind;
    convert h_mono i j hij _;
    aesop;
  · intro k hk;
    have := greedyIndices_inRange d position k ?_ <;> aesop;
  · intro i j hij hj
    have h_dist : d ≤ (position[(greedyIndices d position)[j]!]!) - (position[(greedyIndices d position)[i]!]!) := by
      apply greedyIndices_pairwiseDistGE d position h_precond.2.2 i j hij;
      aesop;
    grind +ring

/-
PROBLEM
============================================================
Bitwise loop optimality
============================================================

PROVIDED SOLUTION
Prove by showing: for all d' with canPlace d' = true and d' ≤ hi0, d' ≤ loop result.

By induction on b: loop b ans returns the max x in [ans, ans + 2^b - 1] ∩ [0, hi0] with canPlace x = true. Use hmono (anti-monotonicity) to show that if canPlace(ans+2^b') = false, all larger values in range also have canPlace = false.
-/
lemma bitwise_loop_optimal (canPlace : Nat → Bool) (hi0 : Nat)
    (hmono : ∀ a b : Nat, a ≤ b → canPlace b = true → canPlace a = true) :
    ∀ (d' : Nat), implementation.loop canPlace hi0 hi0.size 0 < d' → d' ≤ hi0 →
    canPlace d' = false := by
  have h_ind :
      ∀ b ans,
        (∀ d', ans + 2 ^ b ≤ d' → d' ≤ hi0 → canPlace d' = false) →
        ∀ d', implementation.loop canPlace hi0 b ans < d' → d' ≤ hi0 → canPlace d' = false := by
    intro b
    induction b with
    | zero =>
        intro ans hbound d' hlt hle
        have hlt' : ans < d' := by
          simpa [implementation.loop] using hlt
        have hge : ans + 2 ^ 0 ≤ d' := by omega
        exact hbound d' hge hle
    | succ b ih =>
        intro ans hbound d' hlt hle
        simp [implementation.loop, Nat.shiftLeft_eq] at hlt
        by_cases htake : ans + 2 ^ b ≤ hi0 ∧ canPlace (ans + 2 ^ b) = true
        · apply ih (ans + 2 ^ b)
          · intro d'' hd'' hle''
            exact hbound d'' (by omega) hle''
          · simpa [htake] using hlt
          · exact hle
        · apply ih ans
          · intro d'' hd'' hle''
            by_cases hleCand : ans + 2 ^ b ≤ hi0
            · have hfalseCand : canPlace (ans + 2 ^ b) = false := by
                exact Bool.eq_false_iff.mpr (by
                  intro htrue
                  exact htake ⟨ hleCand, htrue ⟩)
              by_cases hdtrue : canPlace d'' = true
              · have := hmono (ans + 2 ^ b) d'' (by omega) hdtrue
                have hcontra : False := by
                  rw [hfalseCand] at this
                  cases this
                exact False.elim hcontra
              · exact Bool.eq_false_iff.mpr hdtrue
            · have : False := by omega
              exact False.elim this
          · simpa [htake] using hlt
          · exact hle
  intro d' hlt hle
  apply h_ind hi0.size 0
  · intro d'' hd'' hle''
    have hltpow : hi0 < 2 ^ hi0.size := Nat.lt_size_self hi0
    have : False := by omega
    exact False.elim this
  · exact hlt
  · exact hle

/-
PROBLEM
============================================================
Not feasible above range
============================================================

PROVIDED SOLUTION
Assume Feasible. Get idxs with size m ≥ 2. Take i=0, j=m-1. By PairwiseDistGE: d ≤ position[idxs[m-1]!]! - position[idxs[0]!]!. Since position is sorted and indices are in range, position[idxs[0]!]! ≥ position[0]! and position[idxs[m-1]!]! ≤ position[n-1]!. So d ≤ position[n-1]! - position[0]!, contradicting hd.
-/
lemma not_feasible_above_range (position : Array Nat) (m : Nat) (d : Nat)
    (h_precond : precondition position m)
    (hd : position[position.size - 1]! - position[0]! < d) :
    ¬ Feasible position m d := by
  contrapose! hd with h_not_feasible;
  obtain ⟨ idxs, hidxs ⟩ := h_not_feasible;
  have h_bounds : ∀ k, k < idxs.size → position[idxs[k]!]! ≥ position[0]! ∧ position[idxs[k]!]! ≤ position[position.size - 1]! := by
    have h_sorted : ∀ i j, i < j → j < position.size → position[i]! < position[j]! := by
      exact h_precond.2.2;
    intros k hk
    have h_bounds : idxs[k]! < position.size := by
      exact hidxs.2.2.1 k hk;
    exact ⟨ if h : idxs[k]! = 0 then by aesop else by linarith [ h_sorted 0 ( idxs[k]! ) ( Nat.pos_of_ne_zero h ) h_bounds ], if h : idxs[k]! = position.size - 1 then by aesop else by linarith [ h_sorted ( idxs[k]! ) ( position.size - 1 ) ( lt_of_le_of_ne ( Nat.le_sub_one_of_lt h_bounds ) h ) ( Nat.sub_lt ( Nat.pos_of_ne_zero ( by aesop ) ) zero_lt_one ) ] ⟩;
  have := hidxs.2.2.2 0 ( m - 1 ) ; rcases m with ( _ | _ | m ) <;> simp_all +arith +decide;
  · cases h_precond ; aesop;
  · cases h_precond ; aesop;
  · grind

/-
PROBLEM
============================================================
Implementation connection
============================================================

PROVIDED SOLUTION
Unfold implementation. Since position.size ≠ 0, take else branch. The canPlace in implementation is definitionally equal to decide (greedyCount d position ≥ m). The body should be definitionally equal. Use unfold/simp/aesop.
-/
lemma implementation_eq_loop (position : Array Nat) (m : Nat) (hn : position.size ≠ 0) :
    implementation position m = implementation.loop
      (fun d => (greedyCount d position) ≥ m)
      (position[position.size - 1]! - position[0]!)
      (position[position.size - 1]! - position[0]!).size
      0 := by
  unfold implementation; aesop;

-- ============================================================
-- Main theorems
-- ============================================================

theorem correctness_goal_0_1 (position : Array ℕ) (m : ℕ) (h_precond : precondition position m) (hFeas0 : Feasible position m 0) : ∀ (d : ℕ),
  m ≤
      (Array.foldl
          (fun st cur =>
            Prod.casesOn st fun fst snd =>
              (fun count last =>
                  if count = 0 then (1, cur) else if last + d ≤ cur then (count + 1, cur) else (count, last))
                fst snd)
          (0, 0) position).1 →
    Feasible position m d := by
    intro d hcount
    exact greedy_soundness position m d h_precond hcount

theorem correctness_goal_1 (position : Array ℕ) (m : ℕ) (h_precond : precondition position m) (h_feas : Feasible position m (implementation position m)) : ∀ (d' : ℕ), implementation position m < d' → ¬Feasible position m d' := by
    intro d' hd' hfeas
    have hn : position.size ≠ 0 := by obtain ⟨hm2, hmn, _⟩ := h_precond; omega
    have h_sorted := h_precond.2.2
    have hgc := greedy_optimality position m d' h_sorted hfeas
    set hi0 := position[position.size - 1]! - position[0]!
    by_cases hle : d' ≤ hi0
    · have himpl := implementation_eq_loop position m hn
      rw [himpl] at hd'
      have hmono : ∀ a b : Nat, a ≤ b → decide (greedyCount b position ≥ m) = true → decide (greedyCount a position ≥ m) = true := by
        intro a b hab hb
        simp only [decide_eq_true_eq] at hb ⊢
        have hfeas_b := greedy_soundness position m b h_precond hb
        have hfeas_a := feasible_mono position m b a hab hfeas_b
        exact greedy_optimality position m a h_sorted hfeas_a
      have hfalse := bitwise_loop_optimal (fun d => greedyCount d position ≥ m) hi0 hmono d' hd' hle
      simp [decide_eq_false_iff_not] at hfalse
      omega
    · push_neg at hle
      exact not_feasible_above_range position m d' h_precond hle hfeas
end Proof
