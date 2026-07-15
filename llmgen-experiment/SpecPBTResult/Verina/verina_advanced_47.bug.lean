import Velvet.Std
import Extensions.Testing
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem: mergeIntervals

section Specs

register_specdef_allow_recursion

def precondition (intervals : List (Prod Int Int)) : Prop :=
  True

instance instDecidablePrecond (intervals : List (Prod Int Int)) : Decidable (precondition intervals) := by
  unfold precondition
  infer_instance

def postcondition (intervals : List (Prod Int Int)) (result : List (Prod Int Int)) :=
  -- Check that all original intervals are covered by some result interval
  let covered := intervals.all (fun (s, e) =>
    result.any (fun (rs, re) => rs ≤ s ∧ e ≤ re))

  -- Check that no intervals in the result overlap
  let rec noOverlap (l : List (Prod Int Int)) : Bool :=
    match l with
    | [] | [_] => true
    | (_, e1) :: (s2, e2) :: rest => e1 < s2 && noOverlap ((s2, e2) :: rest)

  covered ∧ noOverlap result

end Specs

section Impl

def mergeIntervals (intervals : List (Prod Int Int)) : List (Prod Int Int) :=
  -- Insertion sort based on the start of intervals
    let rec insert (x : Prod Int Int) (sorted : List (Prod Int Int)) : List (Prod Int Int) :=
      match sorted with
      | [] => [x]
      | y :: ys => if x.fst ≤ y.fst then x :: sorted else y :: insert x ys

    let rec sort (xs : List (Prod Int Int)) : List (Prod Int Int) :=
      match xs with
      | [] => []
      | x :: xs' => insert x (sort xs')

    let sorted := sort intervals

    -- Merge sorted intervals
    let rec merge (xs : List (Prod Int Int)) (acc : List (Prod Int Int)) : List (Prod Int Int) :=
      match xs, acc with
      | [], _ => acc.reverse
      | (s, e) :: rest, [] => merge rest [(s, e)]
      | (s, e) :: rest, (ps, pe) :: accTail =>
        if s ≤ pe then
          merge rest ((ps, max pe e) :: accTail)
        else
          merge rest ((s, e) :: (ps, pe) :: accTail)

    merge sorted []

end Impl

section TestCases

def test1_intervals : List (Prod Int Int) := [(1, 3), (2, 6), (8, 10), (15, 18)]
def test1_Expected : List (Prod Int Int) := [(1, 6), (8, 10), (15, 18)]

def test2_intervals : List (Prod Int Int) := [(1, 4), (4, 5)]
def test2_Expected : List (Prod Int Int) := [(1, 5)]

def test3_intervals : List (Prod Int Int) := [(1, 10), (2, 3), (4, 5)]
def test3_Expected : List (Prod Int Int) := [(1, 10)]

def test4_intervals : List (Prod Int Int) := [(1, 2), (3, 4), (5, 6)]
def test4_Expected : List (Prod Int Int) := [(1, 2), (3, 4), (5, 6)]

def test5_intervals : List (Prod Int Int) := [(5, 6), (1, 3), (2, 4)]
def test5_Expected : List (Prod Int Int) := [(1, 4), (5, 6)]

end TestCases

set_option maxHeartbeats 500000

def uniqueness_test1'' (result : List (Prod Int Int)) :
  result ≠ test1_Expected →
  ¬ postcondition test1_intervals result := by
  try dsimp at *
  plausible'_mut (seeds := #[test1_Expected]) (config := { numInst := 100000 })
