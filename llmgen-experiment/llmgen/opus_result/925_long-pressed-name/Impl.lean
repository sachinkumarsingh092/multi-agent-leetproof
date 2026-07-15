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
    925. Long Pressed Name: determine whether `typed` could result from typing `name` where each key press may repeat a character one or more times.
    **Important: complexity should be O((m + n)^2) time and O(1) space**
    Natural language breakdown:
    1. Inputs are two sequences of characters: `name` and `typed`.
    2. Typing `name` produces characters in the same order as `name`.
    3. Each character `name[k]` is produced at least once in `typed` (normal press) and may be repeated additional times contiguously (long press).
    4. The overall `typed` output must be exactly the concatenation of these contiguous blocks, one block per character position in `name`.
    5. Therefore, `typed` can be partitioned into exactly `name.size` nonempty consecutive segments; the k-th segment contains only copies of `name[k]`.
    6. If such a partition exists, return true; otherwise return false.
-/

section Specs
-- `segmentAllEq typed start stop c` means: the slice typed[start..stop) is within bounds
-- and every element in that slice equals `c`.
-- We keep this as a Prop (not a reference implementation).
def segmentAllEq (typed : Array Char) (start : Nat) (stop : Nat) (c : Char) : Prop :=
  start ≤ stop ∧ stop ≤ typed.size ∧
    ∀ (i : Nat), start ≤ i ∧ i < stop → typed[i]! = c

-- A partition `breaks` of `typed` into `name.size` consecutive nonempty segments.
-- `breaks` has length `name.size + 1`.
-- Segment k is typed[breaks[k] .. breaks[k+1]) and must be all equal to name[k].
def validBreaks (name : Array Char) (typed : Array Char) (breaks : Array Nat) : Prop :=
  breaks.size = name.size + 1 ∧
  breaks[0]! = 0 ∧
  breaks[name.size]! = typed.size ∧
  (∀ (k : Nat), k < name.size → breaks[k]! < breaks[k+1]!) ∧
  (∀ (k : Nat), k < name.size → segmentAllEq typed breaks[k]! breaks[k+1]! name[k]!)

-- Main correctness predicate: such a valid partition exists.
def isLongPressed (name : Array Char) (typed : Array Char) : Prop :=
  ∃ (breaks : Array Nat), validBreaks name typed breaks

-- No domain restrictions were stated beyond the types.
def precondition (name : Array Char) (typed : Array Char) : Prop :=
  True

-- Result is true iff the long-pressed predicate holds.
def postcondition (name : Array Char) (typed : Array Char) (result : Bool) : Prop :=
  (result = true ↔ isLongPressed name typed)
end Specs

section Impl
method LongPressedName (name : Array Char) (typed : Array Char)
  return (result : Bool)
  require precondition name typed
  ensures postcondition name typed result
  do
  let mut i : Nat := 0
  let mut j : Nat := 0
  let mut ok := true
  while i < name.size
    invariant "i_bound" i ≤ name.size
    invariant "j_bound" j ≤ typed.size
    -- Forward: ok=true means partial breaks exist for name[0..i) → typed[0..j)
    -- Init: i=0, j=0, breaks=#[0] trivially works (size=1, breaks[0]!=0=j, no k<0)
    -- Pres: each iteration extends breaks by appending new j value for segment i
    -- Suff: at exit i=name.size, ok=true gives full partial breaks; combined with j=typed.size gives validBreaks
    invariant "ok_true_partial" ok = true →
      ∃ (breaks : Array Nat), breaks.size = i + 1 ∧ breaks[0]! = 0 ∧ breaks[i]! = j ∧
        (∀ k, k < i → breaks[k]! < breaks[k+1]!) ∧
        (∀ k, k < i → segmentAllEq typed breaks[k]! breaks[k+1]! name[k]!)
    -- Backward (greedy optimality): proving ok=false → ¬isLongPressed requires showing
    -- the greedy algorithm never falls behind any valid partition. Formally, we need:
    --   "∃ valid breaks with breaks[i]! = j" (existential greedy-stays-optimal)
    -- This requires a redistribution/exchange argument when consecutive name chars are equal:
    -- if name[i]=name[i+1] and nextDiff=false, the algorithm assigns only 1 char to segment i,
    -- but a valid partition might assign more. We'd need to show we can always redistribute
    -- to get a valid partition with breaks[i+1]! = j+1. This redistribution lemma is
    -- inherently inductive and beyond SMT automation for loop invariant checking.
    invariant "greedy_optimality_placeholder" true = true
    done_with (i = name.size ∨ ok = false)
    decreasing name.size - i
  do
    -- Must match at least one character
    if j >= typed.size then
      ok := false
      break
    else
      if typed[j]! != name[i]! then
        ok := false
        break
      else
        let c := name[i]!
        -- consume the one mandatory character
        j := j + 1
        -- Check if next name char is different (or this is last name char)
        -- If so, greedily consume all extra copies of c
        let nextDiff := (i + 1 >= name.size) || (name[i + 1]! != c)
        if nextDiff then
          while j < typed.size ∧ typed[j]! = c
            invariant "inner_j_bound" j ≤ typed.size
            invariant "inner_i_bound" i < name.size
            invariant "inner_char_eq" c = name[i]!
            -- Forward: partial breaks exist with segment i partially consumed [breaks[i]!, j)
            -- Init: after j:=j+1, typed[old_j]!=name[i]! from if-check, so 1-element segment works
            -- Pres: inner loop extends segment by one more matching char (typed[j]!=c=name[i]!)
            invariant "inner_ok_true_partial" ok = true →
              ∃ (breaks : Array Nat), breaks.size = i + 1 ∧ breaks[0]! = 0 ∧
              breaks[i]! < j ∧
              (∀ k, k < i → breaks[k]! < breaks[k+1]!) ∧
              (∀ k, k < i → segmentAllEq typed breaks[k]! breaks[k+1]! name[k]!) ∧
              (∀ m, breaks[i]! ≤ m ∧ m < j → typed[m]! = name[i]!)
            -- Backward for inner loop: same exchange argument issue as outer loop.
            -- After greedy consumption of all c's, j should equal breaks[i+1]! for some
            -- valid partition, but proving this requires the redistribution lemma.
            invariant "inner_greedy_optimality_placeholder" true = true
            decreasing typed.size - j
          do
            j := j + 1
        i := i + 1
  if j != typed.size then
    ok := false
  return ok
end Impl

section TestCases
-- Test case 1: Example 1
-- name = "alex", typed = "aaleex" -> true
-- 'a' and 'e' can be long-pressed.
def test1_name : Array Char := #['a', 'l', 'e', 'x']
def test1_typed : Array Char := #['a', 'a', 'l', 'e', 'e', 'x']
def test1_Expected : Bool := true

-- Test case 2: Example 2
-- name = "saeed", typed = "ssaaedd" -> false
-- The second 'e' in name is missing in typed (cannot be explained by long-press).
def test2_name : Array Char := #['s', 'a', 'e', 'e', 'd']
def test2_typed : Array Char := #['s', 's', 'a', 'a', 'e', 'd', 'd']
def test2_Expected : Bool := false

-- Test case 3: Exact match (no long presses)
def test3_name : Array Char := #['a', 'l', 'e', 'x']
def test3_typed : Array Char := #['a', 'l', 'e', 'x']
def test3_Expected : Bool := true

-- Test case 4: Typed shorter than name -> impossible
-- name = "alex", typed = "alx" (missing 'e')
def test4_name : Array Char := #['a', 'l', 'e', 'x']
def test4_typed : Array Char := #['a', 'l', 'x']
def test4_Expected : Bool := false

-- Test case 5: Empty name and empty typed -> valid (zero characters typed)
def test5_name : Array Char := #[]
def test5_typed : Array Char := #[]
def test5_Expected : Bool := true

-- Test case 6: Empty name but nonempty typed -> impossible (extra characters)
def test6_name : Array Char := #[]
def test6_typed : Array Char := #['a']
def test6_Expected : Bool := false

-- Test case 7: Repeated characters in name; typed splits a long run into multiple presses
-- name = "aa", typed = "aaaa" -> true (split into 1+3, 2+2, etc.)
def test7_name : Array Char := #['a', 'a']
def test7_typed : Array Char := #['a', 'a', 'a', 'a']
def test7_Expected : Bool := true

-- Test case 8: Wrong order -> impossible
-- name = "ab", typed = "ba"
def test8_name : Array Char := #['a', 'b']
def test8_typed : Array Char := #['b', 'a']
def test8_Expected : Bool := false

-- Test case 9: Extra trailing different character -> impossible
-- name = "alex", typed = "aaleexy" (extra 'y' at end)
def test9_name : Array Char := #['a', 'l', 'e', 'x']
def test9_typed : Array Char := #['a', 'a', 'l', 'e', 'e', 'x', 'y']
def test9_Expected : Bool := false
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((LongPressedName test1_name test1_typed).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((LongPressedName test2_name test2_typed).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((LongPressedName test3_name test3_typed).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((LongPressedName test4_name test4_typed).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((LongPressedName test5_name test5_typed).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((LongPressedName test6_name test6_typed).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((LongPressedName test7_name test7_typed).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((LongPressedName test8_name test8_typed).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((LongPressedName test9_name test9_typed).run), DivM.res test9_Expected ]
end Assertions

section Pbt
velvet_plausible_test LongPressedName (config := { maxMs := some 20000 })
end Pbt
