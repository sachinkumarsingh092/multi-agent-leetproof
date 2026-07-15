import Velvet.Std
import Extensions.Tactics
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false
set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

/- Problem Description
    1189. Maximum Number of Balloons: compute how many copies of the word "balloon" can be formed from a given text.
    **Important: complexity should be O(n) time and O(1) space**
    Natural language breakdown:
    1. Input is a sequence of characters `text`.
    2. A single instance of the word "balloon" requires the multiset of letters: b×1, a×1, l×2, o×2, n×1.
    3. Each character from `text` may be used at most once across all formed instances.
    4. The output is the maximum natural number `k` such that `text` contains at least the required number of each character to form `k` instances.
    5. If `text` lacks any required character, the maximum is 0.
-/

section Specs
-- Count the occurrences of a character in a character list.
-- We use `List.count` from Mathlib (requires `DecidableEq Char`, available).
def charCount (text : List Char) (c : Char) : Nat :=
  text.count c

-- A number k is feasible if `text` contains enough letters to form k copies of "balloon".
def feasibleBalloons (text : List Char) (k : Nat) : Prop :=
  k ≤ charCount text 'b' ∧
  k ≤ charCount text 'a' ∧
  (2 * k) ≤ charCount text 'l' ∧
  (2 * k) ≤ charCount text 'o' ∧
  k ≤ charCount text 'n'

-- No preconditions: any list of characters is allowed.
def precondition (text : List Char) : Prop :=
  True

-- Postcondition: `result` is feasible and is the maximum feasible k.
def postcondition (text : List Char) (result : Nat) : Prop :=
  feasibleBalloons text result ∧
  (∀ k : Nat, feasibleBalloons text k → k ≤ result)
end Specs

section Impl
method MaximumNumberOfBalloons (text : List Char)
  return (result : Nat)
  require precondition text
  ensures postcondition text result
  do
  -- O(n) time, O(1) extra space: single pass counting required letters.
  let mut cb : Nat := 0
  let mut ca : Nat := 0
  let mut cl : Nat := 0
  let mut co : Nat := 0
  let mut cn : Nat := 0

  -- Iterate through the list without calling List.length in the loop measure.
  let mut xs : List Char := text
  let mut fuel : Nat := text.length
  while fuel > 0
    -- Fuel tracks the remaining length of xs.
    -- Initialization: fuel = text.length and xs = text.
    -- Preservation: on x :: xs' branch, both decrease by 1; on [] branch we set fuel := 0.
    invariant "inv_fuel_len" fuel = xs.length
    -- Each counter equals the number of occurrences in the processed prefix;
    -- equivalently, counter + occurrences remaining in xs equals total occurrences in text.
    -- Initialization: counters are 0 and xs = text.
    -- Preservation: when consuming x, exactly one of the equations changes appropriately.
    invariant "inv_count_b" cb + charCount xs 'b' = charCount text 'b'
    invariant "inv_count_a" ca + charCount xs 'a' = charCount text 'a'
    invariant "inv_count_l" cl + charCount xs 'l' = charCount text 'l'
    invariant "inv_count_o" co + charCount xs 'o' = charCount text 'o'
    invariant "inv_count_n" cn + charCount xs 'n' = charCount text 'n'
    decreasing fuel
  do
    match xs with
    | [] =>
      -- Nothing left to process; consume remaining fuel to finish.
      fuel := 0
    | x :: xs' =>
      if x = 'b' then
        cb := cb + 1
      if x = 'a' then
        ca := ca + 1
      if x = 'l' then
        cl := cl + 1
      if x = 'o' then
        co := co + 1
      if x = 'n' then
        cn := cn + 1
      xs := xs'
      fuel := fuel - 1

  let l2 : Nat := cl / 2
  let o2 : Nat := co / 2

  -- Compute the minimum of the limiting letter counts.
  let mut m : Nat := cb
  if ca < m then
    m := ca
  if l2 < m then
    m := l2
  if o2 < m then
    m := o2
  if cn < m then
    m := cn

  return m
end Impl

section TestCases
-- Test case 1: Example 1
-- text = "nlaebolko" -> 1
-- ['n','l','a','e','b','o','l','k','o']
def test1_text : List Char := ['n','l','a','e','b','o','l','k','o']
def test1_Expected : Nat := 1

-- Test case 2: Example 2
-- text = "loonbalxballpoon" -> 2
-- ['l','o','o','n','b','a','l','x','b','a','l','l','p','o','o','n']
def test2_text : List Char := ['l','o','o','n','b','a','l','x','b','a','l','l','p','o','o','n']
def test2_Expected : Nat := 2

-- Test case 3: Example 3
-- text = "leetcode" -> 0
-- ['l','e','e','t','c','o','d','e']
def test3_text : List Char := ['l','e','e','t','c','o','d','e']
def test3_Expected : Nat := 0

-- Test case 4: Exact word "balloon" -> 1
-- ['b','a','l','l','o','o','n']
def test4_text : List Char := ['b','a','l','l','o','o','n']
def test4_Expected : Nat := 1

-- Test case 5: Two copies concatenated -> 2
-- ['b','a','l','l','o','o','n','b','a','l','l','o','o','n']
def test5_text : List Char := ['b','a','l','l','o','o','n','b','a','l','l','o','o','n']
def test5_Expected : Nat := 2

-- Test case 6: Missing required letters -> 0
-- text = "balon" (only one 'l' and one 'o')
def test6_text : List Char := ['b','a','l','o','n']
def test6_Expected : Nat := 0

-- Test case 7: Empty input -> 0

def test7_text : List Char := []
def test7_Expected : Nat := 0

-- Test case 8: Many letters, limited by 'o' (odd count) -> 1
-- b2 a2 l4 o3 n3 => min(2,2,4/2=2,3/2=1,3)=1

def test8_text : List Char := ['b','b','a','a','l','l','l','l','o','o','o','n','n','n']
def test8_Expected : Nat := 1

-- Test case 9: Extra a/n but minimal b -> 1
-- b1 a2 l2 o2 n2

def test9_text : List Char := ['b','a','a','l','l','o','o','n','n']
def test9_Expected : Nat := 1
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((MaximumNumberOfBalloons test1_text).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((MaximumNumberOfBalloons test2_text).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((MaximumNumberOfBalloons test3_text).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((MaximumNumberOfBalloons test4_text).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((MaximumNumberOfBalloons test5_text).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((MaximumNumberOfBalloons test6_text).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((MaximumNumberOfBalloons test7_text).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((MaximumNumberOfBalloons test8_text).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((MaximumNumberOfBalloons test9_text).run), DivM.res test9_Expected ]
end Assertions

section Pbt
velvet_plausible_test MaximumNumberOfBalloons (config := { maxMs := some 20000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000


prove_correct MaximumNumberOfBalloons by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at *); try (conv => congr <;> simp) ; try expose_names)
end Proof
