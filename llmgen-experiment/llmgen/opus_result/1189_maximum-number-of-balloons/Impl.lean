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
  let mut countB : Nat := 0
  let mut countA : Nat := 0
  let mut countL : Nat := 0
  let mut countO : Nat := 0
  let mut countN : Nat := 0
  let mut remaining := text
  while remaining.length > 0
    -- Invariant: countB plus remaining 'b' count equals total 'b' count
    -- Init: countB=0, remaining=text, so 0 + text.count 'b' = text.count 'b' ✓
    -- Preservation: head is removed from remaining; if head='b', countB increments, otherwise unchanged
    -- Sufficiency: at exit remaining=[], so countB = text.count 'b' (similarly for all counters)
    invariant "countB_inv" countB + remaining.count 'b' = text.count 'b'
    -- Invariant: countA plus remaining 'a' count equals total 'a' count
    invariant "countA_inv" countA + remaining.count 'a' = text.count 'a'
    -- Invariant: countL plus remaining 'l' count equals total 'l' count
    invariant "countL_inv" countL + remaining.count 'l' = text.count 'l'
    -- Invariant: countO plus remaining 'o' count equals total 'o' count
    invariant "countO_inv" countO + remaining.count 'o' = text.count 'o'
    -- Invariant: countN plus remaining 'n' count equals total 'n' count
    invariant "countN_inv" countN + remaining.count 'n' = text.count 'n'
    -- Decreasing: list length decreases each iteration (tail is shorter)
    decreasing remaining.length
  do
    let c := remaining.head!
    remaining := remaining.tail!
    if c = 'b' then
      countB := countB + 1
    else
      if c = 'a' then
        countA := countA + 1
      else
        if c = 'l' then
          countL := countL + 1
        else
          if c = 'o' then
            countO := countO + 1
          else
            if c = 'n' then
              countN := countN + 1
            else
              pure ()
  let halfL := countL / 2
  let halfO := countO / 2
  let mut minVal := countB
  if countA < minVal then
    minVal := countA
  if halfL < minVal then
    minVal := halfL
  if halfO < minVal then
    minVal := halfO
  if countN < minVal then
    minVal := countN
  return minVal
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

theorem goal_0
    (text : List Char)
    (countA : ℕ)
    (countB : ℕ)
    (countL : ℕ)
    (countN : ℕ)
    (countO : ℕ)
    (remaining : List Char)
    (invariant_countB_inv : countB + List.count 'b' remaining = List.count 'b' text)
    (invariant_countA_inv : countA + List.count 'a' remaining = List.count 'a' text)
    (invariant_countL_inv : countL + List.count 'l' remaining = List.count 'l' text)
    (invariant_countO_inv : countO + List.count 'o' remaining = List.count 'o' text)
    (invariant_countN_inv : countN + List.count 'n' remaining = List.count 'n' text)
    (if_pos_1 : remaining.head! = 'b')
    (if_pos : OfNat.ofNat 0 < remaining.length)
    : countB + OfNat.ofNat 1 + List.count 'b' remaining.tail! = List.count 'b' text := by
    have h0 : (OfNat.ofNat 0 : ℕ) = 0 := rfl
    have h1 : (OfNat.ofNat 1 : ℕ) = 1 := rfl
    rw [h0] at if_pos
    rw [h1]
    cases remaining with
    | nil => simp at if_pos
    | cons hd tl =>
      simp only [List.head!] at if_pos_1
      simp only [List.tail!]
      have hcount : List.count 'b' (hd :: tl) = List.count 'b' tl + 1 := by
        rw [if_pos_1]; exact List.count_cons_self
      omega

theorem goal_1
    (text : List Char)
    (countA : ℕ)
    (countB : ℕ)
    (countL : ℕ)
    (countN : ℕ)
    (countO : ℕ)
    (remaining : List Char)
    (invariant_countB_inv : countB + List.count 'b' remaining = List.count 'b' text)
    (invariant_countA_inv : countA + List.count 'a' remaining = List.count 'a' text)
    (invariant_countL_inv : countL + List.count 'l' remaining = List.count 'l' text)
    (invariant_countO_inv : countO + List.count 'o' remaining = List.count 'o' text)
    (invariant_countN_inv : countN + List.count 'n' remaining = List.count 'n' text)
    (if_pos_1 : remaining.head! = 'b')
    (if_pos : OfNat.ofNat 0 < remaining.length)
    : countA + List.count 'a' remaining.tail! = List.count 'a' text := by
    have hne : remaining ≠ [] := by
      intro h; simp [h] at if_pos
    -- tail! = tail for List when nonempty
    have htail : remaining.tail! = remaining.tail := by
      cases remaining with
      | nil => contradiction
      | cons h t => simp [List.tail!, List.tail]
    rw [htail, ← invariant_countA_inv]
    congr 1
    rw [← List.cons_head!_tail hne]
    simp [List.count_cons, if_pos_1]

theorem goal_2
    (text : List Char)
    (countA : ℕ)
    (countB : ℕ)
    (countL : ℕ)
    (countN : ℕ)
    (countO : ℕ)
    (remaining : List Char)
    (invariant_countB_inv : countB + List.count 'b' remaining = List.count 'b' text)
    (invariant_countA_inv : countA + List.count 'a' remaining = List.count 'a' text)
    (invariant_countL_inv : countL + List.count 'l' remaining = List.count 'l' text)
    (invariant_countO_inv : countO + List.count 'o' remaining = List.count 'o' text)
    (invariant_countN_inv : countN + List.count 'n' remaining = List.count 'n' text)
    (if_pos_1 : remaining.head! = 'b')
    (if_pos : OfNat.ofNat 0 < remaining.length)
    : countL + List.count 'l' remaining.tail! = List.count 'l' text := by
    have hne : remaining ≠ [] := by
      intro h; simp [h] at if_pos
    have key := List.cons_head!_tail hne (l := remaining)
    have hcount : List.count 'l' remaining = List.count 'l' remaining.tail := by
      conv_lhs => rw [← key]
      rw [if_pos_1]
      exact List.count_cons_of_ne (by decide)
    rw [show remaining.tail! = remaining.tail from by cases remaining with | nil => contradiction | cons _ _ => rfl]
    linarith

theorem goal_3
    (text : List Char)
    (countA : ℕ)
    (countB : ℕ)
    (countL : ℕ)
    (countN : ℕ)
    (countO : ℕ)
    (remaining : List Char)
    (invariant_countB_inv : countB + List.count 'b' remaining = List.count 'b' text)
    (invariant_countA_inv : countA + List.count 'a' remaining = List.count 'a' text)
    (invariant_countL_inv : countL + List.count 'l' remaining = List.count 'l' text)
    (invariant_countO_inv : countO + List.count 'o' remaining = List.count 'o' text)
    (invariant_countN_inv : countN + List.count 'n' remaining = List.count 'n' text)
    (if_pos_1 : remaining.head! = 'b')
    (if_pos : OfNat.ofNat 0 < remaining.length)
    : countO + List.count 'o' remaining.tail! = List.count 'o' text := by
    have hne : remaining ≠ [] := List.length_pos_iff.mp if_pos
    have hcons : remaining.head! :: remaining.tail = remaining := List.cons_head!_tail hne
    rw [← invariant_countO_inv]
    have : remaining.tail! = remaining.tail := by
      cases remaining with
      | nil => contradiction
      | cons h t => simp [List.tail!, List.tail]
    rw [this]
    have : List.count 'o' remaining = List.count 'o' (remaining.head! :: remaining.tail) := by
      rw [hcons]
    rw [this]
    rw [if_pos_1]
    simp [List.count_cons_of_ne]

theorem goal_4
    (text : List Char)
    (countA : ℕ)
    (countB : ℕ)
    (countL : ℕ)
    (countN : ℕ)
    (countO : ℕ)
    (remaining : List Char)
    (invariant_countB_inv : countB + List.count 'b' remaining = List.count 'b' text)
    (invariant_countA_inv : countA + List.count 'a' remaining = List.count 'a' text)
    (invariant_countL_inv : countL + List.count 'l' remaining = List.count 'l' text)
    (invariant_countO_inv : countO + List.count 'o' remaining = List.count 'o' text)
    (invariant_countN_inv : countN + List.count 'n' remaining = List.count 'n' text)
    (if_pos_1 : remaining.head! = 'b')
    (if_pos : OfNat.ofNat 0 < remaining.length)
    : countN + List.count 'n' remaining.tail! = List.count 'n' text := by
    have hne : remaining ≠ [] := by
      intro h; simp [h] at if_pos
    obtain ⟨hd, tl, rfl⟩ := List.exists_cons_of_ne_nil hne
    simp [List.head!_cons] at if_pos_1
    subst if_pos_1
    simp [List.tail!_cons, List.count_cons] at invariant_countN_inv ⊢
    exact invariant_countN_inv

theorem goal_5
    (text : List Char)
    (countA : ℕ)
    (countB : ℕ)
    (countL : ℕ)
    (countN : ℕ)
    (countO : ℕ)
    (remaining : List Char)
    (invariant_countB_inv : countB + List.count 'b' remaining = List.count 'b' text)
    (invariant_countA_inv : countA + List.count 'a' remaining = List.count 'a' text)
    (invariant_countL_inv : countL + List.count 'l' remaining = List.count 'l' text)
    (invariant_countO_inv : countO + List.count 'o' remaining = List.count 'o' text)
    (invariant_countN_inv : countN + List.count 'n' remaining = List.count 'n' text)
    (if_pos_1 : remaining.head! = 'b')
    (if_pos : OfNat.ofNat 0 < remaining.length)
    : remaining.tail!.length < remaining.length := by
    cases remaining with
    | nil => simp at if_pos
    | cons h t => simp [List.tail!, List.length_cons]

theorem goal_6
    (text : List Char)
    (countA : ℕ)
    (countB : ℕ)
    (countL : ℕ)
    (countN : ℕ)
    (countO : ℕ)
    (remaining : List Char)
    (invariant_countB_inv : countB + List.count 'b' remaining = List.count 'b' text)
    (invariant_countA_inv : countA + List.count 'a' remaining = List.count 'a' text)
    (invariant_countL_inv : countL + List.count 'l' remaining = List.count 'l' text)
    (invariant_countO_inv : countO + List.count 'o' remaining = List.count 'o' text)
    (invariant_countN_inv : countN + List.count 'n' remaining = List.count 'n' text)
    (if_neg : ¬remaining.head! = 'b')
    (if_pos_1 : remaining.head! = 'a')
    (if_pos : OfNat.ofNat 0 < remaining.length)
    : countB + List.count 'b' remaining.tail! = List.count 'b' text := by
    cases remaining with
    | nil => simp at if_pos
    | cons hd tl =>
      simp [List.head!, List.tail!] at *
      rw [List.count_cons] at invariant_countB_inv
      simp [if_neg] at invariant_countB_inv
      exact invariant_countB_inv

theorem goal_7
    (text : List Char)
    (countA : ℕ)
    (countB : ℕ)
    (countL : ℕ)
    (countN : ℕ)
    (countO : ℕ)
    (remaining : List Char)
    (invariant_countB_inv : countB + List.count 'b' remaining = List.count 'b' text)
    (invariant_countA_inv : countA + List.count 'a' remaining = List.count 'a' text)
    (invariant_countL_inv : countL + List.count 'l' remaining = List.count 'l' text)
    (invariant_countO_inv : countO + List.count 'o' remaining = List.count 'o' text)
    (invariant_countN_inv : countN + List.count 'n' remaining = List.count 'n' text)
    (if_neg : ¬remaining.head! = 'b')
    (if_pos_1 : remaining.head! = 'a')
    (if_pos : OfNat.ofNat 0 < remaining.length)
    : countA + OfNat.ofNat 1 + List.count 'a' remaining.tail! = List.count 'a' text := by
    have h0 : (OfNat.ofNat 0 : ℕ) = 0 := rfl
    have h1 : (OfNat.ofNat 1 : ℕ) = 1 := rfl
    rw [h0] at if_pos
    rw [h1]
    match remaining with
    | [] => simp at if_pos
    | h :: t =>
      simp only [List.head!, List.tail!] at *
      subst if_pos_1
      rw [List.count_cons_self] at invariant_countA_inv
      omega

theorem goal_8
    (text : List Char)
    (countA : ℕ)
    (countB : ℕ)
    (countL : ℕ)
    (countN : ℕ)
    (countO : ℕ)
    (remaining : List Char)
    (invariant_countB_inv : countB + List.count 'b' remaining = List.count 'b' text)
    (invariant_countA_inv : countA + List.count 'a' remaining = List.count 'a' text)
    (invariant_countL_inv : countL + List.count 'l' remaining = List.count 'l' text)
    (invariant_countO_inv : countO + List.count 'o' remaining = List.count 'o' text)
    (invariant_countN_inv : countN + List.count 'n' remaining = List.count 'n' text)
    (if_neg : ¬remaining.head! = 'b')
    (if_pos_1 : remaining.head! = 'a')
    (if_pos : OfNat.ofNat 0 < remaining.length)
    : countL + List.count 'l' remaining.tail! = List.count 'l' text := by
    have hne : remaining ≠ [] := by
      intro h; simp [h] at if_pos
    obtain ⟨hd, tl, rfl⟩ := List.exists_cons_of_ne_nil hne
    simp [List.head!, List.tail!] at if_pos_1 ⊢
    simp [List.head!] at if_neg
    rw [List.count_cons_of_ne] at invariant_countL_inv
    · exact invariant_countL_inv
    · intro h; rw [h] at if_pos_1; exact absurd if_pos_1 (by decide)

theorem goal_9
    (text : List Char)
    (countA : ℕ)
    (countB : ℕ)
    (countL : ℕ)
    (countN : ℕ)
    (countO : ℕ)
    (remaining : List Char)
    (invariant_countB_inv : countB + List.count 'b' remaining = List.count 'b' text)
    (invariant_countA_inv : countA + List.count 'a' remaining = List.count 'a' text)
    (invariant_countL_inv : countL + List.count 'l' remaining = List.count 'l' text)
    (invariant_countO_inv : countO + List.count 'o' remaining = List.count 'o' text)
    (invariant_countN_inv : countN + List.count 'n' remaining = List.count 'n' text)
    (if_neg : ¬remaining.head! = 'b')
    (if_pos_1 : remaining.head! = 'a')
    (if_pos : OfNat.ofNat 0 < remaining.length)
    : countO + List.count 'o' remaining.tail! = List.count 'o' text := by
    cases remaining with
    | nil => simp at if_pos
    | cons h t =>
      simp [List.head!, List.tail!] at *
      simp [List.count_cons_of_ne (show h ≠ 'o' by rw [if_pos_1]; decide)] at invariant_countO_inv
      exact invariant_countO_inv

theorem goal_10
    (text : List Char)
    (countA : ℕ)
    (countB : ℕ)
    (countL : ℕ)
    (countN : ℕ)
    (countO : ℕ)
    (remaining : List Char)
    (invariant_countB_inv : countB + List.count 'b' remaining = List.count 'b' text)
    (invariant_countA_inv : countA + List.count 'a' remaining = List.count 'a' text)
    (invariant_countL_inv : countL + List.count 'l' remaining = List.count 'l' text)
    (invariant_countO_inv : countO + List.count 'o' remaining = List.count 'o' text)
    (invariant_countN_inv : countN + List.count 'n' remaining = List.count 'n' text)
    (if_neg : ¬remaining.head! = 'b')
    (if_pos_1 : remaining.head! = 'a')
    (if_pos : OfNat.ofNat 0 < remaining.length)
    : countN + List.count 'n' remaining.tail! = List.count 'n' text := by
    have hne : remaining ≠ [] := List.length_pos_iff_ne_nil.mp if_pos
    obtain ⟨hd, tl, rfl⟩ := List.exists_cons_of_ne_nil hne
    simp [List.head!_cons] at if_pos_1
    subst if_pos_1
    simp [List.tail!_cons, List.count_cons] at invariant_countN_inv ⊢
    exact invariant_countN_inv

theorem goal_11
    (text : List Char)
    (countA : ℕ)
    (countB : ℕ)
    (countL : ℕ)
    (countN : ℕ)
    (countO : ℕ)
    (remaining : List Char)
    (invariant_countB_inv : countB + List.count 'b' remaining = List.count 'b' text)
    (invariant_countA_inv : countA + List.count 'a' remaining = List.count 'a' text)
    (invariant_countL_inv : countL + List.count 'l' remaining = List.count 'l' text)
    (invariant_countO_inv : countO + List.count 'o' remaining = List.count 'o' text)
    (invariant_countN_inv : countN + List.count 'n' remaining = List.count 'n' text)
    (if_neg : ¬remaining.head! = 'b')
    (if_pos_1 : remaining.head! = 'a')
    (if_pos : OfNat.ofNat 0 < remaining.length)
    : remaining.tail!.length < remaining.length := by
    obtain ⟨h, t, rfl⟩ := List.exists_cons_of_length_pos if_pos
    simp [List.tail!]

theorem goal_12
    (text : List Char)
    (countA : ℕ)
    (countB : ℕ)
    (countL : ℕ)
    (countN : ℕ)
    (countO : ℕ)
    (remaining : List Char)
    (invariant_countB_inv : countB + List.count 'b' remaining = List.count 'b' text)
    (invariant_countA_inv : countA + List.count 'a' remaining = List.count 'a' text)
    (invariant_countL_inv : countL + List.count 'l' remaining = List.count 'l' text)
    (invariant_countO_inv : countO + List.count 'o' remaining = List.count 'o' text)
    (invariant_countN_inv : countN + List.count 'n' remaining = List.count 'n' text)
    (if_neg : ¬remaining.head! = 'b')
    (if_neg_1 : ¬remaining.head! = 'a')
    (if_pos_1 : remaining.head! = 'l')
    (if_pos : OfNat.ofNat 0 < remaining.length)
    : countB + List.count 'b' remaining.tail! = List.count 'b' text := by
    have hne : remaining ≠ [] := List.ne_nil_of_length_pos if_pos
    obtain ⟨hd, tl, rfl⟩ : ∃ hd tl, remaining = hd :: tl := by
      cases remaining with
      | nil => contradiction
      | cons h t => exact ⟨h, t, rfl⟩
    simp [List.head!, List.tail!] at *
    have hne_b : hd ≠ 'b' := if_neg
    rw [List.count_cons_of_ne hne_b] at invariant_countB_inv
    exact invariant_countB_inv

theorem goal_13
    (text : List Char)
    (countA : ℕ)
    (countB : ℕ)
    (countL : ℕ)
    (countN : ℕ)
    (countO : ℕ)
    (remaining : List Char)
    (invariant_countB_inv : countB + List.count 'b' remaining = List.count 'b' text)
    (invariant_countA_inv : countA + List.count 'a' remaining = List.count 'a' text)
    (invariant_countL_inv : countL + List.count 'l' remaining = List.count 'l' text)
    (invariant_countO_inv : countO + List.count 'o' remaining = List.count 'o' text)
    (invariant_countN_inv : countN + List.count 'n' remaining = List.count 'n' text)
    (if_neg : ¬remaining.head! = 'b')
    (if_neg_1 : ¬remaining.head! = 'a')
    (if_pos_1 : remaining.head! = 'l')
    (if_pos : OfNat.ofNat 0 < remaining.length)
    : countA + List.count 'a' remaining.tail! = List.count 'a' text := by
    have hne : remaining ≠ [] := by
      intro h; simp [h] at if_pos
    have : remaining.head! :: remaining.tail = remaining := List.cons_head!_tail hne
    have hcount : List.count 'a' remaining = List.count 'a' (remaining.head! :: remaining.tail) := by
      rw [this]
    have hne_char : remaining.head! ≠ 'a' := if_neg_1
    rw [List.count_cons_of_ne hne_char] at hcount
    show countA + List.count 'a' remaining.tail! = List.count 'a' text
    have : remaining.tail! = remaining.tail := by
      cases remaining with
      | nil => contradiction
      | cons h t => simp [List.tail!, List.tail]
    rw [this]
    linarith

theorem goal_14
    (text : List Char)
    (countA : ℕ)
    (countB : ℕ)
    (countL : ℕ)
    (countN : ℕ)
    (countO : ℕ)
    (remaining : List Char)
    (invariant_countB_inv : countB + List.count 'b' remaining = List.count 'b' text)
    (invariant_countA_inv : countA + List.count 'a' remaining = List.count 'a' text)
    (invariant_countL_inv : countL + List.count 'l' remaining = List.count 'l' text)
    (invariant_countO_inv : countO + List.count 'o' remaining = List.count 'o' text)
    (invariant_countN_inv : countN + List.count 'n' remaining = List.count 'n' text)
    (if_neg : ¬remaining.head! = 'b')
    (if_neg_1 : ¬remaining.head! = 'a')
    (if_pos_1 : remaining.head! = 'l')
    (if_pos : OfNat.ofNat 0 < remaining.length)
    : countL + OfNat.ofNat 1 + List.count 'l' remaining.tail! = List.count 'l' text := by
    show countL + 1 + List.count 'l' remaining.tail! = List.count 'l' text
    have hlen : 0 < remaining.length := if_pos
    obtain ⟨h, t, rfl⟩ := List.exists_cons_of_length_pos hlen
    simp [List.head!_cons] at if_pos_1
    subst if_pos_1
    simp only [List.tail!_cons]
    have : List.count 'l' ('l' :: t) = List.count 'l' t + 1 := List.count_cons_self
    omega

theorem goal_15
    (text : List Char)
    (countA : ℕ)
    (countB : ℕ)
    (countL : ℕ)
    (countN : ℕ)
    (countO : ℕ)
    (remaining : List Char)
    (invariant_countB_inv : countB + List.count 'b' remaining = List.count 'b' text)
    (invariant_countA_inv : countA + List.count 'a' remaining = List.count 'a' text)
    (invariant_countL_inv : countL + List.count 'l' remaining = List.count 'l' text)
    (invariant_countO_inv : countO + List.count 'o' remaining = List.count 'o' text)
    (invariant_countN_inv : countN + List.count 'n' remaining = List.count 'n' text)
    (if_neg : ¬remaining.head! = 'b')
    (if_neg_1 : ¬remaining.head! = 'a')
    (if_pos_1 : remaining.head! = 'l')
    (if_pos : OfNat.ofNat 0 < remaining.length)
    : countO + List.count 'o' remaining.tail! = List.count 'o' text := by
    have hne : remaining ≠ [] := List.ne_nil_of_length_pos if_pos
    have hcons : remaining = remaining.head hne :: remaining.tail := by exact (List.head_cons_tail remaining hne).symm
    have htail_eq : remaining.tail! = remaining.tail := by
      cases remaining with
      | nil => contradiction
      | cons h t => simp [List.tail!, List.tail]
    rw [htail_eq]
    have hhead_eq : remaining.head! = remaining.head hne := by
      cases remaining with
      | nil => contradiction
      | cons h t => simp [List.head!, List.head]
    have hhead_is_l : remaining.head hne = 'l' := by rw [← hhead_eq]; exact if_pos_1
    rw [← invariant_countO_inv]
    congr 1
    conv_rhs => rw [hcons]
    simp [List.count_cons, hhead_is_l]

theorem goal_16
    (text : List Char)
    (countA : ℕ)
    (countB : ℕ)
    (countL : ℕ)
    (countN : ℕ)
    (countO : ℕ)
    (remaining : List Char)
    (invariant_countB_inv : countB + List.count 'b' remaining = List.count 'b' text)
    (invariant_countA_inv : countA + List.count 'a' remaining = List.count 'a' text)
    (invariant_countL_inv : countL + List.count 'l' remaining = List.count 'l' text)
    (invariant_countO_inv : countO + List.count 'o' remaining = List.count 'o' text)
    (invariant_countN_inv : countN + List.count 'n' remaining = List.count 'n' text)
    (if_neg : ¬remaining.head! = 'b')
    (if_neg_1 : ¬remaining.head! = 'a')
    (if_pos_1 : remaining.head! = 'l')
    (if_pos : OfNat.ofNat 0 < remaining.length)
    : countN + List.count 'n' remaining.tail! = List.count 'n' text := by
    have hne : remaining ≠ [] := by
      intro h; simp [h] at if_pos
    obtain ⟨hd, tl, rfl⟩ : ∃ hd tl, remaining = hd :: tl := by
      exact ⟨remaining.head hne, remaining.tail, (List.head_cons_tail remaining hne).symm⟩
    simp [List.tail!] at *
    rw [List.count_cons_of_ne] at invariant_countN_inv
    · exact invariant_countN_inv
    · rw [if_pos_1]; decide

theorem goal_17
    (text : List Char)
    (countA : ℕ)
    (countB : ℕ)
    (countL : ℕ)
    (countN : ℕ)
    (countO : ℕ)
    (remaining : List Char)
    (invariant_countB_inv : countB + List.count 'b' remaining = List.count 'b' text)
    (invariant_countA_inv : countA + List.count 'a' remaining = List.count 'a' text)
    (invariant_countL_inv : countL + List.count 'l' remaining = List.count 'l' text)
    (invariant_countO_inv : countO + List.count 'o' remaining = List.count 'o' text)
    (invariant_countN_inv : countN + List.count 'n' remaining = List.count 'n' text)
    (if_neg : ¬remaining.head! = 'b')
    (if_neg_1 : ¬remaining.head! = 'a')
    (if_pos_1 : remaining.head! = 'l')
    (if_pos : OfNat.ofNat 0 < remaining.length)
    : remaining.tail!.length < remaining.length := by
    match remaining with
    | [] => simp at if_pos
    | h :: t => simp [List.tail!_cons]

theorem goal_18
    (text : List Char)
    (countA : ℕ)
    (countB : ℕ)
    (countL : ℕ)
    (countN : ℕ)
    (countO : ℕ)
    (remaining : List Char)
    (invariant_countB_inv : countB + List.count 'b' remaining = List.count 'b' text)
    (invariant_countA_inv : countA + List.count 'a' remaining = List.count 'a' text)
    (invariant_countL_inv : countL + List.count 'l' remaining = List.count 'l' text)
    (invariant_countO_inv : countO + List.count 'o' remaining = List.count 'o' text)
    (invariant_countN_inv : countN + List.count 'n' remaining = List.count 'n' text)
    (if_neg : ¬remaining.head! = 'b')
    (if_neg_1 : ¬remaining.head! = 'a')
    (if_neg_2 : ¬remaining.head! = 'l')
    (if_pos_1 : remaining.head! = 'o')
    (if_pos : OfNat.ofNat 0 < remaining.length)
    : countB + List.count 'b' remaining.tail! = List.count 'b' text := by
    match remaining, if_pos with
    | a :: rest, _ =>
      simp [List.head!_cons] at if_pos_1
      subst if_pos_1
      simp [List.tail!_cons, List.count_cons] at invariant_countB_inv ⊢
      exact invariant_countB_inv

theorem goal_19
    (text : List Char)
    (countA : ℕ)
    (countB : ℕ)
    (countL : ℕ)
    (countN : ℕ)
    (countO : ℕ)
    (remaining : List Char)
    (invariant_countB_inv : countB + List.count 'b' remaining = List.count 'b' text)
    (invariant_countA_inv : countA + List.count 'a' remaining = List.count 'a' text)
    (invariant_countL_inv : countL + List.count 'l' remaining = List.count 'l' text)
    (invariant_countO_inv : countO + List.count 'o' remaining = List.count 'o' text)
    (invariant_countN_inv : countN + List.count 'n' remaining = List.count 'n' text)
    (if_neg : ¬remaining.head! = 'b')
    (if_neg_1 : ¬remaining.head! = 'a')
    (if_neg_2 : ¬remaining.head! = 'l')
    (if_pos_1 : remaining.head! = 'o')
    (if_pos : OfNat.ofNat 0 < remaining.length)
    : countA + List.count 'a' remaining.tail! = List.count 'a' text := by
    rw [← invariant_countA_inv]
    congr 1
    cases remaining with
    | nil => simp at if_pos
    | cons h t =>
      simp [List.tail!, List.head!] at if_neg_1 ⊢
      rw [List.count_cons_of_ne if_neg_1]

theorem goal_20
    (text : List Char)
    (countA : ℕ)
    (countB : ℕ)
    (countL : ℕ)
    (countN : ℕ)
    (countO : ℕ)
    (remaining : List Char)
    (invariant_countB_inv : countB + List.count 'b' remaining = List.count 'b' text)
    (invariant_countA_inv : countA + List.count 'a' remaining = List.count 'a' text)
    (invariant_countL_inv : countL + List.count 'l' remaining = List.count 'l' text)
    (invariant_countO_inv : countO + List.count 'o' remaining = List.count 'o' text)
    (invariant_countN_inv : countN + List.count 'n' remaining = List.count 'n' text)
    (if_neg : ¬remaining.head! = 'b')
    (if_neg_1 : ¬remaining.head! = 'a')
    (if_neg_2 : ¬remaining.head! = 'l')
    (if_pos_1 : remaining.head! = 'o')
    (if_pos : OfNat.ofNat 0 < remaining.length)
    : countL + List.count 'l' remaining.tail! = List.count 'l' text := by
    rw [← invariant_countL_inv]
    congr 1
    match remaining, if_pos, if_neg_2, if_pos_1 with
    | h :: t, _, hne, hhead =>
      simp [List.head!, List.tail!] at hne hhead ⊢
      rw [List.count_cons_of_ne]
      exact fun heq => hne heq

theorem goal_21
    (text : List Char)
    (require_1 : True)
    (countA : ℕ)
    (countB : ℕ)
    (countL : ℕ)
    (countN : ℕ)
    (countO : ℕ)
    (remaining : List Char)
    (invariant_countB_inv : countB + List.count 'b' remaining = List.count 'b' text)
    (invariant_countA_inv : countA + List.count 'a' remaining = List.count 'a' text)
    (invariant_countL_inv : countL + List.count 'l' remaining = List.count 'l' text)
    (invariant_countO_inv : countO + List.count 'o' remaining = List.count 'o' text)
    (invariant_countN_inv : countN + List.count 'n' remaining = List.count 'n' text)
    (if_neg : ¬remaining.head! = 'b')
    (if_neg_1 : ¬remaining.head! = 'a')
    (if_neg_2 : ¬remaining.head! = 'l')
    (if_pos_1 : remaining.head! = 'o')
    (if_pos : OfNat.ofNat 0 < remaining.length)
    : countO + OfNat.ofNat 1 + List.count 'o' remaining.tail! = List.count 'o' text := by
    sorry



theorem goal_21
    (text : List Char)
    (require_1 : True)
    (countA : ℕ)
    (countB : ℕ)
    (countL : ℕ)
    (countN : ℕ)
    (countO : ℕ)
    (remaining : List Char)
    (invariant_countB_inv : countB + List.count 'b' remaining = List.count 'b' text)
    (invariant_countA_inv : countA + List.count 'a' remaining = List.count 'a' text)
    (invariant_countL_inv : countL + List.count 'l' remaining = List.count 'l' text)
    (invariant_countO_inv : countO + List.count 'o' remaining = List.count 'o' text)
    (invariant_countN_inv : countN + List.count 'n' remaining = List.count 'n' text)
    (if_neg : ¬remaining.head! = 'b')
    (if_neg_1 : ¬remaining.head! = 'a')
    (if_neg_2 : ¬remaining.head! = 'l')
    (if_pos_1 : remaining.head! = 'o')
    (if_pos : OfNat.ofNat 0 < remaining.length)
    : countO + OfNat.ofNat 1 + List.count 'o' remaining.tail! = List.count 'o' text := by
    sorry

theorem goal_22
    (text : List Char)
    (require_1 : True)
    (countA : ℕ)
    (countB : ℕ)
    (countL : ℕ)
    (countN : ℕ)
    (countO : ℕ)
    (remaining : List Char)
    (invariant_countB_inv : countB + List.count 'b' remaining = List.count 'b' text)
    (invariant_countA_inv : countA + List.count 'a' remaining = List.count 'a' text)
    (invariant_countL_inv : countL + List.count 'l' remaining = List.count 'l' text)
    (invariant_countO_inv : countO + List.count 'o' remaining = List.count 'o' text)
    (invariant_countN_inv : countN + List.count 'n' remaining = List.count 'n' text)
    (if_neg : ¬remaining.head! = 'b')
    (if_neg_1 : ¬remaining.head! = 'a')
    (if_neg_2 : ¬remaining.head! = 'l')
    (if_pos_1 : remaining.head! = 'o')
    (if_pos : OfNat.ofNat 0 < remaining.length)
    : countN + List.count 'n' remaining.tail! = List.count 'n' text := by
    sorry

theorem goal_23
    (text : List Char)
    (require_1 : True)
    (countA : ℕ)
    (countB : ℕ)
    (countL : ℕ)
    (countN : ℕ)
    (countO : ℕ)
    (remaining : List Char)
    (invariant_countB_inv : countB + List.count 'b' remaining = List.count 'b' text)
    (invariant_countA_inv : countA + List.count 'a' remaining = List.count 'a' text)
    (invariant_countL_inv : countL + List.count 'l' remaining = List.count 'l' text)
    (invariant_countO_inv : countO + List.count 'o' remaining = List.count 'o' text)
    (invariant_countN_inv : countN + List.count 'n' remaining = List.count 'n' text)
    (if_neg : ¬remaining.head! = 'b')
    (if_neg_1 : ¬remaining.head! = 'a')
    (if_neg_2 : ¬remaining.head! = 'l')
    (if_pos_1 : remaining.head! = 'o')
    (if_pos : OfNat.ofNat 0 < remaining.length)
    : remaining.tail!.length < remaining.length := by
    sorry

theorem goal_24
    (text : List Char)
    (require_1 : True)
    (countA : ℕ)
    (countB : ℕ)
    (countL : ℕ)
    (countN : ℕ)
    (countO : ℕ)
    (remaining : List Char)
    (invariant_countB_inv : countB + List.count 'b' remaining = List.count 'b' text)
    (invariant_countA_inv : countA + List.count 'a' remaining = List.count 'a' text)
    (invariant_countL_inv : countL + List.count 'l' remaining = List.count 'l' text)
    (invariant_countO_inv : countO + List.count 'o' remaining = List.count 'o' text)
    (invariant_countN_inv : countN + List.count 'n' remaining = List.count 'n' text)
    (if_neg : ¬remaining.head! = 'b')
    (if_neg_1 : ¬remaining.head! = 'a')
    (if_neg_2 : ¬remaining.head! = 'l')
    (if_neg_3 : ¬remaining.head! = 'o')
    (if_pos_1 : remaining.head! = 'n')
    (if_pos : OfNat.ofNat 0 < remaining.length)
    : countB + List.count 'b' remaining.tail! = List.count 'b' text := by
    sorry

theorem goal_25
    (text : List Char)
    (require_1 : True)
    (countA : ℕ)
    (countB : ℕ)
    (countL : ℕ)
    (countN : ℕ)
    (countO : ℕ)
    (remaining : List Char)
    (invariant_countB_inv : countB + List.count 'b' remaining = List.count 'b' text)
    (invariant_countA_inv : countA + List.count 'a' remaining = List.count 'a' text)
    (invariant_countL_inv : countL + List.count 'l' remaining = List.count 'l' text)
    (invariant_countO_inv : countO + List.count 'o' remaining = List.count 'o' text)
    (invariant_countN_inv : countN + List.count 'n' remaining = List.count 'n' text)
    (if_neg : ¬remaining.head! = 'b')
    (if_neg_1 : ¬remaining.head! = 'a')
    (if_neg_2 : ¬remaining.head! = 'l')
    (if_neg_3 : ¬remaining.head! = 'o')
    (if_pos_1 : remaining.head! = 'n')
    (if_pos : OfNat.ofNat 0 < remaining.length)
    : countA + List.count 'a' remaining.tail! = List.count 'a' text := by
    sorry

theorem goal_26
    (text : List Char)
    (require_1 : True)
    (countA : ℕ)
    (countB : ℕ)
    (countL : ℕ)
    (countN : ℕ)
    (countO : ℕ)
    (remaining : List Char)
    (invariant_countB_inv : countB + List.count 'b' remaining = List.count 'b' text)
    (invariant_countA_inv : countA + List.count 'a' remaining = List.count 'a' text)
    (invariant_countL_inv : countL + List.count 'l' remaining = List.count 'l' text)
    (invariant_countO_inv : countO + List.count 'o' remaining = List.count 'o' text)
    (invariant_countN_inv : countN + List.count 'n' remaining = List.count 'n' text)
    (if_neg : ¬remaining.head! = 'b')
    (if_neg_1 : ¬remaining.head! = 'a')
    (if_neg_2 : ¬remaining.head! = 'l')
    (if_neg_3 : ¬remaining.head! = 'o')
    (if_pos_1 : remaining.head! = 'n')
    (if_pos : OfNat.ofNat 0 < remaining.length)
    : countL + List.count 'l' remaining.tail! = List.count 'l' text := by
    sorry

theorem goal_27
    (text : List Char)
    (require_1 : True)
    (countA : ℕ)
    (countB : ℕ)
    (countL : ℕ)
    (countN : ℕ)
    (countO : ℕ)
    (remaining : List Char)
    (invariant_countB_inv : countB + List.count 'b' remaining = List.count 'b' text)
    (invariant_countA_inv : countA + List.count 'a' remaining = List.count 'a' text)
    (invariant_countL_inv : countL + List.count 'l' remaining = List.count 'l' text)
    (invariant_countO_inv : countO + List.count 'o' remaining = List.count 'o' text)
    (invariant_countN_inv : countN + List.count 'n' remaining = List.count 'n' text)
    (if_neg : ¬remaining.head! = 'b')
    (if_neg_1 : ¬remaining.head! = 'a')
    (if_neg_2 : ¬remaining.head! = 'l')
    (if_neg_3 : ¬remaining.head! = 'o')
    (if_pos_1 : remaining.head! = 'n')
    (if_pos : OfNat.ofNat 0 < remaining.length)
    : countO + List.count 'o' remaining.tail! = List.count 'o' text := by
    sorry

theorem goal_28
    (text : List Char)
    (require_1 : True)
    (countA : ℕ)
    (countB : ℕ)
    (countL : ℕ)
    (countN : ℕ)
    (countO : ℕ)
    (remaining : List Char)
    (invariant_countB_inv : countB + List.count 'b' remaining = List.count 'b' text)
    (invariant_countA_inv : countA + List.count 'a' remaining = List.count 'a' text)
    (invariant_countL_inv : countL + List.count 'l' remaining = List.count 'l' text)
    (invariant_countO_inv : countO + List.count 'o' remaining = List.count 'o' text)
    (invariant_countN_inv : countN + List.count 'n' remaining = List.count 'n' text)
    (if_neg : ¬remaining.head! = 'b')
    (if_neg_1 : ¬remaining.head! = 'a')
    (if_neg_2 : ¬remaining.head! = 'l')
    (if_neg_3 : ¬remaining.head! = 'o')
    (if_pos_1 : remaining.head! = 'n')
    (if_pos : OfNat.ofNat 0 < remaining.length)
    : countN + OfNat.ofNat 1 + List.count 'n' remaining.tail! = List.count 'n' text := by
    sorry

theorem goal_29
    (text : List Char)
    (require_1 : True)
    (countA : ℕ)
    (countB : ℕ)
    (countL : ℕ)
    (countN : ℕ)
    (countO : ℕ)
    (remaining : List Char)
    (invariant_countB_inv : countB + List.count 'b' remaining = List.count 'b' text)
    (invariant_countA_inv : countA + List.count 'a' remaining = List.count 'a' text)
    (invariant_countL_inv : countL + List.count 'l' remaining = List.count 'l' text)
    (invariant_countO_inv : countO + List.count 'o' remaining = List.count 'o' text)
    (invariant_countN_inv : countN + List.count 'n' remaining = List.count 'n' text)
    (if_neg : ¬remaining.head! = 'b')
    (if_neg_1 : ¬remaining.head! = 'a')
    (if_neg_2 : ¬remaining.head! = 'l')
    (if_neg_3 : ¬remaining.head! = 'o')
    (if_pos_1 : remaining.head! = 'n')
    (if_pos : OfNat.ofNat 0 < remaining.length)
    : remaining.tail!.length < remaining.length := by
    sorry

theorem goal_30
    (text : List Char)
    (require_1 : True)
    (countA : ℕ)
    (countB : ℕ)
    (countL : ℕ)
    (countN : ℕ)
    (countO : ℕ)
    (remaining : List Char)
    (invariant_countB_inv : countB + List.count 'b' remaining = List.count 'b' text)
    (invariant_countA_inv : countA + List.count 'a' remaining = List.count 'a' text)
    (invariant_countL_inv : countL + List.count 'l' remaining = List.count 'l' text)
    (invariant_countO_inv : countO + List.count 'o' remaining = List.count 'o' text)
    (invariant_countN_inv : countN + List.count 'n' remaining = List.count 'n' text)
    (if_neg : ¬remaining.head! = 'b')
    (if_neg_1 : ¬remaining.head! = 'a')
    (if_neg_2 : ¬remaining.head! = 'l')
    (if_neg_3 : ¬remaining.head! = 'o')
    (if_neg_4 : ¬remaining.head! = 'n')
    (if_pos : OfNat.ofNat 0 < remaining.length)
    : countB + List.count 'b' remaining.tail! = List.count 'b' text := by
    sorry

theorem goal_31
    (text : List Char)
    (require_1 : True)
    (countA : ℕ)
    (countB : ℕ)
    (countL : ℕ)
    (countN : ℕ)
    (countO : ℕ)
    (remaining : List Char)
    (invariant_countB_inv : countB + List.count 'b' remaining = List.count 'b' text)
    (invariant_countA_inv : countA + List.count 'a' remaining = List.count 'a' text)
    (invariant_countL_inv : countL + List.count 'l' remaining = List.count 'l' text)
    (invariant_countO_inv : countO + List.count 'o' remaining = List.count 'o' text)
    (invariant_countN_inv : countN + List.count 'n' remaining = List.count 'n' text)
    (if_neg : ¬remaining.head! = 'b')
    (if_neg_1 : ¬remaining.head! = 'a')
    (if_neg_2 : ¬remaining.head! = 'l')
    (if_neg_3 : ¬remaining.head! = 'o')
    (if_neg_4 : ¬remaining.head! = 'n')
    (if_pos : OfNat.ofNat 0 < remaining.length)
    : countA + List.count 'a' remaining.tail! = List.count 'a' text := by
    sorry

theorem goal_32
    (text : List Char)
    (require_1 : True)
    (countA : ℕ)
    (countB : ℕ)
    (countL : ℕ)
    (countN : ℕ)
    (countO : ℕ)
    (remaining : List Char)
    (invariant_countB_inv : countB + List.count 'b' remaining = List.count 'b' text)
    (invariant_countA_inv : countA + List.count 'a' remaining = List.count 'a' text)
    (invariant_countL_inv : countL + List.count 'l' remaining = List.count 'l' text)
    (invariant_countO_inv : countO + List.count 'o' remaining = List.count 'o' text)
    (invariant_countN_inv : countN + List.count 'n' remaining = List.count 'n' text)
    (if_neg : ¬remaining.head! = 'b')
    (if_neg_1 : ¬remaining.head! = 'a')
    (if_neg_2 : ¬remaining.head! = 'l')
    (if_neg_3 : ¬remaining.head! = 'o')
    (if_neg_4 : ¬remaining.head! = 'n')
    (if_pos : OfNat.ofNat 0 < remaining.length)
    : countL + List.count 'l' remaining.tail! = List.count 'l' text := by
    sorry

theorem goal_33
    (text : List Char)
    (require_1 : True)
    (countA : ℕ)
    (countB : ℕ)
    (countL : ℕ)
    (countN : ℕ)
    (countO : ℕ)
    (remaining : List Char)
    (invariant_countB_inv : countB + List.count 'b' remaining = List.count 'b' text)
    (invariant_countA_inv : countA + List.count 'a' remaining = List.count 'a' text)
    (invariant_countL_inv : countL + List.count 'l' remaining = List.count 'l' text)
    (invariant_countO_inv : countO + List.count 'o' remaining = List.count 'o' text)
    (invariant_countN_inv : countN + List.count 'n' remaining = List.count 'n' text)
    (if_neg : ¬remaining.head! = 'b')
    (if_neg_1 : ¬remaining.head! = 'a')
    (if_neg_2 : ¬remaining.head! = 'l')
    (if_neg_3 : ¬remaining.head! = 'o')
    (if_neg_4 : ¬remaining.head! = 'n')
    (if_pos : OfNat.ofNat 0 < remaining.length)
    : countO + List.count 'o' remaining.tail! = List.count 'o' text := by
    sorry

theorem goal_34
    (text : List Char)
    (require_1 : True)
    (countA : ℕ)
    (countB : ℕ)
    (countL : ℕ)
    (countN : ℕ)
    (countO : ℕ)
    (remaining : List Char)
    (invariant_countB_inv : countB + List.count 'b' remaining = List.count 'b' text)
    (invariant_countA_inv : countA + List.count 'a' remaining = List.count 'a' text)
    (invariant_countL_inv : countL + List.count 'l' remaining = List.count 'l' text)
    (invariant_countO_inv : countO + List.count 'o' remaining = List.count 'o' text)
    (invariant_countN_inv : countN + List.count 'n' remaining = List.count 'n' text)
    (if_neg : ¬remaining.head! = 'b')
    (if_neg_1 : ¬remaining.head! = 'a')
    (if_neg_2 : ¬remaining.head! = 'l')
    (if_neg_3 : ¬remaining.head! = 'o')
    (if_neg_4 : ¬remaining.head! = 'n')
    (if_pos : OfNat.ofNat 0 < remaining.length)
    : countN + List.count 'n' remaining.tail! = List.count 'n' text := by
    sorry

theorem goal_35
    (text : List Char)
    (require_1 : True)
    (countA : ℕ)
    (countB : ℕ)
    (countL : ℕ)
    (countN : ℕ)
    (countO : ℕ)
    (remaining : List Char)
    (invariant_countB_inv : countB + List.count 'b' remaining = List.count 'b' text)
    (invariant_countA_inv : countA + List.count 'a' remaining = List.count 'a' text)
    (invariant_countL_inv : countL + List.count 'l' remaining = List.count 'l' text)
    (invariant_countO_inv : countO + List.count 'o' remaining = List.count 'o' text)
    (invariant_countN_inv : countN + List.count 'n' remaining = List.count 'n' text)
    (if_neg : ¬remaining.head! = 'b')
    (if_neg_1 : ¬remaining.head! = 'a')
    (if_neg_2 : ¬remaining.head! = 'l')
    (if_neg_3 : ¬remaining.head! = 'o')
    (if_neg_4 : ¬remaining.head! = 'n')
    (if_pos : OfNat.ofNat 0 < remaining.length)
    : remaining.tail!.length < remaining.length := by
    sorry

theorem goal_36
    (text : List Char)
    (require_1 : True)
    (countO : ℕ)
    (remaining : List Char)
    (invariant_countO_inv : countO + List.count 'o' remaining = List.count 'o' text)
    (i : ℕ)
    (i_1 : ℕ)
    (i_2 : ℕ)
    (i_3 : ℕ)
    (i_4 : ℕ)
    (remaining_1 : List Char)
    (if_pos : i < i_1)
    (if_pos_1 : i_2 / OfNat.ofNat 2 < i)
    (if_pos_2 : i_4 / OfNat.ofNat 2 < i_2 / OfNat.ofNat 2)
    (if_pos_3 : i_3 < i_4 / OfNat.ofNat 2)
    (invariant_countA_inv : i + List.count 'a' remaining = List.count 'a' text)
    (invariant_countB_inv : i_1 + List.count 'b' remaining = List.count 'b' text)
    (invariant_countL_inv : i_2 + List.count 'l' remaining = List.count 'l' text)
    (invariant_countN_inv : i_3 + List.count 'n' remaining = List.count 'n' text)
    (done_1 : remaining = [])
    (snd_eq : countO = i_4 ∧ remaining = remaining_1)
    : postcondition text i_3 := by
    sorry

theorem goal_37
    (text : List Char)
    (require_1 : True)
    (countO : ℕ)
    (remaining : List Char)
    (invariant_countO_inv : countO + List.count 'o' remaining = List.count 'o' text)
    (i : ℕ)
    (i_1 : ℕ)
    (i_2 : ℕ)
    (i_3 : ℕ)
    (i_4 : ℕ)
    (remaining_1 : List Char)
    (if_pos : i < i_1)
    (if_pos_1 : i_2 / OfNat.ofNat 2 < i)
    (if_pos_2 : i_4 / OfNat.ofNat 2 < i_2 / OfNat.ofNat 2)
    (invariant_countA_inv : i + List.count 'a' remaining = List.count 'a' text)
    (invariant_countB_inv : i_1 + List.count 'b' remaining = List.count 'b' text)
    (invariant_countL_inv : i_2 + List.count 'l' remaining = List.count 'l' text)
    (invariant_countN_inv : i_3 + List.count 'n' remaining = List.count 'n' text)
    (done_1 : remaining = [])
    (if_neg : i_4 / OfNat.ofNat 2 ≤ i_3)
    (snd_eq : countO = i_4 ∧ remaining = remaining_1)
    : postcondition text (i_4 / OfNat.ofNat 2) := by
    sorry

theorem goal_38
    (text : List Char)
    (require_1 : True)
    (countO : ℕ)
    (remaining : List Char)
    (invariant_countO_inv : countO + List.count 'o' remaining = List.count 'o' text)
    (i : ℕ)
    (i_1 : ℕ)
    (i_2 : ℕ)
    (i_3 : ℕ)
    (i_4 : ℕ)
    (remaining_1 : List Char)
    (if_pos : i < i_1)
    (if_pos_1 : i_2 / OfNat.ofNat 2 < i)
    (if_pos_2 : i_3 < i_2 / OfNat.ofNat 2)
    (invariant_countA_inv : i + List.count 'a' remaining = List.count 'a' text)
    (invariant_countB_inv : i_1 + List.count 'b' remaining = List.count 'b' text)
    (invariant_countL_inv : i_2 + List.count 'l' remaining = List.count 'l' text)
    (invariant_countN_inv : i_3 + List.count 'n' remaining = List.count 'n' text)
    (done_1 : remaining = [])
    (if_neg : i_2 / OfNat.ofNat 2 ≤ i_4 / OfNat.ofNat 2)
    (snd_eq : countO = i_4 ∧ remaining = remaining_1)
    : postcondition text i_3 := by
    sorry

theorem goal_39
    (text : List Char)
    (require_1 : True)
    (countO : ℕ)
    (remaining : List Char)
    (invariant_countO_inv : countO + List.count 'o' remaining = List.count 'o' text)
    (i : ℕ)
    (i_1 : ℕ)
    (i_2 : ℕ)
    (i_3 : ℕ)
    (i_4 : ℕ)
    (remaining_1 : List Char)
    (if_pos : i < i_1)
    (if_pos_1 : i_2 / OfNat.ofNat 2 < i)
    (invariant_countA_inv : i + List.count 'a' remaining = List.count 'a' text)
    (invariant_countB_inv : i_1 + List.count 'b' remaining = List.count 'b' text)
    (invariant_countL_inv : i_2 + List.count 'l' remaining = List.count 'l' text)
    (invariant_countN_inv : i_3 + List.count 'n' remaining = List.count 'n' text)
    (done_1 : remaining = [])
    (if_neg : i_2 / OfNat.ofNat 2 ≤ i_4 / OfNat.ofNat 2)
    (if_neg_1 : i_2 / OfNat.ofNat 2 ≤ i_3)
    (snd_eq : countO = i_4 ∧ remaining = remaining_1)
    : postcondition text (i_2 / OfNat.ofNat 2) := by
    sorry

theorem goal_40
    (text : List Char)
    (require_1 : True)
    (countO : ℕ)
    (remaining : List Char)
    (invariant_countO_inv : countO + List.count 'o' remaining = List.count 'o' text)
    (i : ℕ)
    (i_1 : ℕ)
    (i_2 : ℕ)
    (i_3 : ℕ)
    (i_4 : ℕ)
    (remaining_1 : List Char)
    (if_pos : i < i_1)
    (if_pos_1 : i_4 / OfNat.ofNat 2 < i)
    (if_pos_2 : i_3 < i_4 / OfNat.ofNat 2)
    (invariant_countA_inv : i + List.count 'a' remaining = List.count 'a' text)
    (invariant_countB_inv : i_1 + List.count 'b' remaining = List.count 'b' text)
    (invariant_countL_inv : i_2 + List.count 'l' remaining = List.count 'l' text)
    (invariant_countN_inv : i_3 + List.count 'n' remaining = List.count 'n' text)
    (done_1 : remaining = [])
    (if_neg : i ≤ i_2 / OfNat.ofNat 2)
    (snd_eq : countO = i_4 ∧ remaining = remaining_1)
    : postcondition text i_3 := by
    sorry

theorem goal_41
    (text : List Char)
    (require_1 : True)
    (countO : ℕ)
    (remaining : List Char)
    (invariant_countO_inv : countO + List.count 'o' remaining = List.count 'o' text)
    (i : ℕ)
    (i_1 : ℕ)
    (i_2 : ℕ)
    (i_3 : ℕ)
    (i_4 : ℕ)
    (remaining_1 : List Char)
    (if_pos : i < i_1)
    (if_pos_1 : i_4 / OfNat.ofNat 2 < i)
    (invariant_countA_inv : i + List.count 'a' remaining = List.count 'a' text)
    (invariant_countB_inv : i_1 + List.count 'b' remaining = List.count 'b' text)
    (invariant_countL_inv : i_2 + List.count 'l' remaining = List.count 'l' text)
    (invariant_countN_inv : i_3 + List.count 'n' remaining = List.count 'n' text)
    (done_1 : remaining = [])
    (if_neg : i ≤ i_2 / OfNat.ofNat 2)
    (if_neg_1 : i_4 / OfNat.ofNat 2 ≤ i_3)
    (snd_eq : countO = i_4 ∧ remaining = remaining_1)
    : postcondition text (i_4 / OfNat.ofNat 2) := by
    sorry

theorem goal_42
    (text : List Char)
    (require_1 : True)
    (countO : ℕ)
    (remaining : List Char)
    (invariant_countO_inv : countO + List.count 'o' remaining = List.count 'o' text)
    (i : ℕ)
    (i_1 : ℕ)
    (i_2 : ℕ)
    (i_3 : ℕ)
    (i_4 : ℕ)
    (remaining_1 : List Char)
    (if_pos : i < i_1)
    (if_pos_1 : i_3 < i)
    (invariant_countA_inv : i + List.count 'a' remaining = List.count 'a' text)
    (invariant_countB_inv : i_1 + List.count 'b' remaining = List.count 'b' text)
    (invariant_countL_inv : i_2 + List.count 'l' remaining = List.count 'l' text)
    (invariant_countN_inv : i_3 + List.count 'n' remaining = List.count 'n' text)
    (done_1 : remaining = [])
    (if_neg : i ≤ i_2 / OfNat.ofNat 2)
    (if_neg_1 : i ≤ i_4 / OfNat.ofNat 2)
    (snd_eq : countO = i_4 ∧ remaining = remaining_1)
    : postcondition text i_3 := by
    sorry

theorem goal_43
    (text : List Char)
    (require_1 : True)
    (countO : ℕ)
    (remaining : List Char)
    (invariant_countO_inv : countO + List.count 'o' remaining = List.count 'o' text)
    (i : ℕ)
    (i_1 : ℕ)
    (i_2 : ℕ)
    (i_3 : ℕ)
    (i_4 : ℕ)
    (remaining_1 : List Char)
    (if_pos : i < i_1)
    (invariant_countA_inv : i + List.count 'a' remaining = List.count 'a' text)
    (invariant_countB_inv : i_1 + List.count 'b' remaining = List.count 'b' text)
    (invariant_countL_inv : i_2 + List.count 'l' remaining = List.count 'l' text)
    (invariant_countN_inv : i_3 + List.count 'n' remaining = List.count 'n' text)
    (done_1 : remaining = [])
    (if_neg : i ≤ i_2 / OfNat.ofNat 2)
    (if_neg_1 : i ≤ i_4 / OfNat.ofNat 2)
    (if_neg_2 : i ≤ i_3)
    (snd_eq : countO = i_4 ∧ remaining = remaining_1)
    : postcondition text i := by
    sorry

theorem goal_44
    (text : List Char)
    (require_1 : True)
    (countO : ℕ)
    (remaining : List Char)
    (invariant_countO_inv : countO + List.count 'o' remaining = List.count 'o' text)
    (i : ℕ)
    (i_1 : ℕ)
    (i_2 : ℕ)
    (i_3 : ℕ)
    (i_4 : ℕ)
    (remaining_1 : List Char)
    (if_pos : i_2 / OfNat.ofNat 2 < i_1)
    (if_pos_1 : i_4 / OfNat.ofNat 2 < i_2 / OfNat.ofNat 2)
    (if_pos_2 : i_3 < i_4 / OfNat.ofNat 2)
    (invariant_countA_inv : i + List.count 'a' remaining = List.count 'a' text)
    (invariant_countB_inv : i_1 + List.count 'b' remaining = List.count 'b' text)
    (invariant_countL_inv : i_2 + List.count 'l' remaining = List.count 'l' text)
    (invariant_countN_inv : i_3 + List.count 'n' remaining = List.count 'n' text)
    (done_1 : remaining = [])
    (if_neg : i_1 ≤ i)
    (snd_eq : countO = i_4 ∧ remaining = remaining_1)
    : postcondition text i_3 := by
    sorry

theorem goal_45
    (text : List Char)
    (require_1 : True)
    (countO : ℕ)
    (remaining : List Char)
    (invariant_countO_inv : countO + List.count 'o' remaining = List.count 'o' text)
    (i : ℕ)
    (i_1 : ℕ)
    (i_2 : ℕ)
    (i_3 : ℕ)
    (i_4 : ℕ)
    (remaining_1 : List Char)
    (if_pos : i_2 / OfNat.ofNat 2 < i_1)
    (if_pos_1 : i_4 / OfNat.ofNat 2 < i_2 / OfNat.ofNat 2)
    (invariant_countA_inv : i + List.count 'a' remaining = List.count 'a' text)
    (invariant_countB_inv : i_1 + List.count 'b' remaining = List.count 'b' text)
    (invariant_countL_inv : i_2 + List.count 'l' remaining = List.count 'l' text)
    (invariant_countN_inv : i_3 + List.count 'n' remaining = List.count 'n' text)
    (done_1 : remaining = [])
    (if_neg : i_1 ≤ i)
    (if_neg_1 : i_4 / OfNat.ofNat 2 ≤ i_3)
    (snd_eq : countO = i_4 ∧ remaining = remaining_1)
    : postcondition text (i_4 / OfNat.ofNat 2) := by
    sorry

theorem goal_46
    (text : List Char)
    (require_1 : True)
    (countO : ℕ)
    (remaining : List Char)
    (invariant_countO_inv : countO + List.count 'o' remaining = List.count 'o' text)
    (i : ℕ)
    (i_1 : ℕ)
    (i_2 : ℕ)
    (i_3 : ℕ)
    (i_4 : ℕ)
    (remaining_1 : List Char)
    (if_pos : i_2 / OfNat.ofNat 2 < i_1)
    (if_pos_1 : i_3 < i_2 / OfNat.ofNat 2)
    (invariant_countA_inv : i + List.count 'a' remaining = List.count 'a' text)
    (invariant_countB_inv : i_1 + List.count 'b' remaining = List.count 'b' text)
    (invariant_countL_inv : i_2 + List.count 'l' remaining = List.count 'l' text)
    (invariant_countN_inv : i_3 + List.count 'n' remaining = List.count 'n' text)
    (done_1 : remaining = [])
    (if_neg : i_1 ≤ i)
    (if_neg_1 : i_2 / OfNat.ofNat 2 ≤ i_4 / OfNat.ofNat 2)
    (snd_eq : countO = i_4 ∧ remaining = remaining_1)
    : postcondition text i_3 := by
    sorry

theorem goal_47
    (text : List Char)
    (require_1 : True)
    (countO : ℕ)
    (remaining : List Char)
    (invariant_countO_inv : countO + List.count 'o' remaining = List.count 'o' text)
    (i : ℕ)
    (i_1 : ℕ)
    (i_2 : ℕ)
    (i_3 : ℕ)
    (i_4 : ℕ)
    (remaining_1 : List Char)
    (if_pos : i_2 / OfNat.ofNat 2 < i_1)
    (invariant_countA_inv : i + List.count 'a' remaining = List.count 'a' text)
    (invariant_countB_inv : i_1 + List.count 'b' remaining = List.count 'b' text)
    (invariant_countL_inv : i_2 + List.count 'l' remaining = List.count 'l' text)
    (invariant_countN_inv : i_3 + List.count 'n' remaining = List.count 'n' text)
    (done_1 : remaining = [])
    (if_neg : i_1 ≤ i)
    (if_neg_1 : i_2 / OfNat.ofNat 2 ≤ i_4 / OfNat.ofNat 2)
    (if_neg_2 : i_2 / OfNat.ofNat 2 ≤ i_3)
    (snd_eq : countO = i_4 ∧ remaining = remaining_1)
    : postcondition text (i_2 / OfNat.ofNat 2) := by
    sorry

theorem goal_48
    (text : List Char)
    (require_1 : True)
    (countO : ℕ)
    (remaining : List Char)
    (invariant_countO_inv : countO + List.count 'o' remaining = List.count 'o' text)
    (i : ℕ)
    (i_1 : ℕ)
    (i_2 : ℕ)
    (i_3 : ℕ)
    (i_4 : ℕ)
    (remaining_1 : List Char)
    (if_pos : i_4 / OfNat.ofNat 2 < i_1)
    (if_pos_1 : i_3 < i_4 / OfNat.ofNat 2)
    (invariant_countA_inv : i + List.count 'a' remaining = List.count 'a' text)
    (invariant_countB_inv : i_1 + List.count 'b' remaining = List.count 'b' text)
    (invariant_countL_inv : i_2 + List.count 'l' remaining = List.count 'l' text)
    (invariant_countN_inv : i_3 + List.count 'n' remaining = List.count 'n' text)
    (done_1 : remaining = [])
    (if_neg : i_1 ≤ i)
    (if_neg_1 : i_1 ≤ i_2 / OfNat.ofNat 2)
    (snd_eq : countO = i_4 ∧ remaining = remaining_1)
    : postcondition text i_3 := by
    sorry

theorem goal_49
    (text : List Char)
    (require_1 : True)
    (countO : ℕ)
    (remaining : List Char)
    (invariant_countO_inv : countO + List.count 'o' remaining = List.count 'o' text)
    (i : ℕ)
    (i_1 : ℕ)
    (i_2 : ℕ)
    (i_3 : ℕ)
    (i_4 : ℕ)
    (remaining_1 : List Char)
    (if_pos : i_4 / OfNat.ofNat 2 < i_1)
    (invariant_countA_inv : i + List.count 'a' remaining = List.count 'a' text)
    (invariant_countB_inv : i_1 + List.count 'b' remaining = List.count 'b' text)
    (invariant_countL_inv : i_2 + List.count 'l' remaining = List.count 'l' text)
    (invariant_countN_inv : i_3 + List.count 'n' remaining = List.count 'n' text)
    (done_1 : remaining = [])
    (if_neg : i_1 ≤ i)
    (if_neg_1 : i_1 ≤ i_2 / OfNat.ofNat 2)
    (if_neg_2 : i_4 / OfNat.ofNat 2 ≤ i_3)
    (snd_eq : countO = i_4 ∧ remaining = remaining_1)
    : postcondition text (i_4 / OfNat.ofNat 2) := by
    sorry

theorem goal_50
    (text : List Char)
    (require_1 : True)
    (countO : ℕ)
    (remaining : List Char)
    (invariant_countO_inv : countO + List.count 'o' remaining = List.count 'o' text)
    (i : ℕ)
    (i_1 : ℕ)
    (i_2 : ℕ)
    (i_3 : ℕ)
    (i_4 : ℕ)
    (remaining_1 : List Char)
    (if_pos : i_3 < i_1)
    (invariant_countA_inv : i + List.count 'a' remaining = List.count 'a' text)
    (invariant_countB_inv : i_1 + List.count 'b' remaining = List.count 'b' text)
    (invariant_countL_inv : i_2 + List.count 'l' remaining = List.count 'l' text)
    (invariant_countN_inv : i_3 + List.count 'n' remaining = List.count 'n' text)
    (done_1 : remaining = [])
    (if_neg : i_1 ≤ i)
    (if_neg_1 : i_1 ≤ i_2 / OfNat.ofNat 2)
    (if_neg_2 : i_1 ≤ i_4 / OfNat.ofNat 2)
    (snd_eq : countO = i_4 ∧ remaining = remaining_1)
    : postcondition text i_3 := by
    sorry

theorem goal_51
    (text : List Char)
    (require_1 : True)
    (countO : ℕ)
    (remaining : List Char)
    (invariant_countO_inv : countO + List.count 'o' remaining = List.count 'o' text)
    (i : ℕ)
    (i_1 : ℕ)
    (i_2 : ℕ)
    (i_3 : ℕ)
    (i_4 : ℕ)
    (remaining_1 : List Char)
    (invariant_countA_inv : i + List.count 'a' remaining = List.count 'a' text)
    (invariant_countB_inv : i_1 + List.count 'b' remaining = List.count 'b' text)
    (invariant_countL_inv : i_2 + List.count 'l' remaining = List.count 'l' text)
    (invariant_countN_inv : i_3 + List.count 'n' remaining = List.count 'n' text)
    (done_1 : remaining = [])
    (if_neg : i_1 ≤ i)
    (if_neg_1 : i_1 ≤ i_2 / OfNat.ofNat 2)
    (if_neg_2 : i_1 ≤ i_4 / OfNat.ofNat 2)
    (if_neg_3 : i_1 ≤ i_3)
    (snd_eq : countO = i_4 ∧ remaining = remaining_1)
    : postcondition text i_1 := by
    sorry



prove_correct MaximumNumberOfBalloons by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at *); try (conv => congr <;> simp) ; try expose_names)
  exact (goal_0 text countA countB countL countN countO remaining invariant_countB_inv invariant_countA_inv invariant_countL_inv invariant_countO_inv invariant_countN_inv if_pos_1 if_pos)
  exact (goal_1 text countA countB countL countN countO remaining invariant_countB_inv invariant_countA_inv invariant_countL_inv invariant_countO_inv invariant_countN_inv if_pos_1 if_pos)
  exact (goal_2 text countA countB countL countN countO remaining invariant_countB_inv invariant_countA_inv invariant_countL_inv invariant_countO_inv invariant_countN_inv if_pos_1 if_pos)
  exact (goal_3 text countA countB countL countN countO remaining invariant_countB_inv invariant_countA_inv invariant_countL_inv invariant_countO_inv invariant_countN_inv if_pos_1 if_pos)
  exact (goal_4 text countA countB countL countN countO remaining invariant_countB_inv invariant_countA_inv invariant_countL_inv invariant_countO_inv invariant_countN_inv if_pos_1 if_pos)
  exact (goal_5 text countA countB countL countN countO remaining invariant_countB_inv invariant_countA_inv invariant_countL_inv invariant_countO_inv invariant_countN_inv if_pos_1 if_pos)
  exact (goal_6 text countA countB countL countN countO remaining invariant_countB_inv invariant_countA_inv invariant_countL_inv invariant_countO_inv invariant_countN_inv if_neg if_pos_1 if_pos)
  exact (goal_7 text countA countB countL countN countO remaining invariant_countB_inv invariant_countA_inv invariant_countL_inv invariant_countO_inv invariant_countN_inv if_neg if_pos_1 if_pos)
  exact (goal_8 text countA countB countL countN countO remaining invariant_countB_inv invariant_countA_inv invariant_countL_inv invariant_countO_inv invariant_countN_inv if_neg if_pos_1 if_pos)
  exact (goal_9 text countA countB countL countN countO remaining invariant_countB_inv invariant_countA_inv invariant_countL_inv invariant_countO_inv invariant_countN_inv if_neg if_pos_1 if_pos)
  exact (goal_10 text countA countB countL countN countO remaining invariant_countB_inv invariant_countA_inv invariant_countL_inv invariant_countO_inv invariant_countN_inv if_neg if_pos_1 if_pos)
  exact (goal_11 text countA countB countL countN countO remaining invariant_countB_inv invariant_countA_inv invariant_countL_inv invariant_countO_inv invariant_countN_inv if_neg if_pos_1 if_pos)
  exact (goal_12 text countA countB countL countN countO remaining invariant_countB_inv invariant_countA_inv invariant_countL_inv invariant_countO_inv invariant_countN_inv if_neg if_neg_1 if_pos_1 if_pos)
  exact (goal_13 text countA countB countL countN countO remaining invariant_countB_inv invariant_countA_inv invariant_countL_inv invariant_countO_inv invariant_countN_inv if_neg if_neg_1 if_pos_1 if_pos)
  exact (goal_14 text countA countB countL countN countO remaining invariant_countB_inv invariant_countA_inv invariant_countL_inv invariant_countO_inv invariant_countN_inv if_neg if_neg_1 if_pos_1 if_pos)
  exact (goal_15 text countA countB countL countN countO remaining invariant_countB_inv invariant_countA_inv invariant_countL_inv invariant_countO_inv invariant_countN_inv if_neg if_neg_1 if_pos_1 if_pos)
  exact (goal_16 text countA countB countL countN countO remaining invariant_countB_inv invariant_countA_inv invariant_countL_inv invariant_countO_inv invariant_countN_inv if_neg if_neg_1 if_pos_1 if_pos)
  exact (goal_17 text countA countB countL countN countO remaining invariant_countB_inv invariant_countA_inv invariant_countL_inv invariant_countO_inv invariant_countN_inv if_neg if_neg_1 if_pos_1 if_pos)
  exact (goal_18 text countA countB countL countN countO remaining invariant_countB_inv invariant_countA_inv invariant_countL_inv invariant_countO_inv invariant_countN_inv if_neg if_neg_1 if_neg_2 if_pos_1 if_pos)
  exact (goal_19 text countA countB countL countN countO remaining invariant_countB_inv invariant_countA_inv invariant_countL_inv invariant_countO_inv invariant_countN_inv if_neg if_neg_1 if_neg_2 if_pos_1 if_pos)
  exact (goal_20 text countA countB countL countN countO remaining invariant_countB_inv invariant_countA_inv invariant_countL_inv invariant_countO_inv invariant_countN_inv if_neg if_neg_1 if_neg_2 if_pos_1 if_pos)
  exact (goal_21 text require_1 countA countB countL countN countO remaining invariant_countB_inv invariant_countA_inv invariant_countL_inv invariant_countO_inv invariant_countN_inv if_neg if_neg_1 if_neg_2 if_pos_1 if_pos)
  exact (goal_22 text require_1 countA countB countL countN countO remaining invariant_countB_inv invariant_countA_inv invariant_countL_inv invariant_countO_inv invariant_countN_inv if_neg if_neg_1 if_neg_2 if_pos_1 if_pos)
  exact (goal_23 text require_1 countA countB countL countN countO remaining invariant_countB_inv invariant_countA_inv invariant_countL_inv invariant_countO_inv invariant_countN_inv if_neg if_neg_1 if_neg_2 if_pos_1 if_pos)
  exact (goal_24 text require_1 countA countB countL countN countO remaining invariant_countB_inv invariant_countA_inv invariant_countL_inv invariant_countO_inv invariant_countN_inv if_neg if_neg_1 if_neg_2 if_neg_3 if_pos_1 if_pos)
  exact (goal_25 text require_1 countA countB countL countN countO remaining invariant_countB_inv invariant_countA_inv invariant_countL_inv invariant_countO_inv invariant_countN_inv if_neg if_neg_1 if_neg_2 if_neg_3 if_pos_1 if_pos)
  exact (goal_26 text require_1 countA countB countL countN countO remaining invariant_countB_inv invariant_countA_inv invariant_countL_inv invariant_countO_inv invariant_countN_inv if_neg if_neg_1 if_neg_2 if_neg_3 if_pos_1 if_pos)
  exact (goal_27 text require_1 countA countB countL countN countO remaining invariant_countB_inv invariant_countA_inv invariant_countL_inv invariant_countO_inv invariant_countN_inv if_neg if_neg_1 if_neg_2 if_neg_3 if_pos_1 if_pos)
  exact (goal_28 text require_1 countA countB countL countN countO remaining invariant_countB_inv invariant_countA_inv invariant_countL_inv invariant_countO_inv invariant_countN_inv if_neg if_neg_1 if_neg_2 if_neg_3 if_pos_1 if_pos)
  exact (goal_29 text require_1 countA countB countL countN countO remaining invariant_countB_inv invariant_countA_inv invariant_countL_inv invariant_countO_inv invariant_countN_inv if_neg if_neg_1 if_neg_2 if_neg_3 if_pos_1 if_pos)
  exact (goal_30 text require_1 countA countB countL countN countO remaining invariant_countB_inv invariant_countA_inv invariant_countL_inv invariant_countO_inv invariant_countN_inv if_neg if_neg_1 if_neg_2 if_neg_3 if_neg_4 if_pos)
  exact (goal_31 text require_1 countA countB countL countN countO remaining invariant_countB_inv invariant_countA_inv invariant_countL_inv invariant_countO_inv invariant_countN_inv if_neg if_neg_1 if_neg_2 if_neg_3 if_neg_4 if_pos)
  exact (goal_32 text require_1 countA countB countL countN countO remaining invariant_countB_inv invariant_countA_inv invariant_countL_inv invariant_countO_inv invariant_countN_inv if_neg if_neg_1 if_neg_2 if_neg_3 if_neg_4 if_pos)
  exact (goal_33 text require_1 countA countB countL countN countO remaining invariant_countB_inv invariant_countA_inv invariant_countL_inv invariant_countO_inv invariant_countN_inv if_neg if_neg_1 if_neg_2 if_neg_3 if_neg_4 if_pos)
  exact (goal_34 text require_1 countA countB countL countN countO remaining invariant_countB_inv invariant_countA_inv invariant_countL_inv invariant_countO_inv invariant_countN_inv if_neg if_neg_1 if_neg_2 if_neg_3 if_neg_4 if_pos)
  exact (goal_35 text require_1 countA countB countL countN countO remaining invariant_countB_inv invariant_countA_inv invariant_countL_inv invariant_countO_inv invariant_countN_inv if_neg if_neg_1 if_neg_2 if_neg_3 if_neg_4 if_pos)
  exact (goal_36 text require_1 countO remaining invariant_countO_inv i i_1 i_2 i_3 i_4 remaining_1 if_pos if_pos_1 if_pos_2 if_pos_3 invariant_countA_inv invariant_countB_inv invariant_countL_inv invariant_countN_inv done_1 snd_eq)
  exact (goal_37 text require_1 countO remaining invariant_countO_inv i i_1 i_2 i_3 i_4 remaining_1 if_pos if_pos_1 if_pos_2 invariant_countA_inv invariant_countB_inv invariant_countL_inv invariant_countN_inv done_1 if_neg snd_eq)
  exact (goal_38 text require_1 countO remaining invariant_countO_inv i i_1 i_2 i_3 i_4 remaining_1 if_pos if_pos_1 if_pos_2 invariant_countA_inv invariant_countB_inv invariant_countL_inv invariant_countN_inv done_1 if_neg snd_eq)
  exact (goal_39 text require_1 countO remaining invariant_countO_inv i i_1 i_2 i_3 i_4 remaining_1 if_pos if_pos_1 invariant_countA_inv invariant_countB_inv invariant_countL_inv invariant_countN_inv done_1 if_neg if_neg_1 snd_eq)
  exact (goal_40 text require_1 countO remaining invariant_countO_inv i i_1 i_2 i_3 i_4 remaining_1 if_pos if_pos_1 if_pos_2 invariant_countA_inv invariant_countB_inv invariant_countL_inv invariant_countN_inv done_1 if_neg snd_eq)
  exact (goal_41 text require_1 countO remaining invariant_countO_inv i i_1 i_2 i_3 i_4 remaining_1 if_pos if_pos_1 invariant_countA_inv invariant_countB_inv invariant_countL_inv invariant_countN_inv done_1 if_neg if_neg_1 snd_eq)
  exact (goal_42 text require_1 countO remaining invariant_countO_inv i i_1 i_2 i_3 i_4 remaining_1 if_pos if_pos_1 invariant_countA_inv invariant_countB_inv invariant_countL_inv invariant_countN_inv done_1 if_neg if_neg_1 snd_eq)
  exact (goal_43 text require_1 countO remaining invariant_countO_inv i i_1 i_2 i_3 i_4 remaining_1 if_pos invariant_countA_inv invariant_countB_inv invariant_countL_inv invariant_countN_inv done_1 if_neg if_neg_1 if_neg_2 snd_eq)
  exact (goal_44 text require_1 countO remaining invariant_countO_inv i i_1 i_2 i_3 i_4 remaining_1 if_pos if_pos_1 if_pos_2 invariant_countA_inv invariant_countB_inv invariant_countL_inv invariant_countN_inv done_1 if_neg snd_eq)
  exact (goal_45 text require_1 countO remaining invariant_countO_inv i i_1 i_2 i_3 i_4 remaining_1 if_pos if_pos_1 invariant_countA_inv invariant_countB_inv invariant_countL_inv invariant_countN_inv done_1 if_neg if_neg_1 snd_eq)
  exact (goal_46 text require_1 countO remaining invariant_countO_inv i i_1 i_2 i_3 i_4 remaining_1 if_pos if_pos_1 invariant_countA_inv invariant_countB_inv invariant_countL_inv invariant_countN_inv done_1 if_neg if_neg_1 snd_eq)
  exact (goal_47 text require_1 countO remaining invariant_countO_inv i i_1 i_2 i_3 i_4 remaining_1 if_pos invariant_countA_inv invariant_countB_inv invariant_countL_inv invariant_countN_inv done_1 if_neg if_neg_1 if_neg_2 snd_eq)
  exact (goal_48 text require_1 countO remaining invariant_countO_inv i i_1 i_2 i_3 i_4 remaining_1 if_pos if_pos_1 invariant_countA_inv invariant_countB_inv invariant_countL_inv invariant_countN_inv done_1 if_neg if_neg_1 snd_eq)
  exact (goal_49 text require_1 countO remaining invariant_countO_inv i i_1 i_2 i_3 i_4 remaining_1 if_pos invariant_countA_inv invariant_countB_inv invariant_countL_inv invariant_countN_inv done_1 if_neg if_neg_1 if_neg_2 snd_eq)
  exact (goal_50 text require_1 countO remaining invariant_countO_inv i i_1 i_2 i_3 i_4 remaining_1 if_pos invariant_countA_inv invariant_countB_inv invariant_countL_inv invariant_countN_inv done_1 if_neg if_neg_1 if_neg_2 snd_eq)
  exact (goal_51 text require_1 countO remaining invariant_countO_inv i i_1 i_2 i_3 i_4 remaining_1 invariant_countA_inv invariant_countB_inv invariant_countL_inv invariant_countN_inv done_1 if_neg if_neg_1 if_neg_2 if_neg_3 snd_eq)
end Proof
