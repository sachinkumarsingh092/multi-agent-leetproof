import Lean
import Mathlib.Tactic
import Velvet.Std
import Extensions.VelvetPBT

set_option maxHeartbeats 10000000

section Specs
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false

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
def implementation (text : List Char) : Nat :=
  let cb := text.count 'b'
  let ca := text.count 'a'
  let cl := text.count 'l'
  let co := text.count 'o'
  let cn := text.count 'n'
  min cb (min ca (min (cl / 2) (min (co / 2) cn)))
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
#assert_same_evaluation #[(implementation test1_text), test1_Expected]

-- Test case 2
#assert_same_evaluation #[(implementation test2_text), test2_Expected]

-- Test case 3
#assert_same_evaluation #[(implementation test3_text), test3_Expected]

-- Test case 4
#assert_same_evaluation #[(implementation test4_text), test4_Expected]

-- Test case 5
#assert_same_evaluation #[(implementation test5_text), test5_Expected]

-- Test case 6
#assert_same_evaluation #[(implementation test6_text), test6_Expected]

-- Test case 7
#assert_same_evaluation #[(implementation test7_text), test7_Expected]

-- Test case 8
#assert_same_evaluation #[(implementation test8_text), test8_Expected]

-- Test case 9
#assert_same_evaluation #[(implementation test9_text), test9_Expected]
end Assertions

section Pbt
method implementationPbt (text : List Char)
  return (result : Nat)
  require precondition text
  ensures postcondition text result
  do
  return (implementation text)

velvet_plausible_test implementationPbt (config := { maxMs := some 20000 })
end Pbt

section Proof
theorem correctness_goal
    (text : List Char)
    : postcondition text (implementation text) := by
    unfold postcondition implementation feasibleBalloons charCount
    simp only []
    constructor
    · -- Feasibility
      constructor
      · exact Nat.min_le_left _ _
      constructor
      · exact le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _)
      constructor
      · have h1 : min (List.count 'b' text) (min (List.count 'a' text) (min (List.count 'l' text / 2) (min (List.count 'o' text / 2) (List.count 'n' text)))) ≤ List.count 'l' text / 2 := by
          calc min (List.count 'b' text) (min (List.count 'a' text) (min (List.count 'l' text / 2) (min (List.count 'o' text / 2) (List.count 'n' text))))
              ≤ min (List.count 'a' text) (min (List.count 'l' text / 2) (min (List.count 'o' text / 2) (List.count 'n' text))) := Nat.min_le_right _ _
            _ ≤ min (List.count 'l' text / 2) (min (List.count 'o' text / 2) (List.count 'n' text)) := Nat.min_le_right _ _
            _ ≤ List.count 'l' text / 2 := Nat.min_le_left _ _
        have h2 : Nat.mul 2 (List.count 'l' text / 2) ≤ List.count 'l' text := Nat.mul_div_le _ 2
        omega
      constructor
      · have h1 : min (List.count 'b' text) (min (List.count 'a' text) (min (List.count 'l' text / 2) (min (List.count 'o' text / 2) (List.count 'n' text)))) ≤ List.count 'o' text / 2 := by
          calc min (List.count 'b' text) (min (List.count 'a' text) (min (List.count 'l' text / 2) (min (List.count 'o' text / 2) (List.count 'n' text))))
              ≤ min (List.count 'a' text) (min (List.count 'l' text / 2) (min (List.count 'o' text / 2) (List.count 'n' text))) := Nat.min_le_right _ _
            _ ≤ min (List.count 'l' text / 2) (min (List.count 'o' text / 2) (List.count 'n' text)) := Nat.min_le_right _ _
            _ ≤ min (List.count 'o' text / 2) (List.count 'n' text) := Nat.min_le_right _ _
            _ ≤ List.count 'o' text / 2 := Nat.min_le_left _ _
        have h2 : Nat.mul 2 (List.count 'o' text / 2) ≤ List.count 'o' text := Nat.mul_div_le _ 2
        omega
      · calc min (List.count 'b' text) (min (List.count 'a' text) (min (List.count 'l' text / 2) (min (List.count 'o' text / 2) (List.count 'n' text))))
            ≤ min (List.count 'a' text) (min (List.count 'l' text / 2) (min (List.count 'o' text / 2) (List.count 'n' text))) := Nat.min_le_right _ _
          _ ≤ min (List.count 'l' text / 2) (min (List.count 'o' text / 2) (List.count 'n' text)) := Nat.min_le_right _ _
          _ ≤ min (List.count 'o' text / 2) (List.count 'n' text) := Nat.min_le_right _ _
          _ ≤ List.count 'n' text := Nat.min_le_right _ _
    · -- Maximality
      intro k hk
      obtain ⟨hb, ha, hl, ho, hn⟩ := hk
      rw [le_min_iff]
      constructor
      · exact hb
      rw [le_min_iff]
      constructor
      · exact ha
      rw [le_min_iff]
      constructor
      · rw [Nat.le_div_iff_mul_le (by norm_num : (0:Nat) < 2)]
        omega
      rw [le_min_iff]
      constructor
      · rw [Nat.le_div_iff_mul_le (by norm_num : (0:Nat) < 2)]
        omega
      · exact hn
end Proof
