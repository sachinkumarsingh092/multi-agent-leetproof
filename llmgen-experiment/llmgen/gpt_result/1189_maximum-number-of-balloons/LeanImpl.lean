import Lean
import Mathlib.Tactic
import Velvet.Std

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
  -- Single pass to count only the needed letters. O(n) time, O(1) extra space.
  let counts : Nat × Nat × Nat × Nat × Nat :=
    text.foldl
      (fun (acc : Nat × Nat × Nat × Nat × Nat) ch =>
        let (b, a, l, o, n) := acc
        if ch = 'b' then (b + 1, a, l, o, n)
        else if ch = 'a' then (b, a + 1, l, o, n)
        else if ch = 'l' then (b, a, l + 1, o, n)
        else if ch = 'o' then (b, a, l, o + 1, n)
        else if ch = 'n' then (b, a, l, o, n + 1)
        else acc)
      (0, 0, 0, 0, 0)
  let (b, a, l, o, n) := counts
  Nat.min b (Nat.min a (Nat.min (l / 2) (Nat.min (o / 2) n)))
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

section Proof
theorem correctness_goal
    (text : List Char)
    (h_precond : precondition text)
    : postcondition text (implementation text) := by
  classical
  -- Precondition is trivial.
  have _ : True := h_precond

  -- Define the step function used by the implementation.
  let countStep : (Nat × Nat × Nat × Nat × Nat) → Char → (Nat × Nat × Nat × Nat × Nat) :=
    fun (acc : Nat × Nat × Nat × Nat × Nat) ch =>
      let (b, a, l, o, n) := acc
      if ch = 'b' then (b + 1, a, l, o, n)
      else if ch = 'a' then (b, a + 1, l, o, n)
      else if ch = 'l' then (b, a, l + 1, o, n)
      else if ch = 'o' then (b, a, l, o + 1, n)
      else if ch = 'n' then (b, a, l, o, n + 1)
      else acc

  -- Folding `countStep` accumulates the counts of the tracked characters.
  have fold_counts_general :
      ∀ (t : List Char) (b a l o n : Nat),
        t.foldl countStep (b, a, l, o, n) =
          (b + charCount t 'b',
           a + charCount t 'a',
           l + charCount t 'l',
           o + charCount t 'o',
           n + charCount t 'n') := by
    intro t
    induction t with
    | nil =>
        intro b a l o n
        simp [charCount, countStep]
    | cons ch tl ih =>
        intro b a l o n
        -- Split on which tracked character we see.
        by_cases hb : ch = 'b'
        · subst hb
          -- step increments b
          simp [List.foldl_cons, countStep, ih, charCount,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        · by_cases ha : ch = 'a'
          · subst ha
            simp [List.foldl_cons, countStep, ih, charCount, hb,
              Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          · by_cases hl : ch = 'l'
            · subst hl
              simp [List.foldl_cons, countStep, ih, charCount, hb, ha,
                Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            · by_cases ho : ch = 'o'
              · subst ho
                simp [List.foldl_cons, countStep, ih, charCount, hb, ha, hl,
                  Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
              · by_cases hn : ch = 'n'
                · subst hn
                  simp [List.foldl_cons, countStep, ih, charCount, hb, ha, hl, ho,
                    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
                ·
                  -- other character: accumulator unchanged
                  simp [List.foldl_cons, countStep, ih, charCount, hb, ha, hl, ho, hn,
                    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

  -- Specialized version for the initial accumulator used in the implementation.
  have fold_counts_zero :
      text.foldl countStep (0, 0, 0, 0, 0) =
        (charCount text 'b',
         charCount text 'a',
         charCount text 'l',
         charCount text 'o',
         charCount text 'n') := by
    simpa [Nat.zero_add] using (fold_counts_general text 0 0 0 0 0)

  -- Rewrite the implementation into the mathematical min-of-counts form.
  have himpl :
      implementation text =
        Nat.min (charCount text 'b')
          (Nat.min (charCount text 'a')
            (Nat.min (charCount text 'l' / 2)
              (Nat.min (charCount text 'o' / 2) (charCount text 'n')))) := by
    unfold implementation
    -- Use the computed fold counts.
    have hfold_lambda :
        text.foldl
            (fun (acc : Nat × Nat × Nat × Nat × Nat) ch =>
              let (b, a, l, o, n) := acc
              if ch = 'b' then (b + 1, a, l, o, n)
              else if ch = 'a' then (b, a + 1, l, o, n)
              else if ch = 'l' then (b, a, l + 1, o, n)
              else if ch = 'o' then (b, a, l, o + 1, n)
              else if ch = 'n' then (b, a, l, o, n + 1)
              else acc)
            (0, 0, 0, 0, 0) =
          (charCount text 'b',
           charCount text 'a',
           charCount text 'l',
           charCount text 'o',
           charCount text 'n') := by
      simpa [countStep] using fold_counts_zero
    simp [hfold_lambda]

  -- Now prove the postcondition.
  unfold postcondition
  constructor
  · -- Feasibility
    -- work with the simplified implementation expression
    rw [himpl]
    unfold feasibleBalloons
    -- abbreviate the nested mins
    set r1 : Nat :=
      Nat.min (charCount text 'a')
        (Nat.min (charCount text 'l' / 2)
          (Nat.min (charCount text 'o' / 2) (charCount text 'n')))
    set r : Nat := Nat.min (charCount text 'b') r1

    have hr_b : r ≤ charCount text 'b' := by
      simpa [r] using (min_le_left (charCount text 'b') r1)

    have hr_r1 : r ≤ r1 := by
      simpa [r] using (min_le_right (charCount text 'b') r1)

    have hr_a : r ≤ charCount text 'a' := by
      have : r1 ≤ charCount text 'a' := by
        -- r1 = min (count a) ...
        simpa [r1] using
          (min_le_left (charCount text 'a')
            (Nat.min (charCount text 'l' / 2)
              (Nat.min (charCount text 'o' / 2) (charCount text 'n'))))
      exact le_trans hr_r1 this

    have hr_lDiv : r ≤ charCount text 'l' / 2 := by
      -- r ≤ r1 ≤ r2 ≤ count l / 2
      have hr_r2 : r ≤
          Nat.min (charCount text 'l' / 2)
            (Nat.min (charCount text 'o' / 2) (charCount text 'n')) := by
        have : r1 ≤
            Nat.min (charCount text 'l' / 2)
              (Nat.min (charCount text 'o' / 2) (charCount text 'n')) := by
          simpa [r1] using
            (min_le_right (charCount text 'a')
              (Nat.min (charCount text 'l' / 2)
                (Nat.min (charCount text 'o' / 2) (charCount text 'n'))))
        exact le_trans hr_r1 this
      have :
          Nat.min (charCount text 'l' / 2)
              (Nat.min (charCount text 'o' / 2) (charCount text 'n'))
            ≤ charCount text 'l' / 2 := by
        simpa using
          (min_le_left (charCount text 'l' / 2)
            (Nat.min (charCount text 'o' / 2) (charCount text 'n')))
      exact le_trans hr_r2 this

    have hr_oDiv : r ≤ charCount text 'o' / 2 := by
      have hr_r3 : r ≤ Nat.min (charCount text 'o' / 2) (charCount text 'n') := by
        have hr_r2 : r ≤
            Nat.min (charCount text 'l' / 2)
              (Nat.min (charCount text 'o' / 2) (charCount text 'n')) := by
          have : r1 ≤
              Nat.min (charCount text 'l' / 2)
                (Nat.min (charCount text 'o' / 2) (charCount text 'n')) := by
            simpa [r1] using
              (min_le_right (charCount text 'a')
                (Nat.min (charCount text 'l' / 2)
                  (Nat.min (charCount text 'o' / 2) (charCount text 'n'))))
          exact le_trans hr_r1 this
        have :
            Nat.min (charCount text 'l' / 2)
                (Nat.min (charCount text 'o' / 2) (charCount text 'n'))
              ≤ Nat.min (charCount text 'o' / 2) (charCount text 'n') := by
          simpa using
            (min_le_right (charCount text 'l' / 2)
              (Nat.min (charCount text 'o' / 2) (charCount text 'n')))
        exact le_trans hr_r2 this
      have : Nat.min (charCount text 'o' / 2) (charCount text 'n') ≤ charCount text 'o' / 2 := by
        simpa using (min_le_left (charCount text 'o' / 2) (charCount text 'n'))
      exact le_trans hr_r3 this

    have hr_n : r ≤ charCount text 'n' := by
      have hr_r3 : r ≤ Nat.min (charCount text 'o' / 2) (charCount text 'n') := by
        have hr_r2 : r ≤
            Nat.min (charCount text 'l' / 2)
              (Nat.min (charCount text 'o' / 2) (charCount text 'n')) := by
          have : r1 ≤
              Nat.min (charCount text 'l' / 2)
                (Nat.min (charCount text 'o' / 2) (charCount text 'n')) := by
            simpa [r1] using
              (min_le_right (charCount text 'a')
                (Nat.min (charCount text 'l' / 2)
                  (Nat.min (charCount text 'o' / 2) (charCount text 'n'))))
          exact le_trans hr_r1 this
        have :
            Nat.min (charCount text 'l' / 2)
                (Nat.min (charCount text 'o' / 2) (charCount text 'n'))
              ≤ Nat.min (charCount text 'o' / 2) (charCount text 'n') := by
          simpa using
            (min_le_right (charCount text 'l' / 2)
              (Nat.min (charCount text 'o' / 2) (charCount text 'n')))
        exact le_trans hr_r2 this
      have : Nat.min (charCount text 'o' / 2) (charCount text 'n') ≤ charCount text 'n' := by
        simpa using (min_le_right (charCount text 'o' / 2) (charCount text 'n'))
      exact le_trans hr_r3 this

    have hr_l : 2 * r ≤ charCount text 'l' := by
      have : r * 2 ≤ charCount text 'l' :=
        (Nat.le_div_iff_mul_le (by decide : 0 < (2 : Nat))).1 hr_lDiv
      simpa [Nat.mul_comm] using this

    have hr_o : 2 * r ≤ charCount text 'o' := by
      have : r * 2 ≤ charCount text 'o' :=
        (Nat.le_div_iff_mul_le (by decide : 0 < (2 : Nat))).1 hr_oDiv
      simpa [Nat.mul_comm] using this

    -- Assemble the conjunctions
    refine And.intro ?_ (And.intro ?_ (And.intro ?_ (And.intro ?_ ?_)))
    · simpa [r] using hr_b
    · simpa [r] using hr_a
    · simpa [r] using hr_l
    · simpa [r] using hr_o
    · simpa [r] using hr_n

  · -- Maximality
    intro k hk
    rw [himpl]
    unfold feasibleBalloons at hk
    rcases hk with ⟨hk_b, hk_a, hk_l, hk_o, hk_n⟩

    have hk_lDiv : k ≤ charCount text 'l' / 2 := by
      apply (Nat.le_div_iff_mul_le (by decide : 0 < (2 : Nat))).2
      -- need k*2 ≤ count l
      have : 2 * k ≤ charCount text 'l' := hk_l
      simpa [Nat.mul_comm] using this

    have hk_oDiv : k ≤ charCount text 'o' / 2 := by
      apply (Nat.le_div_iff_mul_le (by decide : 0 < (2 : Nat))).2
      have : 2 * k ≤ charCount text 'o' := hk_o
      simpa [Nat.mul_comm] using this

    have hk_r3 : k ≤ Nat.min (charCount text 'o' / 2) (charCount text 'n') :=
      le_min hk_oDiv hk_n

    have hk_r2 :
        k ≤ Nat.min (charCount text 'l' / 2)
              (Nat.min (charCount text 'o' / 2) (charCount text 'n')) :=
      le_min hk_lDiv hk_r3

    have hk_r1 :
        k ≤ Nat.min (charCount text 'a')
              (Nat.min (charCount text 'l' / 2)
                (Nat.min (charCount text 'o' / 2) (charCount text 'n'))) :=
      le_min hk_a hk_r2

    have hk_r :
        k ≤ Nat.min (charCount text 'b')
              (Nat.min (charCount text 'a')
                (Nat.min (charCount text 'l' / 2)
                  (Nat.min (charCount text 'o' / 2) (charCount text 'n')))) :=
      le_min hk_b hk_r1

    simpa using hk_r
end Proof
