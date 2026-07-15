/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: cce4f184-c43c-4cbf-b159-9c345ed90936

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem correctness_goal (ransomNote : List Char) (magazine : List Char) (h_precond : precondition ransomNote magazine) : postcondition ransomNote magazine (implementation ransomNote magazine)
-/

import Lean

import Mathlib.Tactic


set_option maxHeartbeats 10000000

section Specs

-- Never add new imports here

set_option maxHeartbeats 10000000

set_option pp.coercions false

/- Problem Description
    383. Ransom Note: decide whether one note can be constructed from the letters of a magazine.
    **Important: complexity should be O(m + n) time and O(1) space**
    Natural language breakdown:
    1. Inputs are two sequences of characters: ransomNote and magazine.
    2. A character from magazine can be used at most once when constructing the ransomNote.
    3. Construction is possible exactly when every character occurs in magazine at least as many times as it occurs in ransomNote.
    4. The function returns true iff construction is possible; otherwise it returns false.
    5. The empty ransom note is always constructible from any magazine.
-/

-- Helper: multiset-style availability condition via per-character counts.
-- Mathlib provides `List.count` for decidable equality types.
def canConstructProp (ransomNote : List Char) (magazine : List Char) : Prop :=
  ∀ c : Char, ransomNote.count c ≤ magazine.count c

def precondition (ransomNote : List Char) (magazine : List Char) : Prop :=
  True

def postcondition (ransomNote : List Char) (magazine : List Char) (result : Bool) : Prop :=
  (result = true ↔ canConstructProp ransomNote magazine)

end Specs

section Impl

def implementation (ransomNote : List Char) (magazine : List Char) : Bool :=
  -- Use a fixed-size frequency table over all possible `Char` values.
  -- In Lean, `Char` is a Unicode scalar value, so `Char.toNat < 0x110000`.
  let maxChar : Nat := 0x110000
  let idx (c : Char) : Nat := c.toNat
  let inc (counts : Array Nat) (c : Char) : Array Nat :=
    let i := idx c
    -- `i` is always in bounds because `counts` has length `maxChar`.
    let v := counts.get! i
    counts.set! i (v + 1)
  let dec (counts : Array Nat) (c : Char) : Option (Array Nat) :=
    let i := idx c
    let v := counts.get! i
    match v with
    | 0 => none
    | Nat.succ v' => some (counts.set! i v')
  let counts0 : Array Nat := magazine.foldl inc (Array.mkArray maxChar 0)
  let step (st : Option (Array Nat)) (c : Char) : Option (Array Nat) :=
    match st with
    | none => none
    | some counts => dec counts c
  match ransomNote.foldl step (some counts0) with
  | some _ => true
  | none => false

end Impl

section TestCases

-- Test case 1: Example 1: ransomNote = "a", magazine = "b" => false
def test1_ransomNote : List Char := ['a']

def test1_magazine : List Char := ['b']

def test1_Expected : Bool := false

-- Test case 2: Example 2: ransomNote = "aa", magazine = "ab" => false
def test2_ransomNote : List Char := ['a', 'a']

def test2_magazine : List Char := ['a', 'b']

def test2_Expected : Bool := false

-- Test case 3: Example 3: ransomNote = "aa", magazine = "aab" => true
def test3_ransomNote : List Char := ['a', 'a']

def test3_magazine : List Char := ['a', 'a', 'b']

def test3_Expected : Bool := true

-- Test case 4: Edge: empty ransom note, empty magazine => true
def test4_ransomNote : List Char := []

def test4_magazine : List Char := []

def test4_Expected : Bool := true

-- Test case 5: Edge: empty ransom note, nonempty magazine => true
def test5_ransomNote : List Char := []

def test5_magazine : List Char := ['x', 'y']

def test5_Expected : Bool := true

-- Test case 6: Edge: nonempty ransom note, empty magazine => false
def test6_ransomNote : List Char := ['z']

def test6_magazine : List Char := []

def test6_Expected : Bool := false

-- Test case 7: Exact match with repeats => true
def test7_ransomNote : List Char := ['a', 'b', 'c', 'a']

def test7_magazine : List Char := ['a', 'b', 'c', 'a']

def test7_Expected : Bool := true

-- Test case 8: Insufficient multiplicity for one letter => false
def test8_ransomNote : List Char := ['a', 'b', 'b']

def test8_magazine : List Char := ['b', 'a']

def test8_Expected : Bool := false

-- Test case 9: Magazine has extra letters and permuted order => true
def test9_ransomNote : List Char := ['c', 'a', 't']

def test9_magazine : List Char := ['t', 'a', 'c', 'h', 'e', 'r']

def test9_Expected : Bool := true

end TestCases

section Proof

noncomputable section AristotleLemmas

/-
Helper definitions for the proof: `maxChar`, `build_counts` (constructs frequency array from magazine), and `consume_step` (updates counts for a character in ransom note).
-/
section ProofHelpers

def maxChar : Nat := 0x110000

def build_counts (magazine : List Char) : Array Nat :=
  magazine.foldl (fun counts c =>
    let i := c.toNat
    let v := counts.get! i
    counts.set! i (v + 1)) (Array.mkArray maxChar 0)

def consume_step (st : Option (Array Nat)) (c : Char) : Option (Array Nat) :=
  match st with
  | none => none
  | some counts =>
    let i := c.toNat
    let v := counts.get! i
    match v with
    | 0 => none
    | Nat.succ v' => some (counts.set! i v')

end ProofHelpers

/-
The implementation is equivalent to using the helper functions `build_counts` and `consume_step`.
-/
theorem implementation_eq (ransomNote : List Char) (magazine : List Char) :
  implementation ransomNote magazine =
    match ransomNote.foldl consume_step (some (build_counts magazine)) with
    | some _ => true
    | none => false := by
  congr! 3

/-
Definition of the loop invariant: if the state is `some counts`, then the counts match the remaining characters in the magazine; if `none`, then the ransom note requires more characters than available.
-/
def LoopInvariant (magazine : List Char) (processed : List Char) (st : Option (Array Nat)) : Prop :=
  match st with
  | some counts =>
    (∀ c, counts.get! c.toNat = magazine.count c - processed.count c) ∧
    (∀ c, processed.count c ≤ magazine.count c) ∧
    counts.size = maxChar
  | none =>
    ∃ c, processed.count c > magazine.count c

/-
`build_counts` returns an array of size `maxChar` where the value at index `c.toNat` is the count of `c` in `magazine`.
-/
theorem build_counts_correct (magazine : List Char) :
  let counts := build_counts magazine
  counts.size = maxChar ∧ ∀ c, counts.get! c.toNat = magazine.count c := by
  induction' magazine using List.reverseRecOn with m ih;
  · simp [build_counts, maxChar];
    norm_num [ Array.mkArray ];
    intro c; exact (by
    rw [ Array.get! ];
    rw [ Array.getD ] ; aesop);
  · unfold build_counts at *; simp_all +decide [ List.foldl_append ] ;
    simp_all +decide [ List.count_cons, Array.get! ];
    intro c; by_cases h : ih = c <;> simp +decide [ *, Array.getElem?_setIfInBounds ] ;
    · rw [ if_pos ];
      · rfl;
      · -- Since `c` is a character, its `toNat` value is less than `maxChar` by definition.
        have h_toNat_lt_maxChar : c.toNat < maxChar := by
          have h_maxChar : maxChar = 0x110000 := by
            rfl
          have h_toNat_lt_maxChar : ∀ c : Char, c.toNat < 0x110000 := by
            intro c; exact (by
            have := c.2;
            rw [ Char.toNat ];
            grind);
          exact h_maxChar ▸ h_toNat_lt_maxChar c;
        exact h_toNat_lt_maxChar;
    · split_ifs <;> simp_all +decide [ Char.ext_iff ];
      · exact False.elim <| h <| by exact?;
      · grind

/-
The loop invariant holds initially: the counts array matches the magazine counts, and the processed list is empty.
-/
theorem invariant_init (magazine : List Char) :
  LoopInvariant magazine [] (some (build_counts magazine)) := by
  -- By definition of `LoopInvariant`, we need to show that the counts array matches the magazine counts, and the processed list is empty.
  unfold LoopInvariant;
  convert build_counts_correct magazine using 1 ; aesop

/-
The loop invariant is preserved after processing one character `c`. If the count becomes 0, we transition to `none` state correctly; otherwise we update the count and stay in `some` state.
-/
theorem invariant_step (magazine : List Char) (processed : List Char) (st : Option (Array Nat)) (c : Char) :
  LoopInvariant magazine processed st →
  LoopInvariant magazine (processed ++ [c]) (consume_step st c) := by
  intro hst;
  unfold LoopInvariant at *;
  cases st <;> simp_all +decide [ List.count_cons ];
  · exact hst.imp fun x hx => lt_of_lt_of_le hx ( Nat.le_add_right _ _ );
  · unfold consume_step;
    cases h : ‹Array ℕ›.get! c.toNat <;> simp_all +decide [ List.count_cons ];
    · grind;
    · constructor <;> intro d <;> by_cases hd : c = d <;> simp_all +decide [ Nat.sub_succ ];
      · simp_all +decide [ Array.get! ];
        grind;
      · by_cases h : c.toNat = d.toNat <;> simp_all +decide [ Array.get! ];
        exact False.elim <| hd <| by have := Char.ofNat_toNat c; have := Char.ofNat_toNat d; aesop;
      · omega

/-
The loop invariant is preserved over the entire `foldl` operation on the suffix of the ransom note.
-/
theorem invariant_foldl (magazine : List Char) (processed : List Char) (suffix : List Char) (st : Option (Array Nat)) :
  LoopInvariant magazine processed st →
  LoopInvariant magazine (processed ++ suffix) (suffix.foldl consume_step st) := by
  induction' suffix using List.reverseRecOn with c suffix ih generalizing st processed;
  · aesop;
  · simp_all +decide [ ← List.append_assoc, List.foldl_append ];
    exact fun h => invariant_step _ _ _ _ ( ih _ _ h )

/-
The loop invariant holds after processing the entire ransom note.
-/
theorem invariant_final (ransomNote : List Char) (magazine : List Char) :
  LoopInvariant magazine ransomNote (ransomNote.foldl consume_step (some (build_counts magazine))) := by
  convert invariant_foldl magazine [] ransomNote ( some ( build_counts magazine ) ) _ using 1 ; norm_num [ invariant_init ]

end AristotleLemmas

theorem correctness_goal (ransomNote : List Char) (magazine : List Char) (h_precond : precondition ransomNote magazine) : postcondition ransomNote magazine (implementation ransomNote magazine) := by
    unfold postcondition;
    rw [ implementation_eq ];
    have := invariant_final ransomNote magazine;
    unfold LoopInvariant at this;
    unfold canConstructProp;
    grind

end Proof