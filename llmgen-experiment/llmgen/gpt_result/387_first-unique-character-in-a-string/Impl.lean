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
    387. First Unique Character in a String: return the index of the first non-repeating character.
    **Important: complexity should be O(n) time and O(1) space**
    Natural language breakdown:
    1. The input is a finite sequence of characters s indexed from 0.
    2. A character at index i is non-repeating (unique) if it occurs in s exactly once.
    3. If there exists at least one index i whose character is unique, the function returns the smallest such index.
    4. If no unique character exists, the function returns -1.
    5. All characters are ASCII, meaning each character code is < 128.
-/

section Specs
-- Count how many times a character occurs in the array.
-- Uses Array.countP (no List conversions).
def charCount (s : Array Char) (c : Char) : Nat :=
  s.countP (fun x => x = c)

-- A simple ASCII predicate (as required by constraints).
def isASCII (c : Char) : Prop := c.toNat < 128

-- Input constraint: all characters are ASCII.
def precondition (s : Array Char) : Prop :=
  ∀ (i : Nat), i < s.size → isASCII (s[i]!)

def postcondition (s : Array Char) (result : Int) : Prop :=
  -- If there is a unique character, result is the smallest index with count = 1.
  ((∃ (i : Nat), i < s.size ∧ charCount s (s[i]!) = 1) →
      0 ≤ result ∧
      (result.toNat < s.size) ∧
      charCount s (s[result.toNat]!) = 1 ∧
      (∀ (j : Nat), j < result.toNat → charCount s (s[j]!) ≠ 1))
  ∧
  -- If there is no unique character, result is -1.
  ((¬ (∃ (i : Nat), i < s.size ∧ charCount s (s[i]!) = 1)) →
      result = (-1) ∧
      (∀ (i : Nat), i < s.size → charCount s (s[i]!) ≠ 1))
end Specs

section Impl
method FirstUniqueCharIndex (s : Array Char)
  return (result : Int)
  require precondition s
  ensures postcondition s result
  do
  -- O(n) time, O(1) extra space (fixed-size ASCII table)
  let mut counts : Array Nat := Array.replicate 128 0

  -- First pass: count occurrences of each ASCII character.
  let mut i : Nat := 0
  while i < s.size
    -- i is always within array bounds (as a prefix length)
    invariant "inv1_i_le" i ≤ s.size
    -- counts is always the fixed ASCII table
    invariant "inv1_counts_size" counts.size = 128
    -- processed prefix characters are ASCII (needed for safe indexing into counts)
    invariant "inv1_ascii_prefix" (∀ k : Nat, k < i → s[k]!.toNat < 128)
    -- counts tracks exact occurrences of each ASCII code in the processed prefix
    invariant "inv1_counts_prefix" (∀ code : Nat, code < 128 → counts[code]! = (s.extract 0 i).countP (fun x => x.toNat = code))
    done_with i = s.size
    decreasing s.size - i
  do
    let ch : Char := s[i]!
    let code : Nat := ch.toNat
    -- Safe because of precondition: isASCII ch means code < 128
    let cur : Nat := counts[code]!
    counts := counts.set! code (cur + 1)
    i := i + 1

  -- Second pass: find first index with count = 1.
  let mut j : Nat := 0
  let mut ans : Int := (-1)
  let mut found : Bool := false
  while j < s.size ∧ (found = false)
    -- j stays within bounds
    invariant "inv2_j_le" j ≤ s.size
    -- counts table size is unchanged
    invariant "inv2_counts_size" counts.size = 128
    -- all characters in s are ASCII (from the method precondition)
    invariant "inv2_ascii_all" (∀ k : Nat, k < s.size → s[k]!.toNat < 128)
    -- counts equals the total occurrences of each ASCII code in s
    invariant "inv2_counts_total" (∀ code : Nat, code < 128 → counts[code]! = s.countP (fun x => x.toNat = code))
    -- specialize counts_total to the actual characters in s (matches postcondition's charCount)
    invariant "inv2_counts_charCount" (∀ t : Nat, t < s.size → counts[s[t]!.toNat]! = charCount s (s[t]!))
    -- while still searching, ans remains -1
    invariant "inv2_notfound_ans" (found = false → ans = (-1))
    -- if found is set, ans is exactly the current index and that position is unique
    invariant "inv2_found_ans" (found = true → (ans = Int.ofNat j ∧ j < s.size ∧ counts[s[j]!.toNat]! = 1))
    -- all earlier positions were checked and were not unique
    invariant "inv2_no_unique_before_j" (∀ t : Nat, t < j → counts[s[t]!.toNat]! ≠ 1)
    done_with (found = true ∨ j = s.size)
    -- Decrease either by advancing j, or by switching found from false to true
    decreasing (if found then 0 else s.size - j)
  do
    let ch : Char := s[j]!
    let code : Nat := ch.toNat
    if counts[code]! = 1 then
      ans := (Int.ofNat j)
      found := true
    else
      j := j + 1

  return ans
end Impl

section TestCases
-- Test case 1: Example 1
-- Input: "leetcode" -> output 0
-- ('l' occurs once and is the first such character)
def test1_s : Array Char := #['l','e','e','t','c','o','d','e']
def test1_Expected : Int := 0

-- Test case 2: Example 2
-- Input: "loveleetcode" -> output 2
-- (first unique is 'v' at index 2)
def test2_s : Array Char := #['l','o','v','e','l','e','e','t','c','o','d','e']
def test2_Expected : Int := 2

-- Test case 3: Example 3
-- Input: "aabb" -> output -1
-- (no unique character)
def test3_s : Array Char := #['a','a','b','b']
def test3_Expected : Int := (-1)

-- Test case 4: Empty input (degenerate)
-- No characters => no unique => -1
def test4_s : Array Char := #[]
def test4_Expected : Int := (-1)

-- Test case 5: Singleton input (boundary)
-- Only character is unique => index 0
def test5_s : Array Char := #['z']
def test5_Expected : Int := 0

-- Test case 6: Unique appears after repeats
-- "aabc" => 'b' at index 2 is the first unique
def test6_s : Array Char := #['a','a','b','c']
def test6_Expected : Int := 2

-- Test case 7: All same characters
-- "aaaa" => -1
def test7_s : Array Char := #['a','a','a','a']
def test7_Expected : Int := (-1)

-- Test case 8: Includes ASCII control char and repeats
-- [NUL, 'a', 'a'] => NUL is unique at index 0
-- NUL is ASCII (code 0)
def test8_s : Array Char := #[('\u0000'), 'a', 'a']
def test8_Expected : Int := 0

-- Test case 9: Multiple uniques; must pick the smallest index
-- "abac" => 'b' at 1 and 'c' at 3 are unique, so answer is 1
def test9_s : Array Char := #['a','b','a','c']
def test9_Expected : Int := 1
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((FirstUniqueCharIndex test1_s).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((FirstUniqueCharIndex test2_s).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((FirstUniqueCharIndex test3_s).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((FirstUniqueCharIndex test4_s).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((FirstUniqueCharIndex test5_s).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((FirstUniqueCharIndex test6_s).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((FirstUniqueCharIndex test7_s).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((FirstUniqueCharIndex test8_s).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((FirstUniqueCharIndex test9_s).run), DivM.res test9_Expected ]
end Assertions

section Pbt
velvet_plausible_test FirstUniqueCharIndex (config := { maxMs := some 20000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000

theorem goal_0
    (s : Array Char)
    (require_1 : ∀ i < s.size, s[i]!.toNat < OfNat.ofNat 128)
    (counts : Array ℕ)
    (i : ℕ)
    (invariant_inv1_counts_size : counts.size = OfNat.ofNat 128)
    (invariant_inv1_counts_prefix : ∀ code < OfNat.ofNat 128, counts[code]! = Array.countP (fun x => decide (x.toNat = code)) (s.extract (OfNat.ofNat 0) i))
    (if_pos : i < s.size)
    : ∀ code < OfNat.ofNat 128, (counts.setIfInBounds s[i]!.toNat (counts[s[i]!.toNat]! + OfNat.ofNat 1))[code]! = Array.countP (fun x => decide (x.toNat = code)) (s.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) := by
  intro code hcode

  have hiASCII : s[i]!.toNat < 128 := by
    simpa using (require_1 i if_pos)
  have hidx : s[i]!.toNat < counts.size := by
    simpa [invariant_inv1_counts_size] using hiASCII
  have hcodeCounts : code < counts.size := by
    simpa [invariant_inv1_counts_size] using hcode

  -- express the longer prefix by pushing the next element
  have hextract' : s.extract 0 (i + 1) = (s.extract 0 i).push (s[i]'(by exact if_pos)) := by
    simpa using (@Array.extract_succ_right Char s 0 i (Nat.succ_pos i) if_pos)
  have hextract : s.extract 0 (i + 1) = (s.extract 0 i).push (s[i]!) := by
    -- `get!` agrees with `get` for an in-bounds index
    have hget : s[i]! = s[i]'(by exact if_pos) := by
      simp [Array.get!, if_pos]
    simpa [hget] using hextract'

  let p : Char → Bool := fun x => decide (x.toNat = code)

  have hprefix : counts[code]! = Array.countP p (s.extract 0 i) := by
    simpa [p] using invariant_inv1_counts_prefix code (by simpa using hcode)

  by_cases hEq : s[i]!.toNat = code
  · -- updated entry
    have hp : p (s[i]!) = true := by
      simp [p, hEq]

    have hR : Array.countP p (s.extract 0 (i + 1)) = Array.countP p (s.extract 0 i) + 1 := by
      simpa [hextract, Array.append_singleton, Array.countP_append, hp, p]

    have hprefix' : counts[s[i]!.toNat]! = Array.countP p (s.extract 0 i) := by
      simpa [hEq] using hprefix

    -- the updated array returns the new value at the updated index
    have hset : (counts.setIfInBounds s[i]!.toNat (Array.countP p (s.extract 0 i) + 1))[code]! =
        Array.countP p (s.extract 0 i) + 1 := by
      simp [Array.get!, Array.getElem?_setIfInBounds, hEq, hidx, hcodeCounts]

    -- finish by rewriting the goal to these normalized forms
    calc
      (counts.setIfInBounds s[i]!.toNat (counts[s[i]!.toNat]! + 1))[code]!
          = (counts.setIfInBounds s[i]!.toNat (Array.countP p (s.extract 0 i) + 1))[code]! := by
              simp [hprefix']
      _ = Array.countP p (s.extract 0 i) + 1 := hset
      _ = Array.countP p (s.extract 0 (i + 1)) := by
            simpa using (Eq.symm hR)
      _ = Array.countP (fun x => decide (x.toNat = code)) (s.extract 0 (i + 1)) := by
            simp [p]
      _ = Array.countP (fun x => decide (x.toNat = code)) (s.extract 0 (i + OfNat.ofNat 1)) := by
            simp

  · -- unchanged entry
    have hL : (counts.setIfInBounds s[i]!.toNat (counts[s[i]!.toNat]! + 1))[code]! = counts[code]! := by
      simp [Array.get!, Array.getElem?_setIfInBounds, hEq, hidx, hcodeCounts]

    have hp : p (s[i]!) = false := by
      simp [p, hEq]

    have hR : Array.countP p (s.extract 0 (i + 1)) = Array.countP p (s.extract 0 i) := by
      simpa [hextract, Array.append_singleton, Array.countP_append, hp, p]

    calc
      (counts.setIfInBounds s[i]!.toNat (counts[s[i]!.toNat]! + 1))[code]!
          = counts[code]! := hL
      _ = Array.countP p (s.extract 0 i) := hprefix
      _ = Array.countP p (s.extract 0 (i + 1)) := by simpa using (Eq.symm hR)
      _ = Array.countP (fun x => decide (x.toNat = code)) (s.extract 0 (i + 1)) := by simp [p]
      _ = Array.countP (fun x => decide (x.toNat = code)) (s.extract 0 (i + OfNat.ofNat 1)) := by simp

theorem goal_1
    (s : Array Char)
    (i_1 : Array ℕ)
    (invariant_inv1_counts_size : i_1.size = OfNat.ofNat 128)
    (invariant_inv1_counts_prefix : ∀ code < OfNat.ofNat 128, i_1[code]! = Array.countP (fun x => decide (x.toNat = code)) s)
    : ∀ code < OfNat.ofNat 128, i_1[code]! = Array.countP (fun x => decide (x.toNat = code)) s := by
    intros; expose_names; try simp_all; try grind

theorem goal_2
    (s : Array Char)
    (i_1 : Array ℕ)
    (invariant_inv1_ascii_prefix : ∀ k < s.size, s[k]!.toNat < OfNat.ofNat 128)
    (invariant_inv1_counts_prefix : ∀ code < OfNat.ofNat 128, i_1[code]! = Array.countP (fun x => decide (x.toNat = code)) s)
    : ∀ t < s.size, i_1[s[t]!.toNat]! = Array.countP (fun x => decide (x = s[t]!)) s := by
  intro t ht
  have hcode : s[t]!.toNat < (128 : Nat) := by
    simpa using invariant_inv1_ascii_prefix t ht
  have htable : i_1[s[t]!.toNat]! = Array.countP (fun x => decide (x.toNat = s[t]!.toNat)) s := by
    simpa using (invariant_inv1_counts_prefix (s[t]!.toNat) hcode)
  -- Rewrite the table entry using the invariant, then change the predicate.
  calc
    i_1[s[t]!.toNat]! = Array.countP (fun x => decide (x.toNat = s[t]!.toNat)) s := htable
    _ = Array.countP (fun x => decide (x = s[t]!)) s := by
      -- `countP` is extensional in its predicate.
      apply Array.countP_congr
      intro x hx
      -- Show the two predicates agree, using injectivity of `Char.toNat`.
      have hxiff : (x.toNat = s[t]!.toNat) ↔ (x = s[t]!) := by
        constructor
        · intro h
          -- Use `Char.ofNat` as a left inverse of `toNat`.
          have : Char.ofNat x.toNat = Char.ofNat (s[t]!).toNat := congrArg Char.ofNat h
          simpa [Char.ofNat_toNat] using this
        · intro h
          simpa [h]
      have hdec : decide (x.toNat = s[t]!.toNat) = decide (x = s[t]!) :=
        Bool.decide_congr hxiff
      simpa [hdec]

theorem goal_3
    (s : Array Char)
    (i_1 : Array ℕ)
    (invariant_inv2_counts_charCount : ∀ t < s.size, i_1[s[t]!.toNat]! = Array.countP (fun x => decide (x = s[t]!)) s)
    (i_4 : ℤ)
    (i_5 : Bool)
    (j_1 : ℕ)
    (invariant_inv2_notfound_ans : i_5 = false → i_4 = -OfNat.ofNat 1)
    (invariant_inv2_no_unique_before_j : ∀ t < j_1, ¬i_1[s[t]!.toNat]! = OfNat.ofNat 1)
    (done_2 : i_5 = true ∨ j_1 = s.size)
    (invariant_inv2_found_ans : i_5 = true → i_4 = j_1.cast ∧ j_1 < s.size ∧ i_1[s[j_1]!.toNat]! = OfNat.ofNat 1)
    : postcondition s i_4 := by
  unfold postcondition
  constructor
  · intro hex
    -- show we must be in the found=true case
    have hfound : i_5 = true := by
      by_contra hne
      have hfalse : i_5 = false := by
        cases hi : i_5 with
        | false => rfl
        | true =>
          have : False := hne (by simpa [hi])
          exact False.elim this
      have hj : j_1 = s.size := by
        cases done_2 with
        | inl ht => exact False.elim (hne ht)
        | inr hj => exact hj
      have hnone : ∀ t < s.size, charCount s (s[t]!) ≠ 1 := by
        intro t ht
        have htj : t < j_1 := by simpa [hj] using ht
        have hnot : i_1[s[t]!.toNat]! ≠ 1 := by
          have : ¬ i_1[s[t]!.toNat]! = 1 := invariant_inv2_no_unique_before_j t htj
          simpa using this
        have hcc : i_1[s[t]!.toNat]! = charCount s (s[t]!) := by
          simpa [charCount] using invariant_inv2_counts_charCount t ht
        simpa [hcc] using hnot
      rcases hex with ⟨i, hi, huniq⟩
      exact (hnone i hi) huniq

    have hfa := invariant_inv2_found_ans hfound
    rcases hfa with ⟨hans, hjlt, hcount1⟩

    have hi4toNat : i_4.toNat = j_1 := by
      -- `j_1.cast` is the nat-cast to `Int`
      simpa [hans] using (Int.toNat_natCast j_1)

    have hnonneg : 0 ≤ i_4 := by
      simpa [hans] using (Int.ofNat_nonneg j_1)

    have huniqj : charCount s (s[j_1]!) = 1 := by
      have hccj : i_1[s[j_1]!.toNat]! = charCount s (s[j_1]!) := by
        simpa [charCount] using invariant_inv2_counts_charCount j_1 hjlt
      calc
        charCount s (s[j_1]!) = i_1[s[j_1]!.toNat]! := by simpa using hccj.symm
        _ = 1 := by simpa using hcount1

    refine And.intro hnonneg ?_
    refine And.intro ?_ ?_
    · -- bounds
      simpa [hi4toNat] using hjlt
    · refine And.intro ?_ ?_
      · -- unique at the returned index
        simpa [hi4toNat] using huniqj
      · -- no earlier index is unique
        intro t ht
        have htj : t < j_1 := by simpa [hi4toNat] using ht
        have htS : t < s.size := lt_trans htj hjlt
        have hnot : i_1[s[t]!.toNat]! ≠ 1 := by
          have : ¬ i_1[s[t]!.toNat]! = 1 := invariant_inv2_no_unique_before_j t htj
          simpa using this
        have hcc : i_1[s[t]!.toNat]! = charCount s (s[t]!) := by
          simpa [charCount] using invariant_inv2_counts_charCount t htS
        simpa [hcc] using hnot

  · intro hnoUnique
    by_cases h5 : i_5 = true
    · -- found=true would give a unique character, contradicting `hnoUnique`
      have hfa := invariant_inv2_found_ans h5
      rcases hfa with ⟨hans, hjlt, hcount1⟩
      have hccj : i_1[s[j_1]!.toNat]! = charCount s (s[j_1]!) := by
        simpa [charCount] using invariant_inv2_counts_charCount j_1 hjlt
      have huniqj : charCount s (s[j_1]!) = 1 := by
        calc
          charCount s (s[j_1]!) = i_1[s[j_1]!.toNat]! := by simpa using hccj.symm
          _ = 1 := by simpa using hcount1
      have : (∃ i : Nat, i < s.size ∧ charCount s (s[i]!) = 1) := ⟨j_1, hjlt, huniqj⟩
      exact False.elim (hnoUnique this)
    · -- thus found=false
      have hfalse : i_5 = false := by
        cases hi : i_5 with
        | false => rfl
        | true =>
          have : False := h5 (by simpa [hi])
          exact False.elim this
      have hans : i_4 = (-1) := by
        simpa using invariant_inv2_notfound_ans hfalse
      have hj : j_1 = s.size := by
        cases done_2 with
        | inl ht => exact False.elim (h5 ht)
        | inr hj => exact hj
      refine And.intro hans ?_
      intro t ht
      have htj : t < j_1 := by simpa [hj] using ht
      have hnot : i_1[s[t]!.toNat]! ≠ 1 := by
        have : ¬ i_1[s[t]!.toNat]! = 1 := invariant_inv2_no_unique_before_j t htj
        simpa using this
      have hcc : i_1[s[t]!.toNat]! = charCount s (s[t]!) := by
        simpa [charCount] using invariant_inv2_counts_charCount t ht
      simpa [hcc] using hnot


prove_correct FirstUniqueCharIndex by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at *); try (conv => congr <;> simp) ; try expose_names)
  exact (goal_0 s require_1 counts i invariant_inv1_counts_size invariant_inv1_counts_prefix if_pos)
  exact (goal_1 s i_1 invariant_inv1_counts_size invariant_inv1_counts_prefix)
  exact (goal_2 s i_1 invariant_inv1_ascii_prefix invariant_inv1_counts_prefix)
  exact (goal_3 s i_1 invariant_inv2_counts_charCount i_4 i_5 j_1 invariant_inv2_notfound_ans invariant_inv2_no_unique_before_j done_2 invariant_inv2_found_ans)
end Proof
