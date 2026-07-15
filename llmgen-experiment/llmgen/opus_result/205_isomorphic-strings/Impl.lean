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
    205. Isomorphic Strings: determine whether two strings are isomorphic.
    **Important: complexity should be O(n) time and O(1) space**
    Natural language breakdown:
    1. Inputs are two sequences of characters s and t.
    2. The strings are isomorphic when we can replace each character in s by some character to obtain t.
    3. Replacement must be consistent: if s has the same character at two positions, t must also have the same character at those positions.
    4. Replacement must be injective: if s has different characters at two positions, then t must have different characters at those positions.
    5. The order of characters is preserved; only character identities may change.
    6. Therefore, s and t can be isomorphic only if they have equal length.
    7. A complete characterization is: for all indices i and j within bounds, s[i] = s[j] if and only if t[i] = t[j].
    8. The function returns a Bool that is true exactly when the characterization holds.
-/

section Specs
-- Two lists of characters are isomorphic iff they have the same length and
-- equality of characters is preserved and reflected across all index pairs.
-- This avoids constructing an explicit map while still fully characterizing the condition.

def Isomorphic (s : List Char) (t : List Char) : Prop :=
  s.length = t.length ∧
    ∀ (i : Nat) (j : Nat),
      i < s.length → j < s.length →
        (s[i]! = s[j]!) ↔ (t[i]! = t[j]!)

def precondition (s : List Char) (t : List Char) : Prop :=
  True

def postcondition (s : List Char) (t : List Char) (result : Bool) : Prop :=
  (result = true ↔ Isomorphic s t)
end Specs

section Impl
method IsomorphicStrings (s : List Char) (t : List Char)
  return (result : Bool)
  require precondition s t
  ensures postcondition s t result
  do
  if s.length != t.length then
    return false
  else
    let sArr : Array Char := s.toArray
    let tArr : Array Char := t.toArray
    -- mapS[c] stores the last index+1 where character c appeared in s (0 means unseen)
    -- mapT[c] stores the last index+1 where character c appeared in t (0 means unseen)
    let mut mapS : Array Nat := Array.replicate 256 0
    let mut mapT : Array Nat := Array.replicate 256 0
    let mut i : Nat := 0
    let mut iso : Bool := true
    while i < sArr.size
      -- Bounds on loop counter
      invariant "i_bound" 0 ≤ i ∧ i ≤ sArr.size
      -- Map array sizes are preserved
      invariant "mapS_size" mapS.size = 256
      invariant "mapT_size" mapT.size = 256
      -- Source arrays unchanged
      invariant "sArr_eq" sArr = s.toArray
      invariant "tArr_eq" tArr = t.toArray
      -- Length equality (from else branch)
      invariant "len_eq" s.length = t.length
      invariant "arr_sizes" sArr.size = tArr.size
      -- Map values are bounded by i (store index+1 or 0)
      invariant "mapS_range" ∀ c, c < 256 → mapS[c]! ≤ i
      invariant "mapT_range" ∀ c, c < 256 → mapT[c]! ≤ i
      -- If iso true, partial isomorphism holds for indices < i
      invariant "iso_partial" iso = true →
        ∀ (a : Nat) (b : Nat), a < i → b < i →
          (sArr[a]! = sArr[b]! ↔ tArr[a]! = tArr[b]!)
      -- If iso false, strings are not isomorphic
      invariant "iso_false" iso = false → ¬ Isomorphic s t
      -- mapS[c] > 0: sArr at that position has char c, no later occurrence before i
      invariant "mapS_last" iso = true → ∀ c, c < 256 → mapS[c]! > 0 →
        (sArr[mapS[c]! - 1]!.toNat = c ∧
         ∀ j, mapS[c]! ≤ j → j < i → sArr[j]!.toNat ≠ c)
      -- mapS[c] = 0: c never appeared in sArr[0..i-1]
      invariant "mapS_zero" iso = true → ∀ c, c < 256 → mapS[c]! = 0 →
        ∀ j, j < i → sArr[j]!.toNat ≠ c
      -- mapT[c] > 0: tArr at that position has char c, no later occurrence before i
      invariant "mapT_last" iso = true → ∀ c, c < 256 → mapT[c]! > 0 →
        (tArr[mapT[c]! - 1]!.toNat = c ∧
         ∀ j, mapT[c]! ≤ j → j < i → tArr[j]!.toNat ≠ c)
      -- mapT[c] = 0: c never appeared in tArr[0..i-1]
      invariant "mapT_zero" iso = true → ∀ c, c < 256 → mapT[c]! = 0 →
        ∀ j, j < i → tArr[j]!.toNat ≠ c
      done_with (i = sArr.size ∨ iso = false)
      decreasing sArr.size - i
    do
      let sc := sArr[i]!
      let tc := tArr[i]!
      let scIdx := sc.toNat
      let tcIdx := tc.toNat
      let sVal := mapS[scIdx]!
      let tVal := mapT[tcIdx]!
      if sVal != tVal then
        iso := false
        break
      else
        mapS := mapS.set! scIdx (i + 1)
        mapT := mapT.set! tcIdx (i + 1)
        i := i + 1
    return iso
end Impl

section TestCases
-- Test case 1: Example 1: "egg" vs "add" => true
def test1_s : List Char := ['e', 'g', 'g']
def test1_t : List Char := ['a', 'd', 'd']
def test1_Expected : Bool := true

-- Test case 2: Example 2: "f11" vs "b23" => false
def test2_s : List Char := ['f', '1', '1']
def test2_t : List Char := ['b', '2', '3']
def test2_Expected : Bool := false

-- Test case 3: Example 3: "paper" vs "title" => true
def test3_s : List Char := ['p', 'a', 'p', 'e', 'r']
def test3_t : List Char := ['t', 'i', 't', 'l', 'e']
def test3_Expected : Bool := true

-- Test case 4: Edge case: both empty => true
def test4_s : List Char := []
def test4_t : List Char := []
def test4_Expected : Bool := true

-- Test case 5: Edge case: length mismatch => false
def test5_s : List Char := ['a']
def test5_t : List Char := ['a', 'a']
def test5_Expected : Bool := false

-- Test case 6: Singleton characters (different) => true (map one char to the other)
def test6_s : List Char := ['x']
def test6_t : List Char := ['y']
def test6_Expected : Bool := true

-- Test case 7: Non-injective mapping attempt: "ab" vs "aa" => false
def test7_s : List Char := ['a', 'b']
def test7_t : List Char := ['a', 'a']
def test7_Expected : Bool := false

-- Test case 8: Typical true: "foo" vs "app" (f->a, o->p) => true
def test8_s : List Char := ['f', 'o', 'o']
def test8_t : List Char := ['a', 'p', 'p']
def test8_Expected : Bool := true

-- Test case 9: Typical true: "abca" vs "zbxz" (a->z, b->b, c->x) => true
def test9_s : List Char := ['a', 'b', 'c', 'a']
def test9_t : List Char := ['z', 'b', 'x', 'z']
def test9_Expected : Bool := true
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((IsomorphicStrings test1_s test1_t).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((IsomorphicStrings test2_s test2_t).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((IsomorphicStrings test3_s test3_t).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((IsomorphicStrings test4_s test4_t).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((IsomorphicStrings test5_s test5_t).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((IsomorphicStrings test6_s test6_t).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((IsomorphicStrings test7_s test7_t).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((IsomorphicStrings test8_s test8_t).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((IsomorphicStrings test9_s test9_t).run), DivM.res test9_Expected ]
end Assertions

section Pbt
-- Decidable instance synthesis failed for this method's conditions. Giving up on PBT.

-- velvet_plausible_test IsomorphicStrings (config := { maxMs := some 5000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000

theorem array_getElem!_out_of_bounds (arr : Array ℕ) (idx : ℕ) (h_size : arr.size = 256) (h_ge : idx ≥ 256) : arr[idx]! = 0 := by
  simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
  rw [Array.getElem?_size_le (by omega)]
  simp


theorem goal_0
    (s : List Char)
    (t : List Char)
    (require_1 : True)
    (i : ℕ)
    (iso : Bool)
    (mapS : Array ℕ)
    (mapT : Array ℕ)
    (invariant_mapS_size : mapS.size = OfNat.ofNat 256)
    (invariant_mapT_size : mapT.size = OfNat.ofNat 256)
    (invariant_len_eq : s.length = t.length)
    (invariant_mapS_range : ∀ c < OfNat.ofNat 256, mapS[c]! ≤ i)
    (invariant_mapT_range : ∀ c < OfNat.ofNat 256, mapT[c]! ≤ i)
    (if_neg : s.length = t.length)
    (a : True)
    (a_1 : i ≤ s.length)
    (invariant_arr_sizes : s.length = t.length)
    (invariant_iso_partial : iso = true → ∀ (a b : ℕ), a < i → b < i → (s[a]?.getD 'A' = s[b]?.getD 'A' ↔ t[a]?.getD 'A' = t[b]?.getD 'A'))
    (invariant_iso_false : iso = false → s.length = t.length → ∃ x x_1, ¬(x < s.length → x_1 < s.length → s[x]?.getD 'A' = s[x_1]?.getD 'A' ↔ t[x]?.getD 'A' = t[x_1]?.getD 'A'))
    (invariant_mapS_last : iso = true → ∀ c < OfNat.ofNat 256, OfNat.ofNat 0 < mapS[c]! → (s[mapS[c]! - OfNat.ofNat 1]?.getD 'A').toNat = c ∧ ∀ (j : ℕ), mapS[c]! ≤ j → j < i → ¬(s[j]?.getD 'A').toNat = c)
    (invariant_mapS_zero : iso = true → ∀ c < OfNat.ofNat 256, mapS[c]! = OfNat.ofNat 0 → ∀ j < i, ¬(s[j]?.getD 'A').toNat = c)
    (invariant_mapT_last : iso = true → ∀ c < OfNat.ofNat 256, OfNat.ofNat 0 < mapT[c]! → (t[mapT[c]! - OfNat.ofNat 1]?.getD 'A').toNat = c ∧ ∀ (j : ℕ), mapT[c]! ≤ j → j < i → ¬(t[j]?.getD 'A').toNat = c)
    (invariant_mapT_zero : iso = true → ∀ c < OfNat.ofNat 256, mapT[c]! = OfNat.ofNat 0 → ∀ j < i, ¬(t[j]?.getD 'A').toNat = c)
    (if_pos : i < s.length)
    (if_pos_1 : ¬mapS[(s[i]?.getD 'A').toNat]! = mapT[(t[i]?.getD 'A').toNat]!)
    : s.length = t.length → ∃ x x_1, ¬(x < s.length → x_1 < s.length → s[x]?.getD 'A' = s[x_1]?.getD 'A' ↔ t[x]?.getD 'A' = t[x_1]?.getD 'A') := by
    sorry

theorem goal_1
    (s : List Char)
    (t : List Char)
    (require_1 : True)
    (i : ℕ)
    (iso : Bool)
    (mapS : Array ℕ)
    (mapT : Array ℕ)
    (invariant_mapS_size : mapS.size = OfNat.ofNat 256)
    (invariant_mapT_size : mapT.size = OfNat.ofNat 256)
    (invariant_len_eq : s.length = t.length)
    (invariant_mapS_range : ∀ c < OfNat.ofNat 256, mapS[c]! ≤ i)
    (invariant_mapT_range : ∀ c < OfNat.ofNat 256, mapT[c]! ≤ i)
    (if_neg : s.length = t.length)
    (a : True)
    (a_1 : i ≤ s.length)
    (invariant_arr_sizes : s.length = t.length)
    (invariant_iso_partial : iso = true → ∀ (a b : ℕ), a < i → b < i → (s[a]?.getD 'A' = s[b]?.getD 'A' ↔ t[a]?.getD 'A' = t[b]?.getD 'A'))
    (invariant_iso_false : iso = false → s.length = t.length → ∃ x x_1, ¬(x < s.length → x_1 < s.length → s[x]?.getD 'A' = s[x_1]?.getD 'A' ↔ t[x]?.getD 'A' = t[x_1]?.getD 'A'))
    (invariant_mapS_last : iso = true → ∀ c < OfNat.ofNat 256, OfNat.ofNat 0 < mapS[c]! → (s[mapS[c]! - OfNat.ofNat 1]?.getD 'A').toNat = c ∧ ∀ (j : ℕ), mapS[c]! ≤ j → j < i → ¬(s[j]?.getD 'A').toNat = c)
    (invariant_mapS_zero : iso = true → ∀ c < OfNat.ofNat 256, mapS[c]! = OfNat.ofNat 0 → ∀ j < i, ¬(s[j]?.getD 'A').toNat = c)
    (invariant_mapT_last : iso = true → ∀ c < OfNat.ofNat 256, OfNat.ofNat 0 < mapT[c]! → (t[mapT[c]! - OfNat.ofNat 1]?.getD 'A').toNat = c ∧ ∀ (j : ℕ), mapT[c]! ≤ j → j < i → ¬(t[j]?.getD 'A').toNat = c)
    (invariant_mapT_zero : iso = true → ∀ c < OfNat.ofNat 256, mapT[c]! = OfNat.ofNat 0 → ∀ j < i, ¬(t[j]?.getD 'A').toNat = c)
    (if_pos : i < s.length)
    (if_neg_1 : mapS[(s[i]?.getD 'A').toNat]! = mapT[(t[i]?.getD 'A').toNat]!)
    : iso = true → ∀ (a b : ℕ), a < i + OfNat.ofNat 1 → b < i + OfNat.ofNat 1 → (s[a]?.getD 'A' = s[b]?.getD 'A' ↔ t[a]?.getD 'A' = t[b]?.getD 'A') := by
    sorry



theorem goal_1
    (s : List Char)
    (t : List Char)
    (require_1 : True)
    (i : ℕ)
    (iso : Bool)
    (mapS : Array ℕ)
    (mapT : Array ℕ)
    (invariant_mapS_size : mapS.size = OfNat.ofNat 256)
    (invariant_mapT_size : mapT.size = OfNat.ofNat 256)
    (invariant_len_eq : s.length = t.length)
    (invariant_mapS_range : ∀ c < OfNat.ofNat 256, mapS[c]! ≤ i)
    (invariant_mapT_range : ∀ c < OfNat.ofNat 256, mapT[c]! ≤ i)
    (if_neg : s.length = t.length)
    (a : True)
    (a_1 : i ≤ s.length)
    (invariant_arr_sizes : s.length = t.length)
    (invariant_iso_partial : iso = true → ∀ (a b : ℕ), a < i → b < i → (s[a]?.getD 'A' = s[b]?.getD 'A' ↔ t[a]?.getD 'A' = t[b]?.getD 'A'))
    (invariant_iso_false : iso = false → s.length = t.length → ∃ x x_1, ¬(x < s.length → x_1 < s.length → s[x]?.getD 'A' = s[x_1]?.getD 'A' ↔ t[x]?.getD 'A' = t[x_1]?.getD 'A'))
    (invariant_mapS_last : iso = true → ∀ c < OfNat.ofNat 256, OfNat.ofNat 0 < mapS[c]! → (s[mapS[c]! - OfNat.ofNat 1]?.getD 'A').toNat = c ∧ ∀ (j : ℕ), mapS[c]! ≤ j → j < i → ¬(s[j]?.getD 'A').toNat = c)
    (invariant_mapS_zero : iso = true → ∀ c < OfNat.ofNat 256, mapS[c]! = OfNat.ofNat 0 → ∀ j < i, ¬(s[j]?.getD 'A').toNat = c)
    (invariant_mapT_last : iso = true → ∀ c < OfNat.ofNat 256, OfNat.ofNat 0 < mapT[c]! → (t[mapT[c]! - OfNat.ofNat 1]?.getD 'A').toNat = c ∧ ∀ (j : ℕ), mapT[c]! ≤ j → j < i → ¬(t[j]?.getD 'A').toNat = c)
    (invariant_mapT_zero : iso = true → ∀ c < OfNat.ofNat 256, mapT[c]! = OfNat.ofNat 0 → ∀ j < i, ¬(t[j]?.getD 'A').toNat = c)
    (if_pos : i < s.length)
    (if_neg_1 : mapS[(s[i]?.getD 'A').toNat]! = mapT[(t[i]?.getD 'A').toNat]!)
    : iso = true → ∀ (a b : ℕ), a < i + OfNat.ofNat 1 → b < i + OfNat.ofNat 1 → (s[a]?.getD 'A' = s[b]?.getD 'A' ↔ t[a]?.getD 'A' = t[b]?.getD 'A') := by
    sorry

theorem goal_2
    (s : List Char)
    (t : List Char)
    (require_1 : True)
    (i : ℕ)
    (iso : Bool)
    (mapS : Array ℕ)
    (mapT : Array ℕ)
    (invariant_mapS_size : mapS.size = OfNat.ofNat 256)
    (invariant_mapT_size : mapT.size = OfNat.ofNat 256)
    (invariant_len_eq : s.length = t.length)
    (invariant_mapS_range : ∀ c < OfNat.ofNat 256, mapS[c]! ≤ i)
    (invariant_mapT_range : ∀ c < OfNat.ofNat 256, mapT[c]! ≤ i)
    (if_neg : s.length = t.length)
    (a : True)
    (a_1 : i ≤ s.length)
    (invariant_arr_sizes : s.length = t.length)
    (invariant_iso_partial : iso = true → ∀ (a b : ℕ), a < i → b < i → (s[a]?.getD 'A' = s[b]?.getD 'A' ↔ t[a]?.getD 'A' = t[b]?.getD 'A'))
    (invariant_iso_false : iso = false → s.length = t.length → ∃ x x_1, ¬(x < s.length → x_1 < s.length → s[x]?.getD 'A' = s[x_1]?.getD 'A' ↔ t[x]?.getD 'A' = t[x_1]?.getD 'A'))
    (invariant_mapS_last : iso = true → ∀ c < OfNat.ofNat 256, OfNat.ofNat 0 < mapS[c]! → (s[mapS[c]! - OfNat.ofNat 1]?.getD 'A').toNat = c ∧ ∀ (j : ℕ), mapS[c]! ≤ j → j < i → ¬(s[j]?.getD 'A').toNat = c)
    (invariant_mapS_zero : iso = true → ∀ c < OfNat.ofNat 256, mapS[c]! = OfNat.ofNat 0 → ∀ j < i, ¬(s[j]?.getD 'A').toNat = c)
    (invariant_mapT_last : iso = true → ∀ c < OfNat.ofNat 256, OfNat.ofNat 0 < mapT[c]! → (t[mapT[c]! - OfNat.ofNat 1]?.getD 'A').toNat = c ∧ ∀ (j : ℕ), mapT[c]! ≤ j → j < i → ¬(t[j]?.getD 'A').toNat = c)
    (invariant_mapT_zero : iso = true → ∀ c < OfNat.ofNat 256, mapT[c]! = OfNat.ofNat 0 → ∀ j < i, ¬(t[j]?.getD 'A').toNat = c)
    (if_pos : i < s.length)
    (if_neg_1 : mapS[(s[i]?.getD 'A').toNat]! = mapT[(t[i]?.getD 'A').toNat]!)
    : iso = true → ∀ c < OfNat.ofNat 256, OfNat.ofNat 0 < (mapS.setIfInBounds (s[i]?.getD 'A').toNat (i + OfNat.ofNat 1))[c]! → (s[(mapS.setIfInBounds (s[i]?.getD 'A').toNat (i + OfNat.ofNat 1))[c]! - OfNat.ofNat 1]?.getD 'A').toNat = c ∧ ∀ (j : ℕ), (mapS.setIfInBounds (s[i]?.getD 'A').toNat (i + OfNat.ofNat 1))[c]! ≤ j → j < i + OfNat.ofNat 1 → ¬(s[j]?.getD 'A').toNat = c := by
    sorry

theorem goal_3
    (s : List Char)
    (t : List Char)
    (require_1 : True)
    (i : ℕ)
    (iso : Bool)
    (mapS : Array ℕ)
    (mapT : Array ℕ)
    (invariant_mapS_size : mapS.size = OfNat.ofNat 256)
    (invariant_mapT_size : mapT.size = OfNat.ofNat 256)
    (invariant_len_eq : s.length = t.length)
    (invariant_mapS_range : ∀ c < OfNat.ofNat 256, mapS[c]! ≤ i)
    (invariant_mapT_range : ∀ c < OfNat.ofNat 256, mapT[c]! ≤ i)
    (if_neg : s.length = t.length)
    (a : True)
    (a_1 : i ≤ s.length)
    (invariant_arr_sizes : s.length = t.length)
    (invariant_iso_partial : iso = true → ∀ (a b : ℕ), a < i → b < i → (s[a]?.getD 'A' = s[b]?.getD 'A' ↔ t[a]?.getD 'A' = t[b]?.getD 'A'))
    (invariant_iso_false : iso = false → s.length = t.length → ∃ x x_1, ¬(x < s.length → x_1 < s.length → s[x]?.getD 'A' = s[x_1]?.getD 'A' ↔ t[x]?.getD 'A' = t[x_1]?.getD 'A'))
    (invariant_mapS_last : iso = true → ∀ c < OfNat.ofNat 256, OfNat.ofNat 0 < mapS[c]! → (s[mapS[c]! - OfNat.ofNat 1]?.getD 'A').toNat = c ∧ ∀ (j : ℕ), mapS[c]! ≤ j → j < i → ¬(s[j]?.getD 'A').toNat = c)
    (invariant_mapS_zero : iso = true → ∀ c < OfNat.ofNat 256, mapS[c]! = OfNat.ofNat 0 → ∀ j < i, ¬(s[j]?.getD 'A').toNat = c)
    (invariant_mapT_last : iso = true → ∀ c < OfNat.ofNat 256, OfNat.ofNat 0 < mapT[c]! → (t[mapT[c]! - OfNat.ofNat 1]?.getD 'A').toNat = c ∧ ∀ (j : ℕ), mapT[c]! ≤ j → j < i → ¬(t[j]?.getD 'A').toNat = c)
    (invariant_mapT_zero : iso = true → ∀ c < OfNat.ofNat 256, mapT[c]! = OfNat.ofNat 0 → ∀ j < i, ¬(t[j]?.getD 'A').toNat = c)
    (if_pos : i < s.length)
    (if_neg_1 : mapS[(s[i]?.getD 'A').toNat]! = mapT[(t[i]?.getD 'A').toNat]!)
    : iso = true → ∀ c < OfNat.ofNat 256, (mapS.setIfInBounds (s[i]?.getD 'A').toNat (i + OfNat.ofNat 1))[c]! = OfNat.ofNat 0 → ∀ j < i + OfNat.ofNat 1, ¬(s[j]?.getD 'A').toNat = c := by
    sorry

theorem goal_4
    (s : List Char)
    (t : List Char)
    (require_1 : True)
    (i : ℕ)
    (iso : Bool)
    (mapS : Array ℕ)
    (mapT : Array ℕ)
    (invariant_mapS_size : mapS.size = OfNat.ofNat 256)
    (invariant_mapT_size : mapT.size = OfNat.ofNat 256)
    (invariant_len_eq : s.length = t.length)
    (invariant_mapS_range : ∀ c < OfNat.ofNat 256, mapS[c]! ≤ i)
    (invariant_mapT_range : ∀ c < OfNat.ofNat 256, mapT[c]! ≤ i)
    (if_neg : s.length = t.length)
    (a : True)
    (a_1 : i ≤ s.length)
    (invariant_arr_sizes : s.length = t.length)
    (invariant_iso_partial : iso = true → ∀ (a b : ℕ), a < i → b < i → (s[a]?.getD 'A' = s[b]?.getD 'A' ↔ t[a]?.getD 'A' = t[b]?.getD 'A'))
    (invariant_iso_false : iso = false → s.length = t.length → ∃ x x_1, ¬(x < s.length → x_1 < s.length → s[x]?.getD 'A' = s[x_1]?.getD 'A' ↔ t[x]?.getD 'A' = t[x_1]?.getD 'A'))
    (invariant_mapS_last : iso = true → ∀ c < OfNat.ofNat 256, OfNat.ofNat 0 < mapS[c]! → (s[mapS[c]! - OfNat.ofNat 1]?.getD 'A').toNat = c ∧ ∀ (j : ℕ), mapS[c]! ≤ j → j < i → ¬(s[j]?.getD 'A').toNat = c)
    (invariant_mapS_zero : iso = true → ∀ c < OfNat.ofNat 256, mapS[c]! = OfNat.ofNat 0 → ∀ j < i, ¬(s[j]?.getD 'A').toNat = c)
    (invariant_mapT_last : iso = true → ∀ c < OfNat.ofNat 256, OfNat.ofNat 0 < mapT[c]! → (t[mapT[c]! - OfNat.ofNat 1]?.getD 'A').toNat = c ∧ ∀ (j : ℕ), mapT[c]! ≤ j → j < i → ¬(t[j]?.getD 'A').toNat = c)
    (invariant_mapT_zero : iso = true → ∀ c < OfNat.ofNat 256, mapT[c]! = OfNat.ofNat 0 → ∀ j < i, ¬(t[j]?.getD 'A').toNat = c)
    (if_pos : i < s.length)
    (if_neg_1 : mapS[(s[i]?.getD 'A').toNat]! = mapT[(t[i]?.getD 'A').toNat]!)
    : iso = true → ∀ c < OfNat.ofNat 256, OfNat.ofNat 0 < (mapT.setIfInBounds (t[i]?.getD 'A').toNat (i + OfNat.ofNat 1))[c]! → (t[(mapT.setIfInBounds (t[i]?.getD 'A').toNat (i + OfNat.ofNat 1))[c]! - OfNat.ofNat 1]?.getD 'A').toNat = c ∧ ∀ (j : ℕ), (mapT.setIfInBounds (t[i]?.getD 'A').toNat (i + OfNat.ofNat 1))[c]! ≤ j → j < i + OfNat.ofNat 1 → ¬(t[j]?.getD 'A').toNat = c := by
    sorry

theorem goal_5
    (s : List Char)
    (t : List Char)
    (require_1 : True)
    (i : ℕ)
    (iso : Bool)
    (mapS : Array ℕ)
    (mapT : Array ℕ)
    (invariant_mapS_size : mapS.size = OfNat.ofNat 256)
    (invariant_mapT_size : mapT.size = OfNat.ofNat 256)
    (invariant_len_eq : s.length = t.length)
    (invariant_mapS_range : ∀ c < OfNat.ofNat 256, mapS[c]! ≤ i)
    (invariant_mapT_range : ∀ c < OfNat.ofNat 256, mapT[c]! ≤ i)
    (if_neg : s.length = t.length)
    (a : True)
    (a_1 : i ≤ s.length)
    (invariant_arr_sizes : s.length = t.length)
    (invariant_iso_partial : iso = true → ∀ (a b : ℕ), a < i → b < i → (s[a]?.getD 'A' = s[b]?.getD 'A' ↔ t[a]?.getD 'A' = t[b]?.getD 'A'))
    (invariant_iso_false : iso = false → s.length = t.length → ∃ x x_1, ¬(x < s.length → x_1 < s.length → s[x]?.getD 'A' = s[x_1]?.getD 'A' ↔ t[x]?.getD 'A' = t[x_1]?.getD 'A'))
    (invariant_mapS_last : iso = true → ∀ c < OfNat.ofNat 256, OfNat.ofNat 0 < mapS[c]! → (s[mapS[c]! - OfNat.ofNat 1]?.getD 'A').toNat = c ∧ ∀ (j : ℕ), mapS[c]! ≤ j → j < i → ¬(s[j]?.getD 'A').toNat = c)
    (invariant_mapS_zero : iso = true → ∀ c < OfNat.ofNat 256, mapS[c]! = OfNat.ofNat 0 → ∀ j < i, ¬(s[j]?.getD 'A').toNat = c)
    (invariant_mapT_last : iso = true → ∀ c < OfNat.ofNat 256, OfNat.ofNat 0 < mapT[c]! → (t[mapT[c]! - OfNat.ofNat 1]?.getD 'A').toNat = c ∧ ∀ (j : ℕ), mapT[c]! ≤ j → j < i → ¬(t[j]?.getD 'A').toNat = c)
    (invariant_mapT_zero : iso = true → ∀ c < OfNat.ofNat 256, mapT[c]! = OfNat.ofNat 0 → ∀ j < i, ¬(t[j]?.getD 'A').toNat = c)
    (if_pos : i < s.length)
    (if_neg_1 : mapS[(s[i]?.getD 'A').toNat]! = mapT[(t[i]?.getD 'A').toNat]!)
    : iso = true → ∀ c < OfNat.ofNat 256, (mapT.setIfInBounds (t[i]?.getD 'A').toNat (i + OfNat.ofNat 1))[c]! = OfNat.ofNat 0 → ∀ j < i + OfNat.ofNat 1, ¬(t[j]?.getD 'A').toNat = c := by
    sorry

theorem goal_6
    (s : List Char)
    (t : List Char)
    (require_1 : True)
    (if_neg : s.length = t.length)
    : ∀ c < OfNat.ofNat 256, (Array.replicate (OfNat.ofNat 256) (OfNat.ofNat 0))[c]! = OfNat.ofNat 0 := by
    sorry

theorem goal_7
    (s : List Char)
    (t : List Char)
    (require_1 : True)
    (if_neg : s.length = t.length)
    : ∀ c < OfNat.ofNat 256, (Array.replicate (OfNat.ofNat 256) (OfNat.ofNat 0))[c]! = OfNat.ofNat 0 := by
    sorry

theorem goal_8
    (s : List Char)
    (t : List Char)
    (require_1 : True)
    (if_neg : s.length = t.length)
    : ∀ c < OfNat.ofNat 256, OfNat.ofNat 0 < (Array.replicate (OfNat.ofNat 256) (OfNat.ofNat 0))[c]! → (s[(Array.replicate (OfNat.ofNat 256) (OfNat.ofNat 0))[c]! - OfNat.ofNat 1]?.getD 'A').toNat = c := by
    sorry

theorem goal_9
    (s : List Char)
    (t : List Char)
    (require_1 : True)
    (if_neg : s.length = t.length)
    : ∀ c < OfNat.ofNat 256, OfNat.ofNat 0 < (Array.replicate (OfNat.ofNat 256) (OfNat.ofNat 0))[c]! → (t[(Array.replicate (OfNat.ofNat 256) (OfNat.ofNat 0))[c]! - OfNat.ofNat 1]?.getD 'A').toNat = c := by
    sorry

theorem goal_10
    (s : List Char)
    (t : List Char)
    (require_1 : True)
    (invariant_len_eq : s.length = t.length)
    (i_1 : ℕ)
    (i_2 : Bool)
    (i_3 : Array ℕ)
    (mapT_1 : Array ℕ)
    (invariant_mapS_size : i_3.size = OfNat.ofNat 256)
    (invariant_mapS_range : ∀ c < OfNat.ofNat 256, i_3[c]! ≤ i_1)
    (invariant_mapT_size : mapT_1.size = OfNat.ofNat 256)
    (invariant_mapT_range : ∀ c < OfNat.ofNat 256, mapT_1[c]! ≤ i_1)
    (if_neg : s.length = t.length)
    (invariant_arr_sizes : s.length = t.length)
    (a : True)
    (a_1 : i_1 ≤ s.length)
    (invariant_iso_false : i_2 = false → s.length = t.length → ∃ x x_1, ¬(x < s.length → x_1 < s.length → s[x]?.getD 'A' = s[x_1]?.getD 'A' ↔ t[x]?.getD 'A' = t[x_1]?.getD 'A'))
    (invariant_iso_partial : i_2 = true → ∀ (a b : ℕ), a < i_1 → b < i_1 → (s[a]?.getD 'A' = s[b]?.getD 'A' ↔ t[a]?.getD 'A' = t[b]?.getD 'A'))
    (done_1 : i_1 = s.length ∨ i_2 = false)
    (invariant_mapS_last : i_2 = true → ∀ c < OfNat.ofNat 256, OfNat.ofNat 0 < i_3[c]! → (s[i_3[c]! - OfNat.ofNat 1]?.getD 'A').toNat = c ∧ ∀ (j : ℕ), i_3[c]! ≤ j → j < i_1 → ¬(s[j]?.getD 'A').toNat = c)
    (invariant_mapS_zero : i_2 = true → ∀ c < OfNat.ofNat 256, i_3[c]! = OfNat.ofNat 0 → ∀ j < i_1, ¬(s[j]?.getD 'A').toNat = c)
    (invariant_mapT_last : i_2 = true → ∀ c < OfNat.ofNat 256, OfNat.ofNat 0 < mapT_1[c]! → (t[mapT_1[c]! - OfNat.ofNat 1]?.getD 'A').toNat = c ∧ ∀ (j : ℕ), mapT_1[c]! ≤ j → j < i_1 → ¬(t[j]?.getD 'A').toNat = c)
    (invariant_mapT_zero : i_2 = true → ∀ c < OfNat.ofNat 256, mapT_1[c]! = OfNat.ofNat 0 → ∀ j < i_1, ¬(t[j]?.getD 'A').toNat = c)
    : postcondition s t i_2 := by
    sorry


set_option loom.solver "custom"

macro_rules
| `(tactic|loom_solver) => `(tactic|(
  try injections
  try subst_vars
  try grind (gen := 2)))


prove_correct IsomorphicStrings by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at * <;> expose_names); try (conv => congr <;> simp) ; try rfl; try expose_names)
  exact (goal_0 s t require_1 i iso mapS mapT invariant_mapS_size invariant_mapT_size invariant_len_eq invariant_mapS_range invariant_mapT_range if_neg a a_1 invariant_arr_sizes invariant_iso_partial invariant_iso_false invariant_mapS_last invariant_mapS_zero invariant_mapT_last invariant_mapT_zero if_pos if_pos_1)
  exact (goal_1 s t require_1 i iso mapS mapT invariant_mapS_size invariant_mapT_size invariant_len_eq invariant_mapS_range invariant_mapT_range if_neg a a_1 invariant_arr_sizes invariant_iso_partial invariant_iso_false invariant_mapS_last invariant_mapS_zero invariant_mapT_last invariant_mapT_zero if_pos if_neg_1)
  exact (goal_2 s t require_1 i iso mapS mapT invariant_mapS_size invariant_mapT_size invariant_len_eq invariant_mapS_range invariant_mapT_range if_neg a a_1 invariant_arr_sizes invariant_iso_partial invariant_iso_false invariant_mapS_last invariant_mapS_zero invariant_mapT_last invariant_mapT_zero if_pos if_neg_1)
  exact (goal_3 s t require_1 i iso mapS mapT invariant_mapS_size invariant_mapT_size invariant_len_eq invariant_mapS_range invariant_mapT_range if_neg a a_1 invariant_arr_sizes invariant_iso_partial invariant_iso_false invariant_mapS_last invariant_mapS_zero invariant_mapT_last invariant_mapT_zero if_pos if_neg_1)
  exact (goal_4 s t require_1 i iso mapS mapT invariant_mapS_size invariant_mapT_size invariant_len_eq invariant_mapS_range invariant_mapT_range if_neg a a_1 invariant_arr_sizes invariant_iso_partial invariant_iso_false invariant_mapS_last invariant_mapS_zero invariant_mapT_last invariant_mapT_zero if_pos if_neg_1)
  exact (goal_5 s t require_1 i iso mapS mapT invariant_mapS_size invariant_mapT_size invariant_len_eq invariant_mapS_range invariant_mapT_range if_neg a a_1 invariant_arr_sizes invariant_iso_partial invariant_iso_false invariant_mapS_last invariant_mapS_zero invariant_mapT_last invariant_mapT_zero if_pos if_neg_1)
  exact (goal_6 s t require_1 if_neg)
  exact (goal_7 s t require_1 if_neg)
  exact (goal_8 s t require_1 if_neg)
  exact (goal_9 s t require_1 if_neg)
  exact (goal_10 s t require_1 invariant_len_eq i_1 i_2 i_3 mapT_1 invariant_mapS_size invariant_mapS_range invariant_mapT_size invariant_mapT_range if_neg invariant_arr_sizes a a_1 invariant_iso_false invariant_iso_partial done_1 invariant_mapS_last invariant_mapS_zero invariant_mapT_last invariant_mapT_zero)
end Proof
