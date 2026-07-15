import Lean

import Mathlib.Tactic

set_option maxHeartbeats 10000000

section Specs
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false

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
def implementation (s : List Char) (t : List Char) : Bool :=
  -- O(n) time, O(1) extra space: use constant-size tables over Unicode scalar values.
  -- We maintain two partial injections s→t and t→s using arrays indexed by `Char.toNat`.
  let n := s.length
  if hlen : n = t.length then
    let aS : Array Char := s.toArray
    let aT : Array Char := t.toArray
    let size : Nat := 0x110000
    let empty : Array (Option Nat) := Array.mkArray size none
    let rec go (i : Nat) (st : Array (Option Nat)) (ts : Array (Option Nat)) : Bool :=
      if hi : i < n then
        let cs := aS[i]!; let ct := aT[i]!
        let ks := cs.toNat; let kt := ct.toNat
        -- Use `get?` to avoid proving bounds; `Char.toNat < 0x110000` by definition.
        match st.get? ks, ts.get? kt with
        | some ms, some mt =>
            match ms, mt with
            | none, none =>
                go (i + 1) (st.set! ks (some kt)) (ts.set! kt (some ks))
            | some kt', some ks' =>
                if kt' = kt ∧ ks' = ks then
                  go (i + 1) st ts
                else
                  false
            | _, _ => false
        | _, _ =>
            -- This case should be unreachable if `ks, kt < size`, but keep totality.
            false
      else
        true
    go 0 empty empty
  else
    false
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

section Proof

theorem correctness_goal_0_0 (s : List Char) (t : List Char) (h_precond : precondition s t) (hlen : s.length = t.length) (h_impl : implementation s t =
  let n := s.length;
  let aS := s.toArray;
  let aT := t.toArray;
  let size := 1114112;
  let empty := mkArray size none;
  implementation.go n aS aT 0 empty empty) (h_go_eq : (let n := s.length;
  let aS := s.toArray;
  let aT := t.toArray;
  let size := 1114112;
  let empty := mkArray size none;
  implementation.go n aS aT 0 empty empty = true) ↔
  implementation s t = true) : implementation s t = true ↔ ∀ (i j : ℕ), i < s.length → j < s.length → s[i]! = s[j]! ↔ t[i]! = t[j]! := by
    sorry
end Proof
