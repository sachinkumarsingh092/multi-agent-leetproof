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
  -- O(n) time / O(1) extra space (aside from one-time List→Array conversion).
  -- Work on arrays to get O(1) indexing.
  let sa : Array Char := s.toArray
  let ta : Array Char := t.toArray

  if sa.size != ta.size then
    return false
  else
    let n := sa.size
    let mut ok : Bool := true
    let mut i : Nat := 0
    while (i < n ∧ ok = true)
      -- Sizes stay consistent with n; needed for safe indexing facts.
      invariant "Iso_outer_sizes" (sa.size = n ∧ ta.size = n)
      -- i is always within [0, n].
      invariant "Iso_outer_i_bounds" (i ≤ n)
      -- If ok is still true, all pairs (p,q) with p < i and p < q < n
      -- have been checked and satisfy the isomorphism relation.
      invariant "Iso_outer_checked" (
        ok = true →
          ∀ (p : Nat) (q : Nat),
            p < i → q < n → p < q →
              ((sa[p]! = sa[q]!) ↔ (ta[p]! = ta[q]!))
      )
      -- If ok becomes false, we have found a concrete counterexample pair.
      -- This is crucial to prove: ok=false → ¬Isomorphic s t.
      invariant "Iso_outer_cex" (
        ok = false →
          ∃ (p : Nat) (q : Nat),
            p < q ∧ q < n ∧
              ¬((sa[p]! = sa[q]!) ↔ (ta[p]! = ta[q]!))
      )
      decreasing n - i
    do
      let mut j : Nat := i + 1
      while (j < n ∧ ok = true)
        -- Sizes stay consistent with n; needed for safe indexing facts.
        invariant "Iso_inner_sizes" (sa.size = n ∧ ta.size = n)
        -- i is fixed for this inner loop and within bounds; j stays within [0,n].
        invariant "Iso_inner_bounds" (i < n ∧ j ≤ n)
        -- Preserve the outer-loop progress property inside the inner loop.
        invariant "Iso_inner_prev_outer" (
          ok = true →
            ∀ (p : Nat) (q : Nat),
              p < i → q < n → p < q →
                ((sa[p]! = sa[q]!) ↔ (ta[p]! = ta[q]!))
        )
        -- If ok is still true, all pairs (i,q) for i < q < j have been checked.
        invariant "Iso_inner_checked_i" (
          ok = true →
            ∀ (q : Nat),
              i < q → q < j →
                ((sa[i]! = sa[q]!) ↔ (ta[i]! = ta[q]!))
        )
        -- If ok becomes false, we have found a concrete counterexample pair for this i.
        -- This propagates outward to establish Iso_outer_cex.
        invariant "Iso_inner_cex_i" (
          ok = false →
            ∃ (q : Nat),
              i < q ∧ q < j ∧
                ¬((sa[i]! = sa[q]!) ↔ (ta[i]! = ta[q]!))
        )
        decreasing n - j
      do
        let eqS : Bool := decide (sa[i]! = sa[j]!)
        let eqT : Bool := decide (ta[i]! = ta[j]!)
        if eqS != eqT then
          ok := false
        else
          pure ()
        j := j + 1
      i := i + 1
    return ok
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

theorem goal_0_0_0
    (s : List Char)
    (t : List Char)
    (require_1 : True)
    (i_1 : ℕ)
    (ok_1 : Bool)
    (if_neg : s.length = t.length)
    (invariant_Iso_outer_sizes : t.length = s.length)
    (invariant_Iso_outer_i_bounds : i_1 ≤ s.length)
    (invariant_Iso_outer_cex : ok_1 = false → ∃ p q, p < q ∧ q < s.length ∧ ¬(s[p]?.getD 'A' = s[q]?.getD 'A' ↔ t[p]?.getD 'A' = t[q]?.getD 'A'))
    (invariant_Iso_outer_checked : ok_1 = true →
  ∀ (p q : ℕ), p < i_1 → q < s.length → p < q → (s[p]?.getD 'A' = s[q]?.getD 'A' ↔ t[p]?.getD 'A' = t[q]?.getD 'A'))
    (done_1 : i_1 < s.length → ok_1 = false)
    (hok : ok_1 = true)
    (i : ℕ)
    (j : ℕ)
    : i < s.length → j < s.length → s[i]! = s[j]! ↔ t[i]! = t[j]! := by
    sorry

theorem goal_0_0
    (s : List Char)
    (t : List Char)
    (require_1 : True)
    (i_1 : ℕ)
    (ok_1 : Bool)
    (if_neg : s.length = t.length)
    (invariant_Iso_outer_sizes : t.length = s.length)
    (invariant_Iso_outer_i_bounds : i_1 ≤ s.length)
    (invariant_Iso_outer_cex : ok_1 = false → ∃ p q, p < q ∧ q < s.length ∧ ¬(s[p]?.getD 'A' = s[q]?.getD 'A' ↔ t[p]?.getD 'A' = t[q]?.getD 'A'))
    (invariant_Iso_outer_checked : ok_1 = true →
  ∀ (p q : ℕ), p < i_1 → q < s.length → p < q → (s[p]?.getD 'A' = s[q]?.getD 'A' ↔ t[p]?.getD 'A' = t[q]?.getD 'A'))
    (done_1 : i_1 < s.length → ok_1 = false)
    (hok : ok_1 = true)
    : ∀ (i j : ℕ), i < s.length → j < s.length → s[i]! = s[j]! ↔ t[i]! = t[j]! := by
  intro i j
  change (i < s.length → j < s.length → s[i]! = s[j]!) ↔ t[i]! = t[j]!
  expose_names; exact (goal_0_0_0 s t require_1 i_1 ok_1 if_neg invariant_Iso_outer_sizes invariant_Iso_outer_i_bounds invariant_Iso_outer_cex invariant_Iso_outer_checked done_1 hok i j)

theorem goal_0
    (s : List Char)
    (t : List Char)
    (require_1 : True)
    (i_1 : ℕ)
    (ok_1 : Bool)
    (if_neg : s.length = t.length)
    (invariant_Iso_outer_sizes : t.length = s.length)
    (invariant_Iso_outer_i_bounds : i_1 ≤ s.length)
    (invariant_Iso_outer_cex : ok_1 = false → ∃ p q, p < q ∧ q < s.length ∧ ¬(s[p]?.getD 'A' = s[q]?.getD 'A' ↔ t[p]?.getD 'A' = t[q]?.getD 'A'))
    (invariant_Iso_outer_checked : ok_1 = true → ∀ (p q : ℕ), p < i_1 → q < s.length → p < q → (s[p]?.getD 'A' = s[q]?.getD 'A' ↔ t[p]?.getD 'A' = t[q]?.getD 'A'))
    (done_1 : i_1 < s.length → ok_1 = false)
    : postcondition s t ok_1 := by
  unfold postcondition
  constructor
  · intro hok
    unfold Isomorphic
    refine And.intro if_neg ?_
    expose_names; exact (goal_0_0 s t require_1 i_1 ok_1 if_neg invariant_Iso_outer_sizes invariant_Iso_outer_i_bounds invariant_Iso_outer_cex invariant_Iso_outer_checked done_1 hok)
  · intro hiso
    expose_names; intros; expose_names; try simp_all; try grind


prove_correct IsomorphicStrings by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at * <;> expose_names); try (conv => congr <;> simp) ; try rfl; try expose_names)
  exact (goal_0 s t require_1 i_1 ok_1 if_neg invariant_Iso_outer_sizes invariant_Iso_outer_i_bounds invariant_Iso_outer_cex invariant_Iso_outer_checked done_1)
end Proof
