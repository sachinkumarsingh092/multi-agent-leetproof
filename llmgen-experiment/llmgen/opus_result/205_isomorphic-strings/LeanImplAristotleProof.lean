/- This file type checks in Lean 4.28 -/

import Lean

import Mathlib

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

/-- NOTE: The original definition had a precedence bug: `↔` binds more loosely than `→` in Lean 4,
    so `i < s.length → j < s.length → (s[i]! = s[j]!) ↔ (t[i]! = t[j]!)` was parsed as
    `(i < s.length → j < s.length → s[i]! = s[j]!) ↔ (t[i]! = t[j]!)`, which is not the
    intended meaning. The fix is to add explicit parentheses around the ↔ expression. -/
-- Original (buggy) definition:
-- def Isomorphic (s : List Char) (t : List Char) : Prop :=
--   s.length = t.length ∧
--     ∀ (i : Nat) (j : Nat),
--       i < s.length → j < s.length →
--         (s[i]! = s[j]!) ↔ (t[i]! = t[j]!)
def Isomorphic (s : List Char) (t : List Char) : Prop :=
  s.length = t.length ∧
    ∀ (i : Nat) (j : Nat),
      i < s.length → j < s.length →
        ((s[i]! = s[j]!) ↔ (t[i]! = t[j]!))

def precondition (s : List Char) (t : List Char) : Prop :=
  True

def postcondition (s : List Char) (t : List Char) (result : Bool) : Prop :=
  (result = true ↔ Isomorphic s t)
end Specs

section Impl
def lookupOrInsert (mapping : List (Char × Char)) (key : Char) (value : Char) : Option (List (Char × Char)) :=
  match mapping with
  | [] => some ((key, value) :: [])
  | (k, v) :: rest =>
    if k == key then
      if v == value then some ((k, v) :: rest) else none
    else
      match lookupOrInsert rest key value with
      | none => none
      | some rest' => some ((k, v) :: rest')

def checkIso (s t : List Char) (mapST mapTS : List (Char × Char)) : Bool :=
  match s, t with
  | [], [] => true
  | sc :: srest, tc :: trest =>
    match lookupOrInsert mapST sc tc with
    | none => false
    | some mapST' =>
      match lookupOrInsert mapTS tc sc with
      | none => false
      | some mapTS' => checkIso srest trest mapST' mapTS'
  | _, _ => false

def implementation (s : List Char) (t : List Char) : Bool :=
  checkIso s t [] []
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

/-- A list of pairs is functional if each key maps to at most one value. -/
def IsFunctional (mapping : List (Char × Char)) : Prop :=
  ∀ k v1 v2, (k, v1) ∈ mapping → (k, v2) ∈ mapping → v1 = v2

lemma lookupOrInsert_functional (mapping : List (Char × Char)) (key value : Char) (m' : List (Char × Char))
    (hfn : IsFunctional mapping)
    (h : lookupOrInsert mapping key value = some m') : IsFunctional m' := by
  induction' mapping with mapping_pair mapping_tail ih generalizing key value m'
  · cases h; exact by unfold IsFunctional; aesop
  · unfold lookupOrInsert at h
    rcases h' : lookupOrInsert mapping_tail key value with (_ | m'') <;> simp_all +decide
    · aesop
    · specialize ih key value m''
      specialize ih (by intro k v1 v2 hk hv; specialize hfn k v1 v2; aesop) h'
      split_ifs at h <;> simp_all +decide [IsFunctional]
      · grind
      · have h_mem : ∀ (mapping : List (Char × Char)) (key value : Char) (m' : List (Char × Char)), lookupOrInsert mapping key value = some m' → ∀ (k v : Char), (k, v) ∈ m' → (k, v) ∈ mapping ∨ k = key ∧ v = value := by
          intros mapping key value m' hm' k v hv; induction' mapping with mapping_pair mapping_tail ih generalizing key value m' k v
          · cases hm'; aesop
          · unfold lookupOrInsert at hm'
            cases h : lookupOrInsert mapping_tail key value <;> simp_all +decide [List.mem_cons]
            · grind
            · grind
        grind

/-- If lookupOrInsert succeeds, the new key-value pair is in the result. -/
lemma lookupOrInsert_contains_new (mapping : List (Char × Char)) (key value : Char) (m' : List (Char × Char))
    (h : lookupOrInsert mapping key value = some m') : (key, value) ∈ m' := by
  induction' mapping with k v mapping ih generalizing m'
  · cases h; aesop
  · rw [lookupOrInsert] at h; aesop

/-- If lookupOrInsert succeeds, old entries are preserved. -/
lemma lookupOrInsert_preserves_old (mapping : List (Char × Char)) (key value : Char) (m' : List (Char × Char))
    (h : lookupOrInsert mapping key value = some m')
    (k v : Char) (hmem : (k, v) ∈ mapping) : (k, v) ∈ m' := by
  induction' mapping with k' v' mapping ih generalizing m' k v
  · contradiction
  · unfold lookupOrInsert at h; aesop

/-- checkIso preserves length equality -/
lemma checkIso_length_eq (s t : List Char) (mapST mapTS : List (Char × Char))
    (h : checkIso s t mapST mapTS = true) : s.length = t.length := by
  have h_ind : ∀ (s t : List Char) (mapST mapTS : List (Char × Char)), checkIso s t mapST mapTS = true → s.length = t.length := by
    intros s t mapST mapTS h_checkIso
    induction' s with sc srest ih generalizing t mapST mapTS
    · cases t <;> tauto
    · rcases t with (_ | ⟨tc, trest⟩) <;> simp_all +decide [checkIso]
      cases h : lookupOrInsert mapST sc tc <;> cases h' : lookupOrInsert mapTS tc sc <;> aesop
  exact h_ind s t mapST mapTS h

/-
PROBLEM
Base case: functional maps on a prefix imply Isomorphic

PROVIDED SOLUTION
Unfold Isomorphic. We need two things:
1. s0.length = t0.length: this is hlen0.
2. For any i, j < s0.length, (s0[i]! = s0[j]!) ↔ (t0[i]! = t0[j]!):
   - Forward: Assume s0[i]! = s0[j]!. From hmapST i hi, we have (s0[i]!, t0[i]!) ∈ mapST. From hmapST j hj, we have (s0[j]!, t0[j]!) ∈ mapST. Since s0[i]! = s0[j]!, these two pairs have the same first component. By hfnST (IsFunctional), t0[i]! = t0[j]!.
   - Backward: Assume t0[i]! = t0[j]!. From hmapTS i (using i < s0.length, and s0.length = t0.length for t0 indexing), we have (t0[i]!, s0[i]!) ∈ mapTS. From hmapTS j, we have (t0[j]!, s0[j]!) ∈ mapTS. Since t0[i]! = t0[j]!, by hfnTS, s0[i]! = s0[j]!.

The proof: constructor, exact hlen0, intro i j hi hj, constructor,
- intro heq, exact hfnST _ _ _ (hmapST i hi) (heq ▸ hmapST j hj),
- intro heq, exact hfnTS _ _ _ (hmapTS i hi) (heq ▸ hmapTS j hj).
-/
lemma maps_imply_isomorphic (s0 t0 : List Char) (mapST mapTS : List (Char × Char))
    (hlen0 : s0.length = t0.length)
    (hfnST : IsFunctional mapST) (hfnTS : IsFunctional mapTS)
    (hmapST : ∀ i, i < s0.length → (s0[i]!, t0[i]!) ∈ mapST)
    (hmapTS : ∀ i, i < s0.length → (t0[i]!, s0[i]!) ∈ mapTS) :
    Isomorphic s0 t0 := by
  refine' ⟨ hlen0, fun i j hi hj => _ ⟩;
  constructor;
  · exact fun h => hfnST _ _ _ ( hmapST i hi ) ( h ▸ hmapST j hj );
  · exact fun h => hfnTS _ _ _ ( hmapTS i hi ) ( h ▸ hmapTS j hj )

/-
PROBLEM
Generalized correctness of checkIso with invariant.

PROVIDED SOLUTION
By induction on s, generalizing t, s0, t0, mapST, mapTS.

Base case (s = []): checkIso [] t mapST mapTS = true implies t = [] (by checkIso_length_eq or direct case analysis on t). Then need Isomorphic (s0 ++ []) (t0 ++ []), which simplifies to Isomorphic s0 t0. Apply maps_imply_isomorphic.

Mismatch cases (s = [], t = _::_ or vice versa): checkIso returns false, contradiction.

Inductive case (s = sc :: srest): t must be tc :: trest. From checkIso:
- lookupOrInsert mapST sc tc = some mapST'
- lookupOrInsert mapTS tc sc = some mapTS'
- checkIso srest trest mapST' mapTS' = true

Apply IH with s0' = s0 ++ [sc], t0' = t0 ++ [tc]:
1. s0'.length = t0'.length: follows from hlen0 (both increase by 1)
2. IsFunctional mapST': from lookupOrInsert_functional
3. IsFunctional mapTS': from lookupOrInsert_functional
4. For all i < (s0 ++ [sc]).length:
   - If i < s0.length: (s0 ++ [sc])[i]! = s0[i]!, (t0 ++ [tc])[i]! = t0[i]!. Use hmapST and lookupOrInsert_preserves_old.
   - If i = s0.length: (s0 ++ [sc])[i]! = sc, (t0 ++ [tc])[i]! = tc. Use lookupOrInsert_contains_new.
5. Similarly for mapTS'.

IH gives Isomorphic ((s0 ++ [sc]) ++ srest) ((t0 ++ [tc]) ++ trest).
Rewrite using List.append_assoc: (s0 ++ [sc]) ++ srest = s0 ++ ([sc] ++ srest) = s0 ++ (sc :: srest).
-/
lemma checkIso_correct_general
    (s t s0 t0 : List Char) (mapST mapTS : List (Char × Char))
    (hlen0 : s0.length = t0.length)
    (hfnST : IsFunctional mapST) (hfnTS : IsFunctional mapTS)
    (hmapST : ∀ i, i < s0.length → (s0[i]!, t0[i]!) ∈ mapST)
    (hmapTS : ∀ i, i < s0.length → (t0[i]!, s0[i]!) ∈ mapTS)
    (hcheck : checkIso s t mapST mapTS = true) :
    Isomorphic (s0 ++ s) (t0 ++ t) := by
  -- By induction on $s$, we can show that if $checkIso s t mapST mapTS = true$, then $Isomorphic (s0 ++ s) (t0 ++ t)$.
  induction' s with sc srest ih generalizing t s0 t0 mapST mapTS;
  · rcases t with ( _ | ⟨ tc, trest ⟩ ) <;> simp_all +decide [ checkIso ];
    exact maps_imply_isomorphic s0 t0 mapST mapTS hlen0 hfnST hfnTS ( by aesop ) ( by aesop );
  · rcases t with ( _ | ⟨ tc, trest ⟩ ) <;> simp_all +decide [ checkIso ];
    rcases h : lookupOrInsert mapST sc tc with ( _ | mapST' ) <;> rcases h' : lookupOrInsert mapTS tc sc with ( _ | mapTS' ) <;> simp_all +decide;
    convert ih trest ( s0 ++ [ sc ] ) ( t0 ++ [ tc ] ) mapST' mapTS' ( by simp +decide [ hlen0 ] ) ( lookupOrInsert_functional mapST sc tc mapST' hfnST h ) ( lookupOrInsert_functional mapTS tc sc mapTS' hfnTS h' ) _ _ hcheck using 1;
    · simp +decide [ List.append_assoc ];
    · simp +decide [ List.append_assoc ];
    · intro i hi; by_cases hi' : i < t0.length <;> simp_all +decide [ List.getElem_append ] ;
      · exact lookupOrInsert_preserves_old _ _ _ _ h _ _ ( hmapST _ hi' );
      · exact?;
    · intro i hi; by_cases hi' : i < t0.length <;> simp_all +decide [ List.getElem_append ] ;
      · exact lookupOrInsert_preserves_old _ _ _ _ h' _ _ ( hmapTS _ hi' );
      · have := lookupOrInsert_contains_new mapTS tc sc mapTS' h'; aesop;

theorem correctness_goal_0_0 (s : List Char) (t : List Char) (h_precond : precondition s t) : checkIso s t [] [] = true → Isomorphic s t := by
  intro hcheck
  have := checkIso_correct_general s t [] [] [] []
    (by rfl) (by intro k v1 v2 h1; simp at h1) (by intro k v1 v2 h1; simp at h1)
    (by intro i hi; simp at hi) (by intro i hi; simp at hi) hcheck
  simpa using this

end Proof
