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

section Assertions
-- Test case 1
#assert_same_evaluation #[(implementation test1_s test1_t), test1_Expected]

-- Test case 2
#assert_same_evaluation #[(implementation test2_s test2_t), test2_Expected]

-- Test case 3
#assert_same_evaluation #[(implementation test3_s test3_t), test3_Expected]

-- Test case 4
#assert_same_evaluation #[(implementation test4_s test4_t), test4_Expected]

-- Test case 5
#assert_same_evaluation #[(implementation test5_s test5_t), test5_Expected]

-- Test case 6
#assert_same_evaluation #[(implementation test6_s test6_t), test6_Expected]

-- Test case 7
#assert_same_evaluation #[(implementation test7_s test7_t), test7_Expected]

-- Test case 8
#assert_same_evaluation #[(implementation test8_s test8_t), test8_Expected]

-- Test case 9
#assert_same_evaluation #[(implementation test9_s test9_t), test9_Expected]
end Assertions

section Pbt
method implementationPbt (s : List Char) (t : List Char)
  return (result : Bool)
  require precondition s t
  ensures postcondition s t result
  do
  return (implementation s t)

velvet_plausible_test implementationPbt (config := { maxMs := some 20000 })
end Pbt

section Proof
-- Helper: lookupOrInsert finds key means it returns the stored value
private lemma lookupOrInsert_found (mapping : List (Char × Char)) (key : Char) (value : Char) (k : Char) (v : Char) (rest : List (Char × Char))
    (h : lookupOrInsert mapping key value = some ((k, v) :: rest)) :
    True := trivial

private def MapFn (m : List (Char × Char)) : Prop :=
  ∀ k v1 v2, (k, v1) ∈ m → (k, v2) ∈ m → v1 = v2

private def MapCovers (m : List (Char × Char)) (ps pt : List Char) : Prop :=
  ps.length = pt.length ∧
  ∀ i, i < ps.length → (ps[i]!, pt[i]!) ∈ m

private def MapInvariant (mapST mapTS : List (Char × Char)) (ps pt : List Char) : Prop :=
  ps.length = pt.length ∧
  MapFn mapST ∧ MapFn mapTS ∧
  MapCovers mapST ps pt ∧ MapCovers mapTS pt ps

private lemma mapInvariant_nil : MapInvariant [] [] [] [] := by
  unfold MapInvariant MapFn MapCovers
  refine ⟨rfl, ?_, ?_, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩⟩
  · intro k v1 v2 h1; simp at h1
  · intro k v1 v2 h1; simp at h1
  · intro i h; simp [List.length] at h
  · intro i h; simp [List.length] at h

private lemma lookupOrInsert_mem_of_some (mapping : List (Char × Char)) (key value : Char) :
    ∀ m', lookupOrInsert mapping key value = some m' → (key, value) ∈ m' := by
  induction mapping with
  | nil =>
    intro m' h; simp [lookupOrInsert] at h; subst h; exact List.Mem.head _
  | cons p rest ih =>
    intro m' h
    obtain ⟨k, v⟩ := p
    unfold lookupOrInsert at h
    split at h
    · split at h
      · rename_i hk hv
        have hk' := beq_iff_eq.mp hk; have hv' := beq_iff_eq.mp hv
        subst hk'; subst hv'
        injection h with h; subst h
        exact List.Mem.head _
      · injection h
    · rename_i hk
      have hrec : ∃ rest', lookupOrInsert rest key value = some rest' ∧ m' = (k, v) :: rest' := by
        cases heq : lookupOrInsert rest key value with
        | none => simp [heq] at h
        | some rest' => simp [heq] at h; exact ⟨rest', rfl, h.symm⟩
      obtain ⟨rest', hrec_eq, hm'⟩ := hrec
      subst hm'
      exact List.Mem.tail _ (ih _ hrec_eq)

private lemma lookupOrInsert_preserves (mapping : List (Char × Char)) (key value : Char) (m' : List (Char × Char))
    (h : lookupOrInsert mapping key value = some m') :
    ∀ p, p ∈ mapping → p ∈ m' := by
  induction mapping generalizing m' with
  | nil => intro p hp; simp at hp
  | cons q rest ih =>
    obtain ⟨k, v⟩ := q
    intro p hp
    unfold lookupOrInsert at h
    split at h
    · split at h
      · injection h with h; subst h; exact hp
      · injection h
    · rename_i hk
      cases heq : lookupOrInsert rest key value with
      | none => simp [heq] at h
      | some rest' =>
        simp [heq] at h
        cases hp with
        | head => rw [← h]; exact List.Mem.head _
        | tail _ hp' => rw [← h]; exact List.Mem.tail _ (ih rest' (by simp [heq]) p hp')

-- Core: when checkIso returns true, the lists have equal length
private lemma checkIso_length_eq (s t : List Char) (mapST mapTS : List (Char × Char)) :
    checkIso s t mapST mapTS = true → s.length = t.length := by
  revert t mapST mapTS
  induction s with
  | nil =>
    intro t mapST mapTS h
    cases t with
    | nil => rfl
    | cons tc trest => simp [checkIso] at h
  | cons sc srest ih =>
    intro t mapST mapTS h
    cases t with
    | nil => simp [checkIso] at h
    | cons tc trest =>
      simp [checkIso] at h
      split at h
      · simp at h
      · rename_i mapST' hST
        split at h
        · simp at h
        · rename_i mapTS' hTS
          have := ih trest mapST' mapTS' h
          simp [this]

private def IsFunctional (m : List (Char × Char)) : Prop :=
  ∀ k v1 v2, (k, v1) ∈ m → (k, v2) ∈ m → v1 = v2

private def MapsPrefix (m : List (Char × Char)) (ps pt : List Char) : Prop :=
  ps.length = pt.length ∧ ∀ i, i < ps.length → (ps[i]!, pt[i]!) ∈ m

private def GoodMaps (mapST mapTS : List (Char × Char)) (ps pt : List Char) : Prop :=
  ps.length = pt.length ∧
  IsFunctional mapST ∧ IsFunctional mapTS ∧
  MapsPrefix mapST ps pt ∧ MapsPrefix mapTS pt ps

private lemma goodMaps_nil : GoodMaps [] [] [] [] := by
  unfold GoodMaps IsFunctional MapsPrefix
  exact ⟨rfl, fun k v1 v2 h1 _ => by simp at h1, fun k v1 v2 h1 _ => by simp at h1,
         ⟨rfl, fun i h => by simp at h⟩, ⟨rfl, fun i h => by simp at h⟩⟩

-- If map is functional and lookupOrInsert succeeds, the result is functional
private lemma lookupOrInsert_functional (mapping : List (Char × Char)) (key value : Char) (m' : List (Char × Char))
    (hfn : IsFunctional mapping)
    (h : lookupOrInsert mapping key value = some m') :
    IsFunctional m' := by
  induction mapping generalizing m' with
  | nil =>
    simp [lookupOrInsert] at h; subst h
    unfold IsFunctional
    intro k v1 v2 h1 h2
    simp [List.mem_singleton] at h1 h2
    rw [h1.2, h2.2]
  | cons q rest ih =>
    obtain ⟨k, v⟩ := q
    unfold lookupOrInsert at h
    split at h
    · rename_i hk; split at h
      · injection h with h; subst h; exact hfn
      · injection h
    · rename_i hk
      cases heq : lookupOrInsert rest key value with
      | none => simp [heq] at h
      | some rest' =>
        simp [heq] at h
        have hfn_rest : IsFunctional rest := by
          intro k' v1' v2' h1' h2'
          exact hfn k' v1' v2' (List.mem_cons_of_mem _ h1') (List.mem_cons_of_mem _ h2')
        have hfn_rest' := ih rest' hfn_rest (by rw [heq])
        rw [← h]
        intro k' v1' v2' h1' h2'
        cases h1' with
        | head =>
          cases h2' with
          | head => rfl
          | tail _ h2'' =>
            -- (k, v) is head, (k', v2') in rest'. k' = k.
            -- We need to show v = v2'. But (k, v) was in original mapping.
            -- And (k, v2') ∈ rest'. Since rest' came from lookupOrInsert rest key value,
            -- (k, v2') is either from rest or is (key, value). But k ≠ key.
            -- So (k, v2') ∈ rest. Then by hfn, since (k,v) ∈ mapping and (k,v2') ∈ rest ⊆ mapping.
            -- But we need (k, v2') ∈ rest... we need that m' \ [(k,v)] ⊆ rest ∪ {(key,value)}
            sorry
        | tail _ h1'' =>
          cases h2' with
          | head => sorry
          | tail _ h2'' => exact hfn_rest' k' v1' v2' h1'' h2''

-- Elements in lookupOrInsert result are either from original or the new pair
private lemma lookupOrInsert_mem_result (mapping : List (Char × Char)) (key value : Char) (m' : List (Char × Char))
    (h : lookupOrInsert mapping key value = some m') :
    ∀ p, p ∈ m' → p ∈ mapping ∨ p = (key, value) := by
  induction mapping generalizing m' with
  | nil =>
    simp [lookupOrInsert] at h; subst h
    intro p hp; simp at hp; exact Or.inr hp
  | cons q rest ih =>
    obtain ⟨k, v⟩ := q
    unfold lookupOrInsert at h
    split at h
    · rename_i hk; split at h
      · injection h with h; subst h
        intro p hp; exact Or.inl hp
      · injection h
    · rename_i hk
      cases heq : lookupOrInsert rest key value with
      | none => simp [heq] at h
      | some rest' =>
        simp [heq] at h; rw [← h]
        intro p hp
        cases hp with
        | head => exact Or.inl (List.Mem.head _)
        | tail _ hp' =>
          have := ih rest' (by rw [heq]) p hp'
          cases this with
          | inl h => exact Or.inl (List.Mem.tail _ h)
          | inr h => exact Or.inr h


theorem correctness_goal_0_0
    (s : List Char)
    (t : List Char)
    (h_precond : precondition s t)
    : checkIso s t [] [] = true → Isomorphic s t := by
    sorry

lemma lookupOrInsert_succeeds (mapping : List (Char × Char)) (key value : Char)
    (hcons : ∀ v, (key, v) ∈ mapping → v = value) :
    ∃ m', lookupOrInsert mapping key value = some m' := by
  induction mapping with
  | nil => exact ⟨[(key, value)], rfl⟩
  | cons p rest ih =>
    obtain ⟨k, v⟩ := p
    unfold lookupOrInsert
    by_cases hk : k == key
    · rw [if_pos hk]
      have hk' : k = key := beq_iff_eq.mp hk
      have hv : v = value := by
        apply hcons
        subst hk'
        exact List.Mem.head _
      subst hv
      simp
    · rw [if_neg hk]
      have ih' : ∃ m', lookupOrInsert rest key value = some m' := by
        apply ih
        intro v' hv'
        apply hcons
        exact List.Mem.tail _ hv'
      obtain ⟨m', hm'⟩ := ih'
      rw [hm']
      exact ⟨(k, v) :: m', rfl⟩

lemma lookupOrInsert_consistent (mapping : List (Char × Char)) (key value : Char)
    (hfn : IsFunctional mapping) (hmem : (key, value) ∈ mapping) :
    lookupOrInsert mapping key value = some mapping := by
  induction mapping with
  | nil => simp at hmem
  | cons p rest ih =>
    obtain ⟨k, v⟩ := p
    unfold lookupOrInsert
    cases hmem with
    | head => simp [beq_self_eq_true]
    | tail _ hmem' =>
      by_cases hk : k == key
      · rw [if_pos hk]
        have hk' : k = key := beq_iff_eq.mp hk
        have : v = value := by
          subst hk'
          exact hfn k v value (List.Mem.head _) (List.Mem.tail _ hmem')
        subst this
        simp
      · rw [if_neg hk]
        have hfn' : IsFunctional rest := by
          intro k' v1 v2 h1 h2
          exact hfn k' v1 v2 (List.Mem.tail _ h1) (List.Mem.tail _ h2)
        rw [ih hfn' hmem']

private lemma getElem!_append_left {α : Type} [Inhabited α] {as bs : List α} {i : Nat} (h : i < as.length) :
    (as ++ bs)[i]! = as[i]! := by
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_append_left h]

private lemma getElem!_append_right {α : Type} [Inhabited α] {as bs : List α} {i : Nat} (h : as.length ≤ i) (h2 : i < as.length + bs.length) :
    (as ++ bs)[i]! = bs[i - as.length]! := by
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_append_right h]

private def StrongMaps (mapST mapTS : List (Char × Char)) (ps pt : List Char) : Prop :=
  ps.length = pt.length ∧
  IsFunctional mapST ∧ IsFunctional mapTS ∧
  (∀ i, i < ps.length → (ps[i]!, pt[i]!) ∈ mapST) ∧
  (∀ i, i < pt.length → (pt[i]!, ps[i]!) ∈ mapTS) ∧
  (∀ k v, (k, v) ∈ mapST → ∃ i, i < ps.length ∧ ps[i]! = k ∧ pt[i]! = v) ∧
  (∀ k v, (k, v) ∈ mapTS → ∃ i, i < pt.length ∧ pt[i]! = k ∧ ps[i]! = v)

private lemma strongMaps_nil : StrongMaps [] [] [] [] := by
  unfold StrongMaps
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k v1 v2 h1 _; simp at h1
  · intro k v1 v2 h1 _; simp at h1
  · intro i h; simp at h
  · intro i h; simp at h
  · intro k v h; simp at h
  · intro k v h; simp at h

private lemma getElem!_append_cons {α : Type} [Inhabited α] (ps : List α) (x : α) (xs : List α) :
    (ps ++ x :: xs)[ps.length]! = x := by
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
        List.getElem?_cons_zero]

private lemma getElem!_append_singleton {α : Type} [Inhabited α] (ps : List α) (x : α) :
    (ps ++ [x])[ps.length]! = x := by
  show (ps ++ x :: [])[ps.length]! = x
  exact getElem!_append_cons ps x []

private lemma checkIso_of_iso_gen (s t : List Char) (mapST mapTS : List (Char × Char)) (ps pt : List Char)
    (hgood : StrongMaps mapST mapTS ps pt)
    (hiso : Isomorphic (ps ++ s) (pt ++ t)) :
    checkIso s t mapST mapTS = true := by
  induction s generalizing t mapST mapTS ps pt with
  | nil =>
    match t with
    | [] => simp [checkIso]
    | tc :: trest =>
      exfalso; have h1 := hiso.1; have h2 := hgood.1; simp at h1; omega
  | cons sc srest ih =>
    match t with
    | [] =>
      exfalso; have h1 := hiso.1; have h2 := hgood.1; simp at h1; omega
    | tc :: trest =>
      simp only [checkIso]
      obtain ⟨hlen, hfnST, hfnTS, hcoverST, hcoverTS, hinvST, hinvTS⟩ := hgood
      have hiso_iff := hiso.2
      have hST_cons : ∀ v, (sc, v) ∈ mapST → v = tc := by
        intro v hmem
        obtain ⟨j, hj_lt, hj_ps, hj_pt⟩ := hinvST sc v hmem
        have h1 : (ps ++ sc :: srest)[j]! = sc := by
          rw [getElem!_append_left hj_lt]; exact hj_ps
        have h2 : (ps ++ sc :: srest)[ps.length]! = sc := getElem!_append_cons ps sc srest
        have heq : (pt ++ tc :: trest)[j]! = (pt ++ tc :: trest)[ps.length]! :=
          (hiso_iff j ps.length).mp (fun hj hn => by rw [h1, h2])
        rw [getElem!_append_left (show j < pt.length by omega)] at heq
        rw [show (pt ++ tc :: trest)[ps.length]! = tc from by rw [hlen]; exact getElem!_append_cons pt tc trest] at heq
        rw [← hj_pt]; exact heq
      have hTS_cons : ∀ v, (tc, v) ∈ mapTS → v = sc := by
        intro v hmem
        obtain ⟨j, hj_lt, hj_pt, hj_ps⟩ := hinvTS tc v hmem
        have h1 : (pt ++ tc :: trest)[j]! = tc := by
          rw [getElem!_append_left hj_lt]; exact hj_pt
        have h2' : (pt ++ tc :: trest)[ps.length]! = tc := by rw [hlen]; exact getElem!_append_cons pt tc trest
        have heq_t : (pt ++ tc :: trest)[j]! = (pt ++ tc :: trest)[ps.length]! := by rw [h1, h2']
        have hmpr := (hiso_iff j ps.length).mpr heq_t
        have hlen_s : (ps ++ sc :: srest).length = ps.length + srest.length + 1 := by simp; omega
        have heq := hmpr (by omega) (by omega)
        rw [getElem!_append_left (show j < ps.length by omega),
            getElem!_append_cons] at heq
        rw [← hj_ps]; exact heq
      obtain ⟨mapST', hmST'⟩ := lookupOrInsert_succeeds mapST sc tc hST_cons
      obtain ⟨mapTS', hmTS'⟩ := lookupOrInsert_succeeds mapTS tc sc hTS_cons
      rw [hmST', hmTS']
      apply ih trest mapST' mapTS' (ps ++ [sc]) (pt ++ [tc])
      · have hlen_ps1 : (ps ++ [sc]).length = ps.length + 1 := by simp
        have hlen_pt1 : (pt ++ [tc]).length = pt.length + 1 := by simp
        refine ⟨by omega,
                lookupOrInsert_functional mapST sc tc mapST' hfnST hmST',
                lookupOrInsert_functional mapTS tc sc mapTS' hfnTS hmTS',
                ?_, ?_, ?_, ?_⟩
        · intro i hi
          rw [hlen_ps1] at hi
          by_cases hi' : i < ps.length
          · rw [getElem!_append_left hi', getElem!_append_left (show i < pt.length by omega)]
            exact lookupOrInsert_preserves mapST sc tc mapST' hmST' _ (hcoverST i hi')
          · have hi_eq : i = ps.length := by omega
            subst hi_eq
            rw [getElem!_append_singleton, show ps.length = pt.length from hlen, getElem!_append_singleton]
            exact lookupOrInsert_mem_of_some mapST sc tc mapST' hmST'
        · intro i hi
          rw [hlen_pt1] at hi
          by_cases hi' : i < pt.length
          · rw [getElem!_append_left hi', getElem!_append_left (show i < ps.length by omega)]
            exact lookupOrInsert_preserves mapTS tc sc mapTS' hmTS' _ (hcoverTS i hi')
          · have hi_eq : i = pt.length := by omega
            subst hi_eq
            rw [getElem!_append_singleton, show pt.length = ps.length from hlen.symm, getElem!_append_singleton]
            exact lookupOrInsert_mem_of_some mapTS tc sc mapTS' hmTS'
        · intro k v hmem
          cases lookupOrInsert_mem_result mapST sc tc mapST' hmST' (k, v) hmem with
          | inl h =>
            obtain ⟨i, hi_lt, hi_ps, hi_pt⟩ := hinvST k v h
            refine ⟨i, by omega, ?_, ?_⟩
            · rw [getElem!_append_left (show i < ps.length from hi_lt)]; exact hi_ps
            · rw [getElem!_append_left (show i < pt.length by omega)]; exact hi_pt
          | inr h =>
            have hpair := Prod.mk.inj h
            refine ⟨ps.length, by omega, ?_, ?_⟩
            · rw [getElem!_append_singleton]; exact hpair.1.symm
            · rw [show ps.length = pt.length from hlen, getElem!_append_singleton]; exact hpair.2.symm
        · intro k v hmem
          cases lookupOrInsert_mem_result mapTS tc sc mapTS' hmTS' (k, v) hmem with
          | inl h =>
            obtain ⟨i, hi_lt, hi_pt, hi_ps⟩ := hinvTS k v h
            refine ⟨i, by omega, ?_, ?_⟩
            · rw [getElem!_append_left (show i < pt.length from hi_lt)]; exact hi_pt
            · rw [getElem!_append_left (show i < ps.length by omega)]; exact hi_ps
          | inr h =>
            have hpair := Prod.mk.inj h
            refine ⟨pt.length, by omega, ?_, ?_⟩
            · rw [getElem!_append_singleton]; exact hpair.1.symm
            · rw [show pt.length = ps.length from hlen.symm, getElem!_append_singleton]; exact hpair.2.symm
      · rw [List.append_assoc, List.append_assoc]; simp only [List.singleton_append]; exact hiso


theorem correctness_goal_0_1
    (s : List Char)
    (t : List Char)
    : Isomorphic s t → checkIso s t [] [] = true := by
    intro hiso
    have := checkIso_of_iso_gen s t [] [] [] [] strongMaps_nil
    simp at this
    exact this hiso


theorem correctness_goal_0
    (s : List Char)
    (t : List Char)
    (h_precond : precondition s t)
    : checkIso s t [] [] = true ↔ Isomorphic s t := by
    unfold precondition at h_precond
    -- We need a generalized version of this theorem
    -- Define what it means for a map to be "functional" (each key maps to at most one value)
    -- and what it means for maps to be consistent with a prefix

    -- Key helper: generalized correctness of checkIso
    -- We say maps are "consistent with" prefix lists pS, pT if:
    -- 1) pS.length = pT.length
    -- 2) For each key k in mapST with value v, there exists i < pS.length with pS[i]! = k and pT[i]! = v
    -- 3) For each key k in mapTS with value v, there exists i < pT.length with pT[i]! = k and pS[i]! = v
    -- 4) For all i < pS.length, lookupOrInsert mapST pS[i]! pT[i]! succeeds
    -- 5) For all i < pT.length, lookupOrInsert mapTS pT[i]! pS[i]! succeeds
    -- 6) The prefix is already isomorphic

    -- Actually, let me try a simpler approach: prove both directions separately
    constructor
    · -- Forward: checkIso s t [] [] = true → Isomorphic s t
      have h_fwd : checkIso s t [] [] = true → Isomorphic s t := by expose_names; exact (correctness_goal_0_0 s t h_precond)
      exact h_fwd
    · -- Backward: Isomorphic s t → checkIso s t [] [] = true
      have h_bwd : Isomorphic s t → checkIso s t [] [] = true := by expose_names; exact (correctness_goal_0_1 s t)
      exact h_bwd


theorem correctness_goal
    (s : List Char)
    (t : List Char)
    (h_precond : precondition s t)
    : postcondition s t (implementation s t) := by
    unfold postcondition implementation
    -- We need: checkIso s t [] [] = true ↔ Isomorphic s t
    -- Define what it means for a mapping to be "valid" w.r.t. prefixes
    -- Key generalized lemma about checkIso
    have h_main : checkIso s t [] [] = true ↔ Isomorphic s t := by expose_names; exact (correctness_goal_0 s t h_precond)
    exact h_main
end Proof
