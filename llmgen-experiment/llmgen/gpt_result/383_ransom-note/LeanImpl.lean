import Lean
import Mathlib.Tactic
import Velvet.Std

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
  -- O(m + n) time using a fixed-size frequency table over all Unicode scalar values.
  -- `Char.toNat` is < 0x110000 (= 1114112).
  let size : Nat := 0x110000
  let idx : Char → Nat := fun c => c.toNat
  let init : Array Nat := Array.mkArray size 0
  let inc (a : Array Nat) (c : Char) : Array Nat :=
    let i := idx c
    a.modify i (fun v => v + 1)
  let decOk (a : Array Nat) (c : Char) : Option (Array Nat) :=
    let i := idx c
    let v := a.get! i
    if v = 0 then none else some (a.modify i (fun w => w - 1))
  let freq : Array Nat := magazine.foldl inc init
  let rec consume (a : Array Nat) (xs : List Char) : Bool :=
    match xs with
    | [] => true
    | c :: cs =>
        match decOk a c with
        | none => false
        | some a' => consume a' cs
  consume freq ransomNote
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

section Assertions
-- Test case 1
#assert_same_evaluation #[(implementation test1_ransomNote test1_magazine), test1_Expected]

-- Test case 2
#assert_same_evaluation #[(implementation test2_ransomNote test2_magazine), test2_Expected]

-- Test case 3
#assert_same_evaluation #[(implementation test3_ransomNote test3_magazine), test3_Expected]

-- Test case 4
#assert_same_evaluation #[(implementation test4_ransomNote test4_magazine), test4_Expected]

-- Test case 5
#assert_same_evaluation #[(implementation test5_ransomNote test5_magazine), test5_Expected]

-- Test case 6
#assert_same_evaluation #[(implementation test6_ransomNote test6_magazine), test6_Expected]

-- Test case 7
#assert_same_evaluation #[(implementation test7_ransomNote test7_magazine), test7_Expected]

-- Test case 8
#assert_same_evaluation #[(implementation test8_ransomNote test8_magazine), test8_Expected]

-- Test case 9
#assert_same_evaluation #[(implementation test9_ransomNote test9_magazine), test9_Expected]
end Assertions

section Proof

lemma char_toNat_lt_size (c : Char) : c.toNat < 0x110000 := by
  cases c with
  | mk n hn =>
    -- `Char.toNat` is the underlying code point.
    -- The validity proof `hn` implies that code point is < 0x110000.
    -- First normalize everything to `Nat.isValidChar`.
    have hn' : n.toNat.isValidChar := by
      simpa using hn
    -- Unfold `Nat.isValidChar` and extract the upper bound.
    -- (The predicate excludes surrogate range but always enforces the global upper bound.)
    simp [Nat.isValidChar] at hn'
    -- `hn'` is now a disjunction of bounds; either way we can conclude.
    rcases hn' with hn' | hn'
    · -- below the surrogate range
      exact lt_trans hn' (by decide)
    · -- in the upper (non-surrogate) range
      exact hn'.2


lemma array_get!_eq_getElem_of_lt {α} [Inhabited α] (a : Array α) (i : Nat) (hi : i < a.size) :
    a.get! i = a[i]'hi := by
  -- `get!` is `getD` with the default value; under the bound hypothesis it reduces to `getElem`.
  -- (Unfolding `getD` is safe because it is just a bounds check.)
  simp [Array.get!_eq_getD, Array.getD, hi]

lemma array_get!_modify_of_lt {α} [Inhabited α]
    (a : Array α) (j i : Nat) (f : α → α) (hj : j < a.size) (hi : i < a.size) :
    (a.modify j f).get! i = if j = i then f (a.get! i) else a.get! i := by
  have hi' : i < (a.modify j f).size := by
    simpa [Array.size_modify] using hi
  -- switch to `getElem` so we can use `Array.getElem_modify`
  simp [array_get!_eq_getElem_of_lt, hi, hi', Array.getElem_modify, hj]


lemma mkArray_size (n : Nat) (v : Nat) : (Array.mkArray n v).size = n := by
  simp [Array.mkArray]

lemma mkArray_get! (n : Nat) (v : Nat) (i : Nat) (hi : i < n) :
    (Array.mkArray n v).get! i = v := by
  have hi' : i < (Array.mkArray n v).size := by
    simpa [mkArray_size n v] using hi
  -- unfold `mkArray` to see that every entry is `v`
  have : (Array.mkArray n v)[i]'hi' = v := by
    simp [Array.mkArray]
  simpa [array_get!_eq_getElem_of_lt, hi'] using this


lemma foldl_modify_add_count (xs : List Char) (a : Array Nat) (c : Char)
    (hsz : a.size = 0x110000) :
    (List.foldl (fun a c => a.modify c.toNat (fun v => v + 1)) a xs).get! c.toNat =
      a.get! c.toNat + xs.count c := by
  induction xs generalizing a with
  | nil =>
      simp
  | cons d ds ih =>
      have hc : c.toNat < a.size := by
        simpa [hsz] using (char_toNat_lt_size c)
      have hd : d.toNat < a.size := by
        simpa [hsz] using (char_toNat_lt_size d)
      have hsz' : (a.modify d.toNat (fun v => v + 1)).size = 0x110000 := by
        simpa [Array.size_modify, hsz]
      have ih' := ih (a := a.modify d.toNat (fun v => v + 1)) hsz'
      by_cases hdc : d = c
      · subst hdc
        have hmod : (a.modify d.toNat (fun v => v + 1)).get! d.toNat = a.get! d.toNat + 1 := by
          simpa [array_get!_modify_of_lt, hd, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using (array_get!_modify_of_lt (a := a) (j := d.toNat) (i := d.toNat)
              (f := fun v : Nat => v + 1) (hj := hd) (hi := hd))
        simpa [List.foldl, ih', List.count_cons, hmod, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      ·
        have hnat : d.toNat ≠ c.toNat := by
          intro h'
          apply hdc
          have : Char.ofNat d.toNat = Char.ofNat c.toNat := congrArg Char.ofNat h'
          simpa [Char.ofNat_toNat] using this
        have hmod : (a.modify d.toNat (fun v => v + 1)).get! c.toNat = a.get! c.toNat := by
          have := array_get!_modify_of_lt (a := a) (j := d.toNat) (i := c.toNat)
            (f := fun v : Nat => v + 1) (hj := hd) (hi := hc)
          simpa [hnat] using this
        simpa [List.foldl, ih', List.count_cons, hdc, hmod, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

lemma freq_foldl_count (magazine : List Char) (c : Char) :
    (List.foldl (fun a c => a.modify c.toNat (fun v => v + 1)) (Array.mkArray 0x110000 0) magazine).get! c.toNat =
      magazine.count c := by
  have hsz0 : (Array.mkArray 0x110000 (0 : Nat)).size = 0x110000 := by
    simpa using (mkArray_size 0x110000 (0 : Nat))
  have hc : c.toNat < 0x110000 := char_toNat_lt_size c
  have hinit : (Array.mkArray 0x110000 (0 : Nat)).get! c.toNat = 0 := by
    simpa using (mkArray_get! 0x110000 (0 : Nat) c.toNat hc)
  have := foldl_modify_add_count (xs := magazine) (a := Array.mkArray 0x110000 (0 : Nat)) (c := c) hsz0
  simpa [hinit, Nat.zero_add] using this

theorem correctness_goal_0
    (magazine : List Char)
    : ∀ (c : Char),
  (List.foldl (fun a c => a.modify c.toNat fun v => v + 1) (mkArray 1114112 0) magazine).get! c.toNat =
    List.count c magazine := by
    intros; expose_names; exact freq_foldl_count magazine c

section
  lemma Array.get!_modify_sub1_self (a : Array Nat) (i : Nat) :
      (a.modify i (fun w => w - 1)).get! i = a.get! i - 1 := by
    -- rewrite `get!` via `getElem?`
    simp [Array.get!_eq_getD_getElem?, Array.getElem?_modify]
    -- now reason by cases on `a[i]?`
    cases hopt : a[i]? with
    | none =>
        simp [hopt]
    | some v =>
        simp [hopt]

  lemma Array.get!_modify_sub1_of_ne (a : Array Nat) (i j : Nat) (h : j ≠ i) :
      (a.modify i (fun w => w - 1)).get! j = a.get! j := by
    have hij : i ≠ j := Ne.symm h
    simp [Array.get!_eq_getD_getElem?, Array.getElem?_modify, hij]
end


theorem correctness_goal_1 : ∀ (a : Array ℕ) (xs : List Char),
  implementation.consume (fun a c => if a.get! c.toNat = 0 then none else some (a.modify c.toNat fun w => w - 1)) a xs =
      true ↔
    ∀ (c : Char), List.count c xs ≤ a.get! c.toNat := by
  intro a xs
  induction xs generalizing a with
  | nil =>
      constructor
      · intro _h
        intro c
        simp
      · intro _h
        simp [implementation.consume]
  | cons x xs ih =>
      classical
      by_cases hx0 : a.get! x.toNat = 0
      · constructor
        · intro h
          have : False := by
            simpa [implementation.consume, hx0] using h
          exact False.elim this
        · intro h
          have : False := by
            have hx := h x
            simpa [List.count_cons, hx0] using hx
          exact False.elim this
      ·
        let a' : Array Nat := a.modify x.toNat (fun w => w - 1)
        have hxpos : 0 < a.get! x.toNat := Nat.pos_of_ne_zero hx0
        have h1le : 1 ≤ a.get! x.toNat := (Nat.succ_le_iff).2 hxpos
        have h_consume :
            implementation.consume
                (fun a c => if a.get! c.toNat = 0 then none else some (a.modify c.toNat fun w => w - 1))
                a (x :: xs)
              = implementation.consume
                  (fun a c => if a.get! c.toNat = 0 then none else some (a.modify c.toNat fun w => w - 1))
                  a' xs := by
          simp [implementation.consume, hx0, a']
        constructor
        · intro h
          have h' :
              implementation.consume
                  (fun a c => if a.get! c.toNat = 0 then none else some (a.modify c.toNat fun w => w - 1))
                  a' xs
                = true := by
            simpa [h_consume] using h
          have hcs : ∀ c : Char, List.count c xs ≤ a'.get! c.toNat := (ih (a := a')).1 h'
          intro c
          by_cases hc : c = x
          · -- c = x
            -- substitute `c` (not `x`)
            subst c
            have hle : List.count x xs ≤ a.get! x.toNat - 1 := by
              simpa [a', Array.get!_modify_sub1_self] using (hcs x)
            have hle' : List.count x xs + 1 ≤ (a.get! x.toNat - 1) + 1 :=
              Nat.add_le_add_right hle 1
            have : List.count x (x :: xs) ≤ a.get! x.toNat := by
              simpa [List.count_cons, Nat.sub_add_cancel h1le, Nat.add_assoc] using hle'
            simpa using this
          · -- c ≠ x
            have hidx : c.toNat ≠ x.toNat := by
              intro hEq
              apply hc
              apply Char.eq_of_val_eq
              -- show equality of UInt32 values using injectivity of `UInt32.toNat`
              apply UInt32.toNat.inj
              simpa [Char.toNat] using hEq
            have hget : a'.get! c.toNat = a.get! c.toNat := by
              simpa [a', hidx] using
                (Array.get!_modify_sub1_of_ne (a := a) (i := x.toNat) (j := c.toNat) hidx)
            have hle : List.count c xs ≤ a.get! c.toNat := by
              simpa [hget] using (hcs c)
            simpa [List.count_cons_of_ne (Ne.symm hc)] using hle
        · intro h
          have hcs : ∀ c : Char, List.count c xs ≤ a'.get! c.toNat := by
            intro c
            by_cases hc : c = x
            · subst c
              have hx := h x
              have hsucc : Nat.succ (List.count x xs) ≤ a.get! x.toNat := by
                simpa [List.count_cons, Nat.add_assoc] using hx
              have hlt : List.count x xs < a.get! x.toNat := Nat.lt_of_succ_le hsucc
              have hle : List.count x xs ≤ a.get! x.toNat - 1 := Nat.le_pred_of_lt hlt
              simpa [a', Array.get!_modify_sub1_self] using hle
            ·
              have hidx : c.toNat ≠ x.toNat := by
                intro hEq
                apply hc
                apply Char.eq_of_val_eq
                apply UInt32.toNat.inj
                simpa [Char.toNat] using hEq
              have hget : a'.get! c.toNat = a.get! c.toNat := by
                simpa [a', hidx] using
                  (Array.get!_modify_sub1_of_ne (a := a) (i := x.toNat) (j := c.toNat) hidx)
              have hc_count : List.count c xs = List.count c (x :: xs) := by
                symm
                simpa [List.count_cons_of_ne (Ne.symm hc)]
              have := h c
              simpa [hc_count, hget] using this
          have h' :
              implementation.consume
                  (fun a c => if a.get! c.toNat = 0 then none else some (a.modify c.toNat fun w => w - 1))
                  a' xs
                = true := (ih (a := a')).2 hcs
          simpa [h_consume] using h'

theorem correctness_goal
    (ransomNote : List Char)
    (magazine : List Char)
    (h_precond : precondition ransomNote magazine)
    : postcondition ransomNote magazine (implementation ransomNote magazine) := by
  -- precondition is trivial
  simp [precondition] at h_precond
  -- unfold the spec
  simp [postcondition, canConstructProp]

  -- Rewrite the implementation to expose the auxiliary recursive function `implementation.consume`.
  -- (This is what Lean generates from the local `let rec consume`.)
  simp [implementation]

  -- Key fact (1): the frequency table built from `magazine` stores `List.count`.
  have h_freq :
      ∀ c : Char,
        (List.foldl (fun (a : Array Nat) (c : Char) => a.modify c.toNat (fun v => v + 1))
            (Array.mkArray 0x110000 0) magazine).get! c.toNat =
          magazine.count c := by
    expose_names; exact (correctness_goal_0 magazine)

  -- Key fact (2): consuming succeeds iff there are enough characters for all counts.
  have h_consume :
      ∀ (a : Array Nat) (xs : List Char),
        implementation.consume
            (fun (a : Array Nat) (c : Char) =>
              if a.get! c.toNat = 0 then none else some (a.modify c.toNat (fun w => w - 1)))
            a xs = true ↔
          ∀ c : Char, xs.count c ≤ a.get! c.toNat := by
    expose_names; exact (correctness_goal_1)

  -- Finish by combining the two facts.
  -- `simp [h_consume]` reduces the goal to the per-character inequality on the initial frequency table,
  -- then `simp [h_freq]` turns that into the desired `List.count` inequality.
  simpa [h_consume, h_freq]
end Proof
