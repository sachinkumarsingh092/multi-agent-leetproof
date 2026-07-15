import Lean
import Mathlib.Tactic
import Velvet.Std

set_option maxHeartbeats 10000000

section Specs
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false

/- Problem Description
    917. Reverse Only Letters: Reverse only the English letters in a character sequence, keeping non-letters fixed.
    **Important: complexity should be O(n) time and O(n) space**
    Natural language breakdown:
    1. Input is a finite sequence of characters.
    2. A character is considered an English letter exactly when it is an ASCII uppercase letter ('A'..'Z') or an ASCII lowercase letter ('a'..'z').
    3. Every non-letter character must stay at the same index in the output.
    4. The set of indices that contain letters must be the same in input and output.
    5. Reading only the letters from left to right in the output yields the reverse of the letters read from left to right in the input.
    6. The output has the same length as the input.
-/

-- Helper predicate: ASCII uppercase letter ('A'..'Z').
def isAsciiUpper (c : Char) : Bool :=
  ('A'.toNat ≤ c.toNat) && (c.toNat ≤ 'Z'.toNat)

-- Helper predicate: ASCII lowercase letter ('a'..'z').
def isAsciiLower (c : Char) : Bool :=
  ('a'.toNat ≤ c.toNat) && (c.toNat ≤ 'z'.toNat)

-- Helper predicate: English letter (ASCII) is upper or lower.
def isLetter (c : Char) : Bool :=
  isAsciiUpper c || isAsciiLower c

-- Helper: extract the subsequence of letters.
def letters (s : List Char) : List Char :=
  s.filter (fun c => isLetter c)

-- No special input restrictions.
def precondition (s : List Char) : Prop :=
  True

-- Postcondition: length preserved; non-letters fixed; letter mask preserved; letters reversed.
def postcondition (s : List Char) (result : List Char) : Prop :=
  result.length = s.length ∧
  (∀ (i : Nat), i < s.length → (isLetter s[i]! = false) → result[i]! = s[i]!) ∧
  (∀ (i : Nat), i < s.length → isLetter result[i]! = isLetter s[i]!) ∧
  letters result = (letters s).reverse
end Specs

section Impl
def implementation (s : List Char) : List Char :=
  -- Re-define the ASCII letter predicate locally (cannot use spec helpers).
  let isUpper : Char → Bool := fun c =>
    ('A'.toNat ≤ c.toNat) && (c.toNat ≤ 'Z'.toNat)
  let isLower : Char → Bool := fun c =>
    ('a'.toNat ≤ c.toNat) && (c.toNat ≤ 'z'.toNat)
  let isLet : Char → Bool := fun c => isUpper c || isLower c

  -- Collect letters once, reverse them, then refill left-to-right.
  let revLetters : List Char := (s.filter isLet).reverse

  let rec go (xs : List Char) (ls : List Char) (acc : List Char) : List Char :=
    match xs with
    | [] => acc.reverse
    | x :: xs' =>
        if isLet x then
          match ls with
          | [] =>
              -- Should not happen: ls comes from the letters of s.
              go xs' [] (x :: acc)
          | l :: ls' => go xs' ls' (l :: acc)
        else
          go xs' ls (x :: acc)

  go s revLetters []
end Impl

section TestCases
-- Test case 1: example 1
-- Input: "ab-cd"  Output: "dc-ba"
def test1_s : List Char := ['a','b','-','c','d']
def test1_Expected : List Char := ['d','c','-','b','a']

-- Test case 2: example 2
-- Input: "a-bC-dEf-ghIj"  Output: "j-Ih-gfE-dCba"
def test2_s : List Char := ['a','-','b','C','-','d','E','f','-','g','h','I','j']
def test2_Expected : List Char := ['j','-','I','h','-','g','f','E','-','d','C','b','a']

-- Test case 3: example 3
-- Input: "Test1ng-Leet=code-Q!"  Output: "Qedo1ct-eeLg=ntse-T!"
def test3_s : List Char :=
  ['T','e','s','t','1','n','g','-','L','e','e','t','=','c','o','d','e','-','Q','!']
def test3_Expected : List Char :=
  ['Q','e','d','o','1','c','t','-','e','e','L','g','=','n','t','s','e','-','T','!']

-- Test case 4: empty input

def test4_s : List Char := []
def test4_Expected : List Char := []

-- Test case 5: only letters (all reversed)

def test5_s : List Char := ['A','b','C','d']
def test5_Expected : List Char := ['d','C','b','A']

-- Test case 6: only non-letters (unchanged)

def test6_s : List Char := ['-','1','_','!']
def test6_Expected : List Char := ['-','1','_','!']

-- Test case 7: single character that is a letter

def test7_s : List Char := ['z']
def test7_Expected : List Char := ['z']

-- Test case 8: single character that is not a letter

def test8_s : List Char := ['?']
def test8_Expected : List Char := ['?']

-- Test case 9: letters separated by digits and punctuation
-- Input letters: a b c d e; reversed: e d c b a
-- Non-letters stay in place.

def test9_s : List Char := ['a','1','b','2','-','c','3','d','4','e']
def test9_Expected : List Char := ['e','1','d','2','-','c','3','b','4','a']

-- Recommend to validate: empty input, inputs with only non-letters, inputs mixing letters/non-letters
end TestCases

section Assertions
-- Test case 1
#assert_same_evaluation #[(implementation test1_s), test1_Expected]

-- Test case 2
#assert_same_evaluation #[(implementation test2_s), test2_Expected]

-- Test case 3
#assert_same_evaluation #[(implementation test3_s), test3_Expected]

-- Test case 4
#assert_same_evaluation #[(implementation test4_s), test4_Expected]

-- Test case 5
#assert_same_evaluation #[(implementation test5_s), test5_Expected]

-- Test case 6
#assert_same_evaluation #[(implementation test6_s), test6_Expected]

-- Test case 7
#assert_same_evaluation #[(implementation test7_s), test7_Expected]

-- Test case 8
#assert_same_evaluation #[(implementation test8_s), test8_Expected]

-- Test case 9
#assert_same_evaluation #[(implementation test9_s), test9_Expected]
end Assertions

section Proof
theorem correctness_goal
    (s : List Char)
    : postcondition s (implementation s) := by
  classical

  let p : Char → Bool := fun c =>
    (('A'.toNat ≤ c.toNat) && (c.toNat ≤ 'Z'.toNat)) ||
      (('a'.toNat ≤ c.toNat) && (c.toNat ≤ 'z'.toNat))

  have hp : ∀ c, p c = isLetter c := by
    intro c
    simp [p, isLetter, isAsciiUpper, isAsciiLower]

  let fill : List Char → List Char → List Char :=
    fun xs =>
      xs.rec (motive := fun _ => List Char → List Char)
        (fun _ls => [])
        (fun x xs ih ls =>
          if p x then
            match ls with
            | [] => x :: ih []
            | l :: ls' => l :: ih ls'
          else
            x :: ih ls)

  have fill_nil (ls : List Char) : fill [] ls = [] := by
    simp [fill]

  have fill_cons (x : Char) (xs ls : List Char) :
      fill (x :: xs) ls =
        if p x then
          match ls with
          | [] => x :: fill xs []
          | l :: ls' => l :: fill xs ls'
        else
          x :: fill xs ls := by
    simp [fill]

  have himpl_go :
      implementation s =
        implementation.go p s ((s.filter p).reverse) [] := by
    simp [implementation, p]

  have hgo_eq :
      ∀ xs ls acc,
        implementation.go p xs ls acc = acc.reverse ++ fill xs ls := by
    intro xs
    induction xs with
    | nil =>
        intro ls acc
        simp [implementation.go, fill_nil]
    | cons x xs ih =>
        intro ls acc
        by_cases hx : p x
        · cases ls with
          | nil =>
              simp [implementation.go, fill_cons, hx, ih, List.append_assoc]
          | cons l ls' =>
              simp [implementation.go, fill_cons, hx, ih, List.append_assoc]
        ·
          simp [implementation.go, fill_cons, hx, ih, List.append_assoc]

  have himpl_fill :
      implementation s = fill s ((s.filter p).reverse) := by
    simp [himpl_go, hgo_eq]

  have hfill_length : ∀ xs ls, (fill xs ls).length = xs.length := by
    intro xs
    induction xs with
    | nil =>
        intro ls
        simp [fill_nil]
    | cons x xs ih =>
        intro ls
        by_cases hx : p x
        · cases ls with
          | nil => simp [fill_cons, hx, ih]
          | cons l ls' => simp [fill_cons, hx, ih]
        · simp [fill_cons, hx, ih]

  have hfill_get_nonletter :
      ∀ xs ls i,
        i < xs.length → p xs[i]! = false → (fill xs ls)[i]! = xs[i]! := by
    intro xs
    induction xs with
    | nil =>
        intro ls i hi
        simp at hi
    | cons x xs ih =>
        intro ls i hi hpx
        cases i with
        | zero =>
            have : p x = false := by simpa [List.get!_cons_zero] using hpx
            simp [fill_cons, this, List.get!_cons_zero]
        | succ i =>
            have hi' : i < xs.length := Nat.lt_of_succ_lt_succ hi
            by_cases hx : p x
            · cases ls with
              | nil =>
                  simpa [fill_cons, hx, List.get!_cons_succ] using
                    ih [] i hi' (by simpa [List.get!_cons_succ] using hpx)
              | cons l ls' =>
                  simpa [fill_cons, hx, List.get!_cons_succ] using
                    ih ls' i hi' (by simpa [List.get!_cons_succ] using hpx)
            ·
              simpa [fill_cons, hx, List.get!_cons_succ] using
                ih ls i hi' (by simpa [List.get!_cons_succ] using hpx)

  have hAllP : ∀ (xs : List Char), ∀ c ∈ (xs.filter p).reverse, p c = true := by
    intro xs c hc
    have : c ∈ xs.filter p := by
      simpa using (List.mem_reverse.mp hc)
    exact (List.mem_filter.mp this).2

  have hfill_mask :
      ∀ xs ls,
        (∀ c ∈ ls, p c = true) →
        ∀ i, i < xs.length → p (fill xs ls)[i]! = p xs[i]! := by
    intro xs
    induction xs with
    | nil =>
        intro ls hall i hi
        simp at hi
    | cons x xs ih =>
        intro ls hall i hi
        cases i with
        | zero =>
            by_cases hx : p x
            · cases ls with
              | nil =>
                  simp [fill_cons, hx, List.get!_cons_zero]
              | cons l ls' =>
                  have hl : p l = true := hall l (by simp)
                  simp [fill_cons, hx, List.get!_cons_zero, hl]
            ·
              simp [fill_cons, hx, List.get!_cons_zero]
        | succ i =>
            have hi' : i < xs.length := Nat.lt_of_succ_lt_succ hi
            by_cases hx : p x
            · cases ls with
              | nil =>
                  simpa [fill_cons, hx, List.get!_cons_succ] using
                    ih [] (by intro c hc; cases hc) i hi'
              | cons l ls' =>
                  have hall' : ∀ c ∈ ls', p c = true := by
                    intro c hc
                    exact hall c (by simp [hc])
                  simpa [fill_cons, hx, List.get!_cons_succ] using
                    ih ls' hall' i hi'
            ·
              simpa [fill_cons, hx, List.get!_cons_succ] using
                ih ls hall i hi'

  have hfill_filter_eq :
      ∀ xs ls,
        (∀ c ∈ ls, p c = true) →
        ls.length = (xs.filter p).length →
        (fill xs ls).filter p = ls := by
    intro xs
    induction xs with
    | nil =>
        intro ls hall hlen
        have : ls = [] := by
          apply List.eq_nil_of_length_eq_zero
          simpa using hlen
        simp [fill_nil, this]
    | cons x xs ih =>
        intro ls hall hlen
        by_cases hx : p x
        · cases ls with
          | nil =>
              exfalso
              have hpos : (0:Nat) < (List.filter p (x :: xs)).length := by
                simp [List.filter, hx]
              have : (List.filter p (x :: xs)).length = 0 := by
                simpa using hlen.symm
              exact (Nat.ne_of_gt hpos) this
          | cons l ls' =>
              have hl : p l = true := hall l (by simp)
              have hall' : ∀ c ∈ ls', p c = true := by
                intro c hc
                exact hall c (by simp [hc])
              have hlen' : ls'.length = (xs.filter p).length := by
                apply Nat.succ.inj
                simpa [List.filter, hx] using hlen
              -- compute
              calc
                (fill (x :: xs) (l :: ls')).filter p
                    = (l :: fill xs ls').filter p := by
                        simp [fill_cons, hx]
                _ = l :: (fill xs ls').filter p := by
                        simp [List.filter, hl]
                _ = l :: ls' := by
                        simp [ih ls' hall' hlen']
        ·
          have hlen' : ls.length = (xs.filter p).length := by
            simpa [List.filter, hx] using hlen
          calc
            (fill (x :: xs) ls).filter p
                = (x :: fill xs ls).filter p := by
                    simp [fill_cons, hx]
            _ = (fill xs ls).filter p := by
                    simp [List.filter, hx]
            _ = ls := ih ls hall hlen'

  unfold postcondition
  refine And.intro ?_ (And.intro ?_ (And.intro ?_ ?_))
  · simpa [himpl_fill, hfill_length]
  · intro i hi hnot
    have hpnot : p s[i]! = false := by
      simpa [hp (s[i]!)] using hnot
    simpa [himpl_fill] using hfill_get_nonletter s ((s.filter p).reverse) i hi hpnot
  · intro i hi
    have hall : ∀ c ∈ ((s.filter p).reverse), p c = true := by
      intro c hc
      exact hAllP s c hc
    have hm : p (fill s ((s.filter p).reverse))[i]! = p s[i]! :=
      hfill_mask s ((s.filter p).reverse) hall i hi
    simpa [himpl_fill, hp _] using hm
  ·
    have hall : ∀ c ∈ ((s.filter p).reverse), p c = true := by
      intro c hc
      exact hAllP s c hc
    have hfilter : (fill s ((s.filter p).reverse)).filter p = (s.filter p).reverse := by
      apply hfill_filter_eq
      · exact hall
      · simp
    have hletters_s : letters s = s.filter p := by
      unfold letters
      simpa using
        (List.filter_congr (l := s) (p := fun c => isLetter c) (q := p)
          (by intro x hx; simpa [hp x]))
    have hletters_res : letters (fill s ((s.filter p).reverse)) = (fill s ((s.filter p).reverse)).filter p := by
      unfold letters
      simpa using
        (List.filter_congr (l := fill s ((s.filter p).reverse)) (p := fun c => isLetter c) (q := p)
          (by intro x hx; simpa [hp x]))
    calc
      letters (implementation s)
          = letters (fill s ((s.filter p).reverse)) := by simpa [himpl_fill]
      _ = (fill s ((s.filter p).reverse)).filter p := by simpa [hletters_res]
      _ = (s.filter p).reverse := hfilter
      _ = (letters s).reverse := by simpa [hletters_s]
end Proof
