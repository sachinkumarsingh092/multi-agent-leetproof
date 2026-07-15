import Lean
import Mathlib.Tactic
import Velvet.Std
import Extensions.VelvetPBT

set_option maxHeartbeats 10000000

section Specs
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false
set_option pp.funBinderTypes true

/- Problem Description
    CountingBits: Given a natural number n, return an array ans of length n + 1
    where ans[i] is the number of 1-bits in the binary representation of i.
    **Important: complexity should be O(n) time and O(n) space**
    Natural language breakdown:
    1. The input n is a natural number.
    2. The output ans is an array of natural numbers.
    3. The output array has length exactly n + 1.
    4. For every index i with 0 ≤ i ≤ n (equivalently i < ans.size), ans[i] equals the count of bit positions k
       where the k-th bit of i is 1.
    5. Because i ≤ n, it suffices to count 1-bits among bit positions k < n + 1 (a simple, explicit bound).
       This bound is used only for specification purposes.
-/

-- Helper: count of 1-bits of i restricted to bit positions k < bnd.
-- We use `Nat.testBit i k : Bool` and count how many k in `Finset.range bnd` have `testBit = true`.
-- (This avoids relying on a library `Nat.popcount` constant that may not be available.)
def popcountUpTo (bnd : Nat) (i : Nat) : Nat :=
  ((Finset.range bnd).filter (fun k : Nat => i.testBit k)).card

def precondition (n : Nat) : Prop :=
  True

def postcondition (n : Nat) (ans : Array Nat) : Prop :=
  ans.size = n + 1 ∧
  (∀ (i : Nat), i < ans.size → ans[i]! = popcountUpTo (n + 1) i)
end Specs

section Impl
def implementation (n : Nat) : Array Nat :=
  -- Build the answer using the recurrence:
  --   ans[0] = 0
  --   ans[i+1] = ans[(i+1)/2] + ((i+1) % 2)
  -- We use a `Nat.rec` loop to avoid termination issues.
  let step (i : Nat) (acc : Array Nat) : Array Nat :=
    let j : Nat := i + 1
    let half : Nat := j / 2
    let bit : Nat := j % 2
    let prev : Nat := acc[half]!
    acc.push (prev + bit)
  (Nat.rec (motive := fun _ => Array Nat)
      (#[0])
      (fun i acc => step i acc)
      n)
end Impl

section TestCases
-- Test case 1: Example 1
-- Input: n = 2
-- Output: [0,1,1]
def test1_n : Nat := 2
def test1_Expected : Array Nat := #[0, 1, 1]

-- Test case 2: Example 2
-- Input: n = 5
-- Output: [0,1,1,2,1,2]
def test2_n : Nat := 5
def test2_Expected : Array Nat := #[0, 1, 1, 2, 1, 2]

-- Test case 3: Edge case n = 0
-- Output: [0]
def test3_n : Nat := 0
def test3_Expected : Array Nat := #[0]

-- Test case 4: Edge case n = 1
-- Output: [0,1]
def test4_n : Nat := 1
def test4_Expected : Array Nat := #[0, 1]

-- Test case 5: Small n = 3
-- Output: [0,1,1,2]
def test5_n : Nat := 3
def test5_Expected : Array Nat := #[0, 1, 1, 2]

-- Test case 6: n = 8 (includes a power of two)
-- Output: [0,1,1,2,1,2,2,3,1]
def test6_n : Nat := 8
def test6_Expected : Array Nat := #[0, 1, 1, 2, 1, 2, 2, 3, 1]

-- Test case 7: n = 10 (typical mid-size)
-- Output: [0,1,1,2,1,2,2,3,1,2,2]
def test7_n : Nat := 10
def test7_Expected : Array Nat := #[0, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2]

-- Test case 8: n = 16 (includes another power of two)
-- Output: [0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,1]
def test8_n : Nat := 16
def test8_Expected : Array Nat := #[0, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 2, 3, 3, 4, 1]

-- Recommend to validate: test1_n, test2_n, test3_n
end TestCases

section Assertions
-- Test case 1
#assert_same_evaluation #[(implementation test1_n), test1_Expected]

-- Test case 2
#assert_same_evaluation #[(implementation test2_n), test2_Expected]

-- Test case 3
#assert_same_evaluation #[(implementation test3_n), test3_Expected]

-- Test case 4
#assert_same_evaluation #[(implementation test4_n), test4_Expected]

-- Test case 5
#assert_same_evaluation #[(implementation test5_n), test5_Expected]

-- Test case 6
#assert_same_evaluation #[(implementation test6_n), test6_Expected]

-- Test case 7
#assert_same_evaluation #[(implementation test7_n), test7_Expected]

-- Test case 8
#assert_same_evaluation #[(implementation test8_n), test8_Expected]
end Assertions

section Pbt
method implementationPbt (n : Nat)
  return (result : Array Nat)
  require precondition n
  ensures postcondition n result
  do
  return (implementation n)

velvet_plausible_test implementationPbt (config := { maxMs := some 20000 })
end Pbt

section Proof

open Finset

theorem popcountUpTo_succ (bnd x : Nat) :
    popcountUpTo (bnd + 1) x = popcountUpTo bnd (x / 2) + (x % 2) := by
  classical
  unfold popcountUpTo

  have hrange : Finset.range (bnd + 1) =
      Finset.range 1 ∪ (Finset.range bnd).map (addLeftEmbedding 1) := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using (Finset.range_add 1 bnd)

  rw [hrange]
  rw [Finset.filter_union]

  have hdisj : Disjoint (Finset.range 1) ((Finset.range bnd).map (addLeftEmbedding 1)) := by
    simpa using (Finset.disjoint_range_addLeftEmbedding 1 (Finset.range bnd))
  have hdisj' :
      Disjoint ((Finset.range 1).filter (fun k : Nat => x.testBit k = true))
        (((Finset.range bnd).map (addLeftEmbedding 1)).filter (fun k : Nat => x.testBit k = true)) :=
    Finset.disjoint_filter_filter (p := fun k : Nat => x.testBit k = true)
      (q := fun k : Nat => x.testBit k = true) hdisj

  rw [Finset.card_union_of_disjoint hdisj']

  have hr1 : Finset.range 1 = ({0} : Finset Nat) := by
    simp [Finset.range_succ]

  have hlsb : ((Finset.range 1).filter (fun k : Nat => x.testBit k = true)).card = x % 2 := by
    -- reduce to filtering the singleton `{0}`
    have hx : x % 2 = 0 ∨ x % 2 = 1 := Nat.mod_two_eq_zero_or_one x
    cases hx with
    | inl h0 =>
        have ht : x.testBit 0 = false := (Nat.mod_two_eq_zero_iff_testBit_zero).1 h0
        have : ({0} : Finset Nat).filter (fun k : Nat => x.testBit k = true) = ∅ := by
          ext k
          by_cases hk : k = 0
          · subst hk; simp [ht]
          · simp [hk]
        -- `range 1` case
        simpa [hr1, this, h0]
    | inr h1 =>
        have ht : x.testBit 0 = true := (Nat.mod_two_eq_one_iff_testBit_zero).1 h1
        have : ({0} : Finset Nat).filter (fun k : Nat => x.testBit k = true) = {0} := by
          ext k
          by_cases hk : k = 0
          · subst hk; simp [ht]
          · simp [hk]
        simpa [hr1, this, h1]

  have hrest :
      (((Finset.range bnd).map (addLeftEmbedding 1)).filter (fun k : Nat => x.testBit k = true)).card =
        ((Finset.range bnd).filter (fun k : Nat => (x / 2).testBit k = true)).card := by
    -- reindex the range by `k ↦ k+1`
    rw [Finset.filter_map]
    have hcard :
        (((Finset.range bnd).filter ((fun k : Nat => x.testBit k = true) ∘ (addLeftEmbedding 1))).map (addLeftEmbedding 1)).card =
          ((Finset.range bnd).filter ((fun k : Nat => x.testBit k = true) ∘ (addLeftEmbedding 1))).card := by
      simpa using
        (Finset.card_map (f := addLeftEmbedding 1)
          (s := (Finset.range bnd).filter ((fun k : Nat => x.testBit k = true) ∘ (addLeftEmbedding 1))))
    rw [hcard]
    apply congrArg Finset.card
    ext k
    simp [Function.comp, Nat.testBit_add_one, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

  -- Finish: substitute the computed cards.
  rw [hlsb, hrest]
  -- commutativity of addition
  simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]


theorem correctness_goal
    (n : Nat)
    (h_precond : precondition n)
    : postcondition n (implementation n) := by
  classical
  -- precondition is trivial
  have _ : True := h_precond

  let step (i : Nat) (acc : Array Nat) : Array Nat :=
    let j : Nat := i + 1
    let half : Nat := j / 2
    let bit : Nat := j % 2
    acc.push (acc.get! half + bit)

  let acc : Nat → Array Nat :=
    fun m => Nat.rec (motive := fun _ => Array Nat) (#[0]) (fun i a => step i a) m

  -- in-bounds `get!` equals `getElem`
  have get!_eq_get {xs : Array Nat} {i : Nat} (h : i < xs.size) : xs.get! i = xs[i] := by
    -- unfold via `getD`/`get?`
    simp [Array.get!_eq_getD, Array.getD, Array.get?, h]

  -- `get!` after `push`.
  have get!_push_lt {xs : Array Nat} (x : Nat) {i : Nat} (h : i < xs.size) :
      (xs.push x).get! i = xs.get! i := by
    have hi : i < (xs.push x).size := by
      simpa [Array.size_push] using Nat.lt_trans h (Nat.lt_succ_self xs.size)
    have hpush : (xs.push x)[i] = xs[i] := by
      have := Array.getElem_push (xs := xs) (x := x) (i := i) hi
      simpa [h, hi] using this
    calc
      (xs.push x).get! i = (xs.push x)[i] := get!_eq_get (xs := xs.push x) (i := i) hi
      _ = xs[i] := hpush
      _ = xs.get! i := by simpa using (get!_eq_get (xs := xs) (i := i) h).symm

  have get!_push_size {xs : Array Nat} (x : Nat) :
      (xs.push x).get! xs.size = x := by
    have hi : xs.size < (xs.push x).size := by
      simpa [Array.size_push] using Nat.lt_succ_self xs.size
    have hpush : (xs.push x)[xs.size] = x := by
      have := Array.getElem_push (xs := xs) (x := x) (i := xs.size) hi
      have hnlt : ¬xs.size < xs.size := Nat.lt_irrefl _
      simpa [hi, hnlt] using this
    calc
      (xs.push x).get! xs.size = (xs.push x)[xs.size] := get!_eq_get (xs := xs.push x) (i := xs.size) hi
      _ = x := hpush

  -- If the top bit is false, increasing the bound by one does not change `popcountUpTo`.
  have popcountUpTo_succ_of_testBit_false (x : Nat) (hx : x.testBit n = false) :
      popcountUpTo (n + 1) x = popcountUpTo n x := by
    classical
    unfold popcountUpTo
    rw [Finset.range_succ]
    have :
        (insert n (Finset.range n)).filter (fun k : Nat => x.testBit k = true) =
          (Finset.range n).filter (fun k : Nat => x.testBit k = true) := by
      ext k
      by_cases hk : k = n
      · subst hk
        simp [hx]
      · simp [hk]
    simp [this]

  have hinv : ∀ m, m ≤ n →
      (acc m).size = m + 1 ∧
      (∀ i : Nat, i < (acc m).size → (acc m).get! i = popcountUpTo (n + 1) i) := by
    intro m hm
    induction m with
    | zero =>
        constructor
        · simp [acc]
        · intro i hi
          have hi0 : i = 0 := by
            apply Nat.eq_of_lt_succ_of_not_lt
            · simpa [acc] using hi
            · simp
          subst hi0
          simp [Array.get!_eq_getD, Array.getD, acc, popcountUpTo]
    | succ m ih =>
        have hm' : m ≤ n := Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self m)) hm
        have ih' := ih hm'
        cases ih' with
        | intro hsize hvals =>
          let a : Array Nat := acc m
          have ha_size : a.size = m + 1 := by simpa [a] using hsize

          have hacc_succ : acc (Nat.succ m) = step m a := by
            simp [acc, a]

          let j : Nat := m + 1
          let half : Nat := j / 2
          let bit : Nat := j % 2
          let newVal : Nat := a.get! half + bit
          have hstep : step m a = a.push newVal := by
            simp [step, j, half, bit, newVal]

          constructor
          · simp [hacc_succ, hstep, ha_size, Array.size_push, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
          · intro i hi
            have hi' : i < (a.push newVal).size := by
              simpa [hacc_succ, hstep] using hi
            by_cases hlt : i < a.size
            · have hget : (a.push newVal).get! i = a.get! i := get!_push_lt (xs := a) newVal hlt
              have hold : a.get! i = popcountUpTo (n + 1) i := by
                have : i < (acc m).size := by simpa [a] using hlt
                simpa [a] using hvals i this
              simpa [hacc_succ, hstep, hget, hold]
            · have hi_eq : i = a.size := by
                have : i < a.size.succ := by
                  simpa [Array.size_push] using hi'
                exact Nat.eq_of_lt_succ_of_not_lt this hlt
              subst hi_eq
              have hget_last : (a.push newVal).get! a.size = newVal := get!_push_size (xs := a) newVal

              have ha_size' : a.size = j := by simpa [a, j] using ha_size
              have hhalf_lt_asize : half < a.size := by
                have : half < j := by
                  have hjpos : 0 < j := by simpa [j] using Nat.succ_pos m
                  simpa [half, j] using (Nat.div_lt_self hjpos (by decide : 1 < 2))
                simpa [ha_size'] using this

              have hprev : a.get! half = popcountUpTo (n + 1) half := by
                have : half < (acc m).size := by simpa [a] using hhalf_lt_asize
                simpa [a] using hvals half this

              have hj_le_n : j ≤ n := by simpa [j] using hm
              have hhalf_bitfalse : half.testBit n = false := by
                have hnlt : n < 2 ^ n := Nat.lt_two_pow_self
                have hhalf_le_n : half ≤ n := by
                  have hhalf_le_j : half ≤ j := by simpa [half] using (Nat.div_le_self j 2)
                  exact Nat.le_trans hhalf_le_j hj_le_n
                have hhalf_lt : half < 2 ^ n := lt_of_le_of_lt hhalf_le_n hnlt
                exact Nat.testBit_lt_two_pow hhalf_lt

              have hhalf_pop : popcountUpTo (n + 1) half = popcountUpTo n half :=
                popcountUpTo_succ_of_testBit_false half hhalf_bitfalse

              have hrec0 : popcountUpTo (n + 1) j = popcountUpTo n (j / 2) + (j % 2) := by
                simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using (popcountUpTo_succ n j)

              have hrec : popcountUpTo (n + 1) j = popcountUpTo (n + 1) half + bit := by
                calc
                  popcountUpTo (n + 1) j
                      = popcountUpTo n (j / 2) + (j % 2) := hrec0
                  _ = popcountUpTo n half + bit := by simp [half, bit]
                  _ = popcountUpTo (n + 1) half + bit := by
                        rw [← hhalf_pop]

              have hnew : newVal = popcountUpTo (n + 1) j := by
                calc
                  newVal = popcountUpTo (n + 1) half + bit := by
                    simp [newVal, hprev]
                  _ = popcountUpTo (n + 1) j := by
                    simpa using hrec.symm

              have : (acc (Nat.succ m)).get! a.size = popcountUpTo (n + 1) a.size := by
                calc
                  (acc (Nat.succ m)).get! a.size = newVal := by
                    simp [hacc_succ, hstep, hget_last]
                  _ = popcountUpTo (n + 1) j := hnew
                  _ = popcountUpTo (n + 1) a.size := by simpa [ha_size']

              simpa [hacc_succ, hstep] using this

  have hfinal := hinv n le_rfl
  cases hfinal with
  | intro hsz hvals =>
    refine And.intro ?_ ?_
    · simpa [implementation, acc, step] using hsz
    · intro i hi
      have : (implementation n).get! i = popcountUpTo (n + 1) i := by
        simpa [implementation, acc, step] using hvals i (by simpa [implementation, acc, step] using hi)
      simpa using this
end Proof
