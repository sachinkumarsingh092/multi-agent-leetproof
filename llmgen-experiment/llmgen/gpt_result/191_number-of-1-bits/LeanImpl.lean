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
    191. Number of 1 Bits: return the number of set bits in the binary representation of a natural number.
    **Important: complexity should be O(k) time and O(1) space**, where k is the number of set bits in n.
    Natural language breakdown:
    1. Input is a natural number n (non-negative integer).
    2. Each natural number has a binary representation with bits indexed from 0 (least-significant bit) upward.
    3. A bit is set iff it equals 1, i.e. iff n.testBit i = true for that index i.
    4. The required output is the count of indices i for which the bit is set.
    5. For i ≥ n.size (the number of bits needed to represent n), n.testBit i is false, so counting up to n.size suffices.
    6. Edge cases: n = 0 has zero set bits; powers of two have exactly one set bit.
-/

-- We count set bits among indices 0,1,...,n.size-1.
-- For i ≥ n.size, Nat.testBit is false, so the count over this range is the Hamming weight.

def precondition (n : Nat) : Prop :=
  True

def postcondition (n : Nat) (result : Nat) : Prop :=
  result = ((Finset.range n.size).filter (fun (i : Nat) => n.testBit i = true)).card ∧
  result ≤ n.size
end Specs

section Impl
def implementation (n : Nat) : Nat :=
  -- Brian Kernighan's algorithm: repeatedly clear the lowest set bit.
  -- Runs in O(k) iterations where k is the number of set bits in `n`.
  let rec go (m : Nat) (acc : Nat) : Nat :=
    if h0 : m = 0 then
      acc
    else
      go (m &&& (m - 1)) (acc + 1)
  termination_by m
  decreasing_by
    -- show `(m &&& (m - 1)) < m` when `m ≠ 0`
    have hmpos : 0 < m := Nat.pos_of_ne_zero h0
    have hlt : m - 1 < m := Nat.sub_lt hmpos (Nat.succ_pos 0)
    have hle : m &&& (m - 1) ≤ m - 1 := Nat.and_le_right
    exact Nat.lt_of_le_of_lt hle hlt
  go n 0
end Impl

section TestCases
-- Test case 1: Example 1
def test1_n : Nat := 11
def test1_Expected : Nat := 3

-- Test case 2: Example 2
def test2_n : Nat := 128
def test2_Expected : Nat := 1

-- Test case 3: Example 3
def test3_n : Nat := 2147483645
def test3_Expected : Nat := 30

-- Test case 4: boundary n = 0
def test4_n : Nat := 0
def test4_Expected : Nat := 0

-- Test case 5: boundary n = 1
def test5_n : Nat := 1
def test5_Expected : Nat := 1

-- Test case 6: all low bits set (15 = 0b1111)
def test6_n : Nat := 15
def test6_Expected : Nat := 4

-- Test case 7: power of two (16 = 0b10000)
def test7_n : Nat := 16
def test7_Expected : Nat := 1

-- Test case 8: all bits set in a byte (255 = 0b11111111)
def test8_n : Nat := 255
def test8_Expected : Nat := 8

-- Test case 9: all bits set in 10 bits (1023 = 0b1111111111)
def test9_n : Nat := 1023
def test9_Expected : Nat := 10
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

-- Test case 9
#assert_same_evaluation #[(implementation test9_n), test9_Expected]
end Assertions

section Pbt
method implementationPbt (n : Nat)
  return (result : Nat)
  require precondition n
  ensures postcondition n result
  do
  return (implementation n)

velvet_plausible_test implementationPbt (config := { maxMs := some 20000 })
end Pbt

section Proof
theorem correctness_goal_0_0
    (n : ℕ)
    (h_precond : precondition n)
    (m : ℕ)
    (ih : ∀ m_1 < m, ∀ (acc : ℕ), implementation.go m_1 acc = acc + {i ∈ Finset.range m_1.size | m_1.testBit i = true}.card)
    (acc : ℕ)
    (h0 : ¬m = 0)
    (hlt : m &&& m - 1 < m)
    : {i ∈ Finset.range (m &&& m - 1).size | (m &&& m - 1).testBit i = true}.card + 1 =
  {i ∈ Finset.range m.size | m.testBit i = true}.card := by
    sorry

theorem correctness_goal_0
    (n : ℕ)
    (h_precond : precondition n)
    : implementation n = {i ∈ Finset.range n.size | n.testBit i = true}.card := by
  classical
  have _ : True := by simpa [precondition] using h_precond

  have h_go : ∀ m acc,
      implementation.go m acc =
        acc + {i ∈ Finset.range m.size | m.testBit i = true}.card := by
    intro m
    refine Nat.strong_induction_on m ?_
    intro m ih acc
    by_cases h0 : m = 0
    · subst h0
      unfold implementation.go
      simp
    · have hlt : (m &&& (m - 1)) < m := by
        have hmpos : 0 < m := Nat.pos_of_ne_zero h0
        have hlt1 : m - 1 < m := Nat.sub_lt hmpos (Nat.succ_pos 0)
        have hle : m &&& (m - 1) ≤ m - 1 := Nat.and_le_right
        exact Nat.lt_of_le_of_lt hle hlt1
      have hdec :
          {i ∈ Finset.range (m &&& (m - 1)).size | (m &&& (m - 1)).testBit i = true}.card + 1 =
            {i ∈ Finset.range m.size | m.testBit i = true}.card := by
        expose_names; exact (correctness_goal_0_0 n h_precond m ih acc h0 hlt)
      have ih' : implementation.go (m &&& (m - 1)) (acc + 1) =
            (acc + 1) + {i ∈ Finset.range (m &&& (m - 1)).size |
              (m &&& (m - 1)).testBit i = true}.card := by
        simpa using ih (m &&& (m - 1)) hlt (acc + 1)
      unfold implementation.go
      have : implementation.go (m &&& (m - 1)) (acc + 1) = acc +
          {i ∈ Finset.range m.size | m.testBit i = true}.card := by
        calc
          implementation.go (m &&& (m -  1)) (acc + 1)
              = (acc + 1) + {i ∈ Finset.range (m &&& (m - 1)).size |
                  (m &&& (m - 1)).testBit i = true}.card := ih'
          _ = acc + ({i ∈ Finset.range (m &&& (m - 1)).size |
                  (m &&& (m - 1)).testBit i = true}.card + 1) := by
                simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          _ = acc + {i ∈ Finset.range m.size | m.testBit i = true}.card := by
                simpa [Nat.add_assoc] using congrArg (fun t => acc + t) hdec
      simpa [h0, Nat.add_assoc] using this

  simpa [implementation] using (h_go n 0)

theorem correctness_goal
    (n : Nat)
    (h_precond : precondition n)
    : postcondition n (implementation n) := by
  classical
  have h_eq : implementation n = ((Finset.range n.size).filter (fun i : Nat => n.testBit i = true)).card := by
    expose_names; exact (correctness_goal_0 n h_precond)
  have h_le : implementation n ≤ n.size := by
    have hcard : ((Finset.range n.size).filter (fun i : Nat => n.testBit i = true)).card ≤ n.size := by
      have := (Finset.card_filter_le (Finset.range n.size) (fun i : Nat => n.testBit i = true))
      -- simplify card of range
      simpa [Finset.card_range] using this
    -- rewrite with h_eq
    simpa [h_eq] using hcard
  -- package into postcondition
  exact And.intro h_eq h_le
end Proof
