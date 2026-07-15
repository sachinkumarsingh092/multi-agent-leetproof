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
    SingleNumber: in a non-empty array of integers, every element appears exactly twice except for one element that appears once; return that single element.
    **Important: complexity should be O(n) time and O(1) space**
    Natural language breakdown:
    1. The input is an array `nums` of integers and it is non-empty.
    2. There exists an integer `s` that occurs in `nums` exactly once.
    3. Every other integer occurring in `nums` occurs in `nums` exactly twice.
    4. The output must be the unique integer that occurs exactly once.
-/

-- Helper predicate: an element occurs exactly once in an array.
def occursOnce (nums : Array Int) (x : Int) : Prop :=
  nums.count x = 1

-- Helper predicate: an element occurs exactly twice in an array.
def occursTwice (nums : Array Int) (x : Int) : Prop :=
  nums.count x = 2

-- Precondition: the array is non-empty and has exactly one element with count 1,
-- and all other elements appearing in the array have count 2.
def precondition (nums : Array Int) : Prop :=
  nums.size > 0 ∧
  (∃ s : Int,
    s ∈ nums ∧
    occursOnce nums s ∧
    (∀ y : Int, y ∈ nums → y ≠ s → occursTwice nums y))

-- Postcondition: result is the unique element that occurs once.
def postcondition (nums : Array Int) (result : Int) : Prop :=
  result ∈ nums ∧
  occursOnce nums result ∧
  (∀ y : Int, y ∈ nums → occursOnce nums y → y = result)
end Specs

section Impl
def natBitwise (f : Bool → Bool → Bool) (m n : Nat) : Int :=
  if f false false then
    Int.negSucc (Nat.bitwise (fun x y => not (f x y)) m n)
  else
    Int.ofNat (Nat.bitwise f m n)

def intBitwise (f : Bool → Bool → Bool) : Int → Int → Int
  | Int.ofNat m, Int.ofNat n => natBitwise f m n
  | Int.ofNat m, Int.negSucc n => natBitwise (fun x y => f x (not y)) m n
  | Int.negSucc m, Int.ofNat n => natBitwise (fun x y => f (not x) y) m n
  | Int.negSucc m, Int.negSucc n => natBitwise (fun x y => f (not x) (not y)) m n

def implementation (nums : Array Int) : Int :=
  nums.foldl (fun acc x => intBitwise xor acc x) (0 : Int)
end Impl

section TestCases
-- Test case 1: Example 1
-- Input: nums = [2,2,1]
-- Output: 1

def test1_nums : Array Int := #[ (2 : Int), (2 : Int), (1 : Int) ]
def test1_Expected : Int := (1 : Int)

-- Test case 2: Example 2

def test2_nums : Array Int := #[ (4 : Int), (1 : Int), (2 : Int), (1 : Int), (2 : Int) ]
def test2_Expected : Int := (4 : Int)

-- Test case 3: Example 3 (singleton array)

def test3_nums : Array Int := #[ (1 : Int) ]
def test3_Expected : Int := (1 : Int)

-- Test case 4: includes 0 (edge value) with unique 1

def test4_nums : Array Int := #[ (0 : Int), (1 : Int), (0 : Int) ]
def test4_Expected : Int := (1 : Int)

-- Test case 5: includes negative number as the unique element

def test5_nums : Array Int := #[ (-1 : Int), (2 : Int), (2 : Int) ]
def test5_Expected : Int := (-1 : Int)

-- Test case 6: unique element in the middle, multiple pairs

def test6_nums : Array Int := #[ (5 : Int), (5 : Int), (6 : Int), (7 : Int), (7 : Int) ]
def test6_Expected : Int := (6 : Int)

-- Test case 7: larger odd length, unique element at end

def test7_nums : Array Int := #[ (1 : Int), (1 : Int), (2 : Int), (2 : Int), (3 : Int), (3 : Int), (4 : Int) ]
def test7_Expected : Int := (4 : Int)

-- Test case 8: unique element at start

def test8_nums : Array Int := #[ (9 : Int), (8 : Int), (8 : Int), (7 : Int), (7 : Int) ]
def test8_Expected : Int := (9 : Int)

-- Test case 9: singleton array containing 0

def test9_nums : Array Int := #[ (0 : Int) ]
def test9_Expected : Int := (0 : Int)
end TestCases

section Assertions
-- Test case 1
#assert_same_evaluation #[(implementation test1_nums), test1_Expected]

-- Test case 2
#assert_same_evaluation #[(implementation test2_nums), test2_Expected]

-- Test case 3
#assert_same_evaluation #[(implementation test3_nums), test3_Expected]

-- Test case 4
#assert_same_evaluation #[(implementation test4_nums), test4_Expected]

-- Test case 5
#assert_same_evaluation #[(implementation test5_nums), test5_Expected]

-- Test case 6
#assert_same_evaluation #[(implementation test6_nums), test6_Expected]

-- Test case 7
#assert_same_evaluation #[(implementation test7_nums), test7_Expected]

-- Test case 8
#assert_same_evaluation #[(implementation test8_nums), test8_Expected]

-- Test case 9
#assert_same_evaluation #[(implementation test9_nums), test9_Expected]
end Assertions

section Pbt
method implementationPbt (nums : Array Int)
  return (result : Int)
  require precondition nums
  ensures postcondition nums result
  do
  return (implementation nums)

velvet_plausible_test implementationPbt (config := { maxMs := some 20000 })
end Pbt

section Proof
lemma nat_bitwise_xor_self (n : Nat) : Nat.bitwise xor n n = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp [Nat.testBit_bitwise]


lemma nat_bitwise_bne_self (n : Nat) : Nat.bitwise (fun x y => x != y) n n = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp [Nat.testBit_bitwise]


lemma intBitwise_xor_self (a : Int) : intBitwise xor a a = 0 := by
  cases a with
  | ofNat n =>
      -- natBitwise xor n n
      simp [intBitwise, natBitwise, nat_bitwise_xor_self]
  | negSucc n =>
      simp [intBitwise, natBitwise, nat_bitwise_bne_self]



theorem correctness_goal_0_0
    (nums : Array ℤ)
    (hsize : nums.size > 0)
    (s : ℤ)
    (hs_mem : s ∈ nums)
    (hs_once : occursOnce nums s)
    (hs_twice : ∀ y ∈ nums, y ≠ s → occursTwice nums y)
    (huniq_once : ∀ y ∈ nums, occursOnce nums y → y = s)
    (hpre : precondition nums)
    : postcondition nums (implementation nums) := by
    sorry

theorem correctness_goal_0
    (nums : Array ℤ)
    (hsize : nums.size > 0)
    (s : ℤ)
    (hs_mem : s ∈ nums)
    (hs_once : occursOnce nums s)
    (hs_twice : ∀ y ∈ nums, y ≠ s → occursTwice nums y)
    (huniq_once : ∀ y ∈ nums, occursOnce nums y → y = s)
    : implementation nums = s := by
  classical
  have hpre : precondition nums := by
    refine ⟨hsize, ?_⟩
    refine ⟨s, hs_mem, hs_once, ?_⟩
    intro y hy hne
    exact hs_twice y hy hne

  have hpost : postcondition nums (implementation nums) := by
    -- main functional correctness of the xor-fold implementation
    expose_names; exact (correctness_goal_0_0 nums hsize s hs_mem hs_once hs_twice huniq_once hpre)

  -- use the postcondition uniqueness with y = s
  have hs_eq : s = implementation nums := by
    exact (hpost.2.2 s hs_mem hs_once)

  simpa [hs_eq] using hs_eq.symm

theorem correctness_goal
    (nums : Array Int)
    (h_precond : precondition nums)
    : postcondition nums (implementation nums) := by
  rcases h_precond with ⟨hsize, ⟨s, hs_mem, hs_once, hs_twice⟩⟩

  have huniq_once : ∀ y : Int, y ∈ nums → occursOnce nums y → y = s := by
    intro y hyMem hyOnce
    by_contra hne
    have hyTwice : occursTwice nums y := hs_twice y hyMem hne
    have h1 : nums.count y = 1 := by simpa [occursOnce] using hyOnce
    have h2 : nums.count y = 2 := by simpa [occursTwice] using hyTwice
    have h12 : (1 : Nat) = 2 := by exact h1.symm.trans h2
    exact (by decide : (1 : Nat) ≠ 2) h12

  have himpl_eq : implementation nums = s := by
    expose_names; exact (correctness_goal_0 nums hsize s hs_mem hs_once hs_twice huniq_once)

  refine And.intro ?_ (And.intro ?_ ?_)
  · simpa [himpl_eq] using hs_mem
  · simpa [occursOnce, himpl_eq] using hs_once
  · intro y hyMem hyOnce
    have : y = s := huniq_once y hyMem hyOnce
    simpa [himpl_eq, this]
end Proof
