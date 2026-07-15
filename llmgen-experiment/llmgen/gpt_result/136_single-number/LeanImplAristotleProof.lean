import Lean

import Mathlib.Tactic

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

section XorProperties

-- Abbreviation for the XOR operation used in implementation
abbrev ixor (a b : Int) : Int := intBitwise xor a b

-- Key: xor on Bool equals bne
lemma xor_eq_bne : ∀ a b : Bool, xor a b = bne a b := by decide

/-
PROBLEM
natBitwise xor relates to Nat.xor

PROVIDED SOLUTION
Since xor = bne on Bool (by decide on all 4 cases), natBitwise xor m n = natBitwise bne m n. Unfold natBitwise: since bne false false = false, we get Int.ofNat (Nat.bitwise bne m n) = Int.ofNat (m ^^^ n) by rfl (since Nat.xor = Nat.bitwise bne).
-/
lemma natBitwise_xor (m n : Nat) : natBitwise xor m n = Int.ofNat (m ^^^ n) := by
  unfold natBitwise; aesop

/-
PROBLEM
Self-cancellation: a xor a = 0

PROVIDED SOLUTION
Cases on a: (1) ofNat m: ixor = natBitwise xor m m = Int.ofNat (m ^^^ m) by natBitwise_xor = Int.ofNat 0 by Nat.xor_self = 0. (2) negSucc m: ixor = natBitwise (fun x y => xor (!x) (!y)) m m. We have (fun x y => xor (!x) (!y)) false false = xor true true = false, so else branch gives Int.ofNat (Nat.bitwise (fun x y => xor (!x) (!y)) m m). Now xor (!x) (!y) = bne (!x) (!y). For all cases: bne (!x) (!y) = bne x y. So Nat.bitwise (fun x y => xor (!x) (!y)) m m = Nat.bitwise bne m m = m ^^^ m = 0. So result is Int.ofNat 0 = 0.
-/
lemma ixor_self (a : Int) : ixor a a = 0 := by
  -- By definition of `intBitwise`, we know that `intBitwise xor a a = 0`.
  have h_xor_self : ∀ a : Int, intBitwise xor a a = 0 := by
    unfold intBitwise;
    intro a; cases a <;> simp +decide [ natBitwise_xor ] ;
  exact h_xor_self a

/-
PROBLEM
Left identity: 0 xor a = a

PROVIDED SOLUTION
Cases on a: (1) ofNat m: ixor 0 (ofNat m) = natBitwise xor 0 m = Int.ofNat (0 ^^^ m) = Int.ofNat m. (2) negSucc m: ixor 0 (negSucc m) = natBitwise (fun x y => xor x (!y)) 0 m. (fun x y => xor x (!y)) false false = xor false true = true. So if-branch: Int.negSucc (Nat.bitwise (fun x y => !(xor x (!y))) 0 m). !(xor x (!y)) for all cases = !(bne x (!y)). For x=false, y=false: !(bne false true)=!(true)=false. x=false,y=true: !(bne false false)=!(false)=true. x=true,y=false: !(bne true true)=!(false)=true. x=true,y=true: !(bne true false)=!(true)=false. So (fun x y => !(xor x (!y))) = (fun x y => (x == y)) = (fun x y => !(bne x y)). Nat.bitwise of this applied to 0 and m: since first arg is 0, Nat.bitwise (fun x y => !(bne x y)) 0 m = m (because for 0 and m, it picks bits of m and applies f false bit, and f false b = !(!b) = b... actually this needs more care). Just use simp/omega/decide on the Nat.bitwise definition.
-/
lemma ixor_zero_left (a : Int) : ixor 0 a = a := by
  unfold ixor;
  unfold intBitwise;
  cases a <;> norm_num [ natBitwise ];
  · exact Nat.zero_xor _;
  · exact Nat.eq_of_testBit_eq fun i => by simp +decide [ Nat.testBit_bitwise ] ;

/-
PROBLEM
Right identity: a xor 0 = a

PROVIDED SOLUTION
Cases on a: (1) ofNat m: ixor (ofNat m) 0 = natBitwise xor m 0 = Int.ofNat (m ^^^ 0) = Int.ofNat m by Nat.xor_zero. (2) negSucc m: ixor (negSucc m) 0 = natBitwise (fun x y => xor (!x) y) m 0. Use decide-level case analysis and Nat.bitwise properties.
-/
lemma ixor_zero_right (a : Int) : ixor a 0 = a := by
  cases a;
  · unfold ixor; simp +decide [ intBitwise ] ;
    rw [ natBitwise_xor ] ; aesop;
  · unfold ixor;
    unfold intBitwise;
    unfold natBitwise;
    simp +zetaDelta at *;
    exact Nat.eq_of_testBit_eq fun i => by simp +decide [ Nat.testBit_bitwise ] ;

/-
PROBLEM
Commutativity

PROVIDED SOLUTION
Cases on a and b (4 cases: ofNat/ofNat, ofNat/negSucc, negSucc/ofNat, negSucc/negSucc). In each case, unfold intBitwise and natBitwise, use Nat.xor_comm (or Nat.bitwise_comm) and the fact that the Bool function arguments are related by swapping. For ofNat m, ofNat n: both give natBitwise xor m n and natBitwise xor n m, use Nat.xor_comm. For ofNat m, negSucc n vs negSucc n, ofNat m: the functions (fun x y => xor x (!y)) and (fun x y => xor (!x) y) are related by argument swap, and Nat.bitwise_comm handles this.
-/
lemma ixor_comm (a b : Int) : ixor a b = ixor b a := by
  -- Apply the commutativity of Nat.xor to each case.
  have h_comm : ∀ m n : Nat, Nat.bitwise xor m n = Nat.bitwise xor n m := by
    apply Nat.xor_comm;
  unfold ixor;
  unfold intBitwise;
  unfold natBitwise; aesop;

/-
PROBLEM
Associativity

PROVIDED SOLUTION
This is the hardest algebraic property. Cases on a, b, c (8 cases). In each case, unfold intBitwise and natBitwise. The inner Nat.bitwise calls compose. Use Nat.xor_assoc and properties of Nat.bitwise. Key observation: natBitwise with various Bool functions composes correctly because XOR is associative at the bit level. May need to show that composing the Bool-level functions through the intBitwise/natBitwise machinery preserves associativity. Try using simp with intBitwise, natBitwise, and then reducing to Nat.xor_assoc.
-/
lemma ixor_assoc (a b c : Int) : ixor (ixor a b) c = ixor a (ixor b c) := by
  unfold ixor;
  unfold intBitwise;
  cases a <;> cases b <;> cases c <;> simp +decide [ * ];
  all_goals unfold natBitwise; simp +decide [ Nat.xor ] ;
  all_goals apply Nat.xor_assoc;

-- RightCommutative for foldl
instance : RightCommutative (fun (acc : Int) (x : Int) => ixor acc x) where
  right_comm a b c := by
    show ixor (ixor a b) c = ixor (ixor a c) b
    rw [ixor_assoc, ixor_assoc, ixor_comm b c]

end XorProperties

section FoldXorLemma

/-
PROBLEM
The main combinatorial lemma: folding XOR over a list with the given count
properties returns the unique element.
We prove this on lists, then lift to arrays.

PROVIDED SOLUTION
Proof by strong induction on l.length.

Base: if l.length = 1, since s has count 1 in l, l = [s]. Then foldl gives ixor 0 s = s by ixor_zero_left.

Step: if l.length > 1, there exists y ∈ l with y ≠ s (since s appears once but list has more than 1 element). By hs_other, l.count y = 2. Use List.perm_cons_erase to get l ~ y :: l.erase y, and then (l.erase y).count y = 1, so use perm_cons_erase again to get l.erase y ~ y :: (l.erase y).erase y. Let l' = (l.erase y).erase y. Then l ~ y :: y :: l'. By List.Perm.foldl_eq (with RightCommutative), foldl on l equals foldl on (y :: y :: l') = foldl starting with ixor (ixor 0 y) y = ixor 0 0 = 0 (using ixor_self and ixor_zero_left). Wait: ixor (ixor 0 y) y = ixor y y = 0 by ixor_zero_left then ixor_self. So we get foldl on l' starting with 0.

Now l' has: count s = 1 (since y ≠ s, erasing y doesn't affect s's count), and for all z ∈ l', z ≠ s → count z = 2 (erasing two copies of y removes y entirely, other counts unchanged). Also l'.length < l.length. By IH, foldl on l' = s.

Key lemmas: List.perm_cons_erase, List.Perm.foldl_eq, List.count_erase_of_ne, List.count_erase_self, ixor_self, ixor_zero_left, ixor_zero_right.
-/
lemma list_foldl_ixor_unique (l : List Int) (s : Int)
    (hs_count : l.count s = 1)
    (hs_other : ∀ y, y ∈ l → y ≠ s → l.count y = 2) :
    l.foldl (fun acc x => ixor acc x) 0 = s := by
      -- By definition of `List.Perm.foldl_eq`
      have h_perm : List.Perm l (List.replicate (List.count s l) s ++ List.flatMap (fun y => List.replicate (List.count y l) y) (List.toFinset l |> Finset.filter (fun y => y ≠ s)).toList) := by
        rw [ List.perm_iff_count ];
        intro y; by_cases hy : y = s <;> simp_all +decide [ List.count_replicate, List.count_flatMap ] ;
        by_cases hy' : y ∈ l <;> simp_all +decide [ List.count_cons, List.count_flatMap ];
        · rw [ Finset.sum_eq_single y ] <;> aesop;
        · simp_all +decide [ List.count_eq_zero_of_not_mem, eq_comm ];
          exact Eq.symm ( Finset.sum_eq_zero fun x hx => by rw [ List.count_replicate ] ; aesop );
      have h_perm_foldl : List.foldl (fun acc x => ixor acc x) 0 (List.replicate (List.count s l) s ++ List.flatMap (fun y => List.replicate (List.count y l) y) (List.toFinset l |> Finset.filter (fun y => y ≠ s)).toList) = s := by
        simp_all +decide [ixor_comm, ixor_assoc];
        -- By definition of `List.flatMap`, we can rewrite the list as a list of pairs of elements.
        have h_flatMap : ∀ {l : List ℤ}, List.foldl (fun acc x => ixor acc x) (ixor s 0) (List.flatMap (fun y => List.replicate 2 y) l) = s := by
          intros l; induction' l using List.reverseRecOn with l ih <;> simp_all +decide [ List.flatMap ] ;
          · exact?;
          · rw [ ixor_assoc, ixor_self, ixor_zero_right ];
        convert h_flatMap using 2;
        rw [ List.flatMap_congr ];
        aesop;
      rw [ ← h_perm_foldl, h_perm.foldl_eq ]

end FoldXorLemma

section Proof

/-
PROBLEM
Bridge between Array and List operations

PROVIDED SOLUTION
Array.count is defined in terms of the underlying list. Unfold definitions or use simp with Array lemmas.
-/
lemma array_count_eq_list_count (nums : Array Int) (x : Int) :
    nums.count x = nums.toList.count x := by
      induction nums using Array.recOn ; aesop

/-
PROVIDED SOLUTION
Array membership is defined via the underlying list. Use Array.mem_def or simp.
-/
lemma array_mem_iff_list_mem (nums : Array Int) (x : Int) :
    x ∈ nums ↔ x ∈ nums.toList := by
      grind

/-
PROVIDED SOLUTION
Array.foldl is defined in terms of the underlying list's foldl. Use Array.foldl_toList or similar.
-/
lemma array_foldl_eq_list_foldl (nums : Array Int) :
    nums.foldl (fun acc x => ixor acc x) 0 = nums.toList.foldl (fun acc x => ixor acc x) 0 := by
      grind

theorem correctness_goal_0_0 (nums : Array ℤ) (hsize : nums.size > 0) (s : ℤ) (hs_mem : s ∈ nums) (hs_once : occursOnce nums s) (hs_twice : ∀ y ∈ nums, y ≠ s → occursTwice nums y) (huniq_once : ∀ y ∈ nums, occursOnce nums y → y = s) (hpre : precondition nums) : postcondition nums (implementation nums) := by
    unfold postcondition implementation
    -- Convert array operations to list operations
    have hlist_count_s : nums.toList.count s = 1 := by
      rw [← array_count_eq_list_count]; exact hs_once
    have hlist_other : ∀ y, y ∈ nums.toList → y ≠ s → nums.toList.count y = 2 := by
      intro y hy hne
      rw [← array_count_eq_list_count]
      exact hs_twice y ((array_mem_iff_list_mem nums y).mpr hy) hne
    have hfold : nums.foldl (fun acc x => intBitwise xor acc x) 0 = s := by
      rw [show (fun acc x => intBitwise xor acc x) = (fun acc x => ixor acc x) from rfl]
      rw [array_foldl_eq_list_foldl]
      exact list_foldl_ixor_unique nums.toList s hlist_count_s hlist_other
    rw [hfold]
    exact ⟨hs_mem, hs_once, huniq_once⟩
end Proof