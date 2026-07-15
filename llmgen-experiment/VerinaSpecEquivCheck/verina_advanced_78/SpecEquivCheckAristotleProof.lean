/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: dc13aff3-9270-414f-a306-caedf3963445

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (nums : List Int) (target : Int) : VerinaSpec.twoSum_precond nums target ↔ LLMSpec.precondition nums target

- theorem postcondition_equiv (nums : List Int) (target : Int) (result : Prod Nat Nat) : LLMSpec.precondition nums target →
  (VerinaSpec.twoSum_postcond nums target result ↔ LLMSpec.postcondition nums target result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def twoSum_precond (nums : List Int) (target : Int) : Prop :=
  let pairwiseSum := List.range nums.length |>.flatMap (fun i =>
    nums.drop (i + 1) |>.map (fun y => nums[i]! + y))
  nums.length > 1 ∧ pairwiseSum.count target = 1

def findComplement (nums : List Int) (target : Int) (i : Nat) (x : Int) : Option Nat :=
  let rec aux (nums : List Int) (j : Nat) : Option Nat :=
    match nums with
    | []      => none
    | y :: ys => if x + y = target then some (i + j + 1) else aux ys (j + 1)
  aux nums 0

def twoSumAux (nums : List Int) (target : Int) (i : Nat) : Prod Nat Nat :=
  match nums with
  | []      => panic! "No solution exists"
  | x :: xs =>
    match findComplement xs target i x with
    | some j => (i, j)
    | none   => twoSumAux xs target (i + 1)

def twoSum_postcond (nums : List Int) (target : Int) (result: Prod Nat Nat) : Prop :=
  let i := result.fst;
  let j := result.snd;
  (i < j) ∧
  (i < nums.length) ∧ (j < nums.length) ∧
  (nums[i]!) + (nums[j]!) = target

end VerinaSpec

namespace LLMSpec

-- (i,j) is a valid TwoSum witness for (nums,target) when it is ordered, in-bounds, and sums to target.
-- Note: `j < nums.length` together with `i < j` implies `i < nums.length`, so we do not repeat it.
def IsTwoSumWitness (nums : List Int) (target : Int) (i : Nat) (j : Nat) : Prop :=
  i < j ∧ j < nums.length ∧ nums[i]! + nums[j]! = target

-- There exists exactly one witness pair with i<j.
def HasUniqueTwoSum (nums : List Int) (target : Int) : Prop :=
  (∃ i : Nat, ∃ j : Nat, IsTwoSumWitness nums target i j) ∧
  (∀ i1 : Nat, ∀ j1 : Nat, ∀ i2 : Nat, ∀ j2 : Nat,
    IsTwoSumWitness nums target i1 j1 →
    IsTwoSumWitness nums target i2 j2 →
    (i1 = i2 ∧ j1 = j2))

-- Preconditions:
-- 1) The input admits exactly one solution pair (i,j) with i<j.
def precondition (nums : List Int) (target : Int) : Prop :=
  HasUniqueTwoSum nums target

-- Postcondition:
-- 1) The returned pair is a valid witness.
-- 2) Any other valid witness must have the same indices (so the returned pair is the unique solution).
def postcondition (nums : List Int) (target : Int) (result : Prod Nat Nat) : Prop :=
  IsTwoSumWitness nums target result.1 result.2 ∧
  (∀ i : Nat, ∀ j : Nat,
    IsTwoSumWitness nums target i j → (i = result.1 ∧ j = result.2))

end LLMSpec

section Proof

theorem precondition_equiv (nums : List Int) (target : Int) : VerinaSpec.twoSum_precond nums target ↔ LLMSpec.precondition nums target := by
  constructor <;> intro h <;> rcases h with ⟨ h₁, h₂ ⟩;
  · constructor <;> norm_num at *;
    · -- Let's choose any index $i$ such that $i < j$ and $nums[i]! + nums[j]! = target$.
      obtain ⟨i, hi⟩ : ∃ i ∈ List.range nums.length, ∃ j ∈ List.drop (i + 1) (List.range nums.length), nums[i]! + nums[j]! = target := by
        contrapose! h₂;
        rw [ List.count_eq_zero_of_not_mem ] <;> simp_all +decide [ List.mem_flatMap ];
        intro x hx; specialize h₂ x hx; simp_all +decide [ List.mem_iff_get ] ;
        convert h₂ using 1;
        grind +ring;
      obtain ⟨ hi₁, j, hj₁, hj₂ ⟩ := hi;
      -- Since $j$ is in the drop of the range after $i+1$, it follows that $j > i$.
      have hj_gt_i : j > i := by
        rw [ List.mem_iff_get ] at hj₁;
        grind;
      exact ⟨ i, j, hj_gt_i, by simpa using List.mem_range.mp ( List.mem_of_mem_drop hj₁ ), hj₂ ⟩;
    · intro i1 j1 i2 j2 hi hj
      have h_count : List.count target (List.flatMap (fun (i : ℕ) => List.drop (i + 1) (List.map (fun (y : ℤ) => nums[i]?.getD 0 + y) nums)) (List.range nums.length)) = Finset.card (Finset.filter (fun (p : ℕ × ℕ) => p.1 < p.2 ∧ nums[p.1]?.getD 0 + nums[p.2]?.getD 0 = target) (Finset.product (Finset.range nums.length) (Finset.range nums.length))) := by
        have h_count : List.count target (List.flatMap (fun (i : ℕ) => List.drop (i + 1) (List.map (fun (y : ℤ) => nums[i]?.getD 0 + y) nums)) (List.range nums.length)) = Finset.sum (Finset.range nums.length) (fun i => Finset.sum (Finset.Ico (i + 1) nums.length) (fun j => if nums[i]?.getD 0 + nums[j]?.getD 0 = target then 1 else 0)) := by
          have h_count : ∀ i ∈ List.range nums.length, List.count target (List.drop (i + 1) (List.map (fun (y : ℤ) => nums[i]?.getD 0 + y) nums)) = Finset.sum (Finset.Ico (i + 1) nums.length) (fun j => if nums[i]?.getD 0 + nums[j]?.getD 0 = target then 1 else 0) := by
            intros i hi
            have h_count : List.count target (List.drop (i + 1) (List.map (fun (y : ℤ) => nums[i]?.getD 0 + y) nums)) = Finset.sum (Finset.range (nums.length - (i + 1))) (fun j => if nums[i]?.getD 0 + nums[(i + 1 + j)]?.getD 0 = target then 1 else 0) := by
              have h_count : ∀ (l : List ℤ), List.count target l = Finset.sum (Finset.range l.length) (fun j => if l[j]?.getD 0 = target then 1 else 0) := by
                intro l; induction l <;> simp +decide [ *, Finset.sum_range_succ' ] ;
                rw [ Finset.card_filter ];
                rw [ Finset.sum_range_succ' ] ; aesop;
              convert h_count _ using 2 ; simp +decide [ add_comm, add_left_comm, add_assoc ];
              grind +ring;
            rw [ h_count, Finset.sum_Ico_eq_sum_range ];
          rw [ ← Finset.sum_congr rfl h_count ];
          induction' nums.length with n ih <;> simp_all +decide [ Finset.sum_range_succ, List.range_succ ];
        erw [ h_count, Finset.card_filter ];
        erw [ Finset.sum_product ] ; simp +decide [ Finset.sum_ite ] ;
        congr! 2 with x ; aesop;
      have h_unique : ∀ p1 p2 : ℕ × ℕ, p1 ∈ Finset.filter (fun (p : ℕ × ℕ) => p.1 < p.2 ∧ nums[p.1]?.getD 0 + nums[p.2]?.getD 0 = target) (Finset.product (Finset.range nums.length) (Finset.range nums.length)) → p2 ∈ Finset.filter (fun (p : ℕ × ℕ) => p.1 < p.2 ∧ nums[p.1]?.getD 0 + nums[p.2]?.getD 0 = target) (Finset.product (Finset.range nums.length) (Finset.range nums.length)) → p1 = p2 := by
        exact Finset.card_eq_one.mp ( h_count.symm.trans h₂ ) |> fun ⟨ p, hp ⟩ => by aesop;
      specialize h_unique ( i1, j1 ) ( i2, j2 ) ; simp_all +decide [ LLMSpec.IsTwoSumWitness ] ;
      exact h_unique ( by linarith ) ( by simpa [ List.getElem?_eq_getElem ( by linarith : i1 < nums.length ), List.getElem?_eq_getElem ( by linarith : j1 < nums.length ) ] using hi.2.2 ) ( by linarith ) ( by simpa [ List.getElem?_eq_getElem ( by linarith : i2 < nums.length ), List.getElem?_eq_getElem ( by linarith : j2 < nums.length ) ] using hj.2.2 );
  · -- By definition of `IsTwoSumWitness`, we know that `i < j` and `nums[i]! + nums[j]! = target`.
    obtain ⟨i, j, hij⟩ : ∃ i j, LLMSpec.IsTwoSumWitness nums target i j := h₁
    have h_count : List.count target (List.flatMap (fun i => List.map (fun y => nums[i]! + y) (List.drop (i + 1) nums)) (List.range nums.length)) ≥ 1 := by
      have h_count : target ∈ List.flatMap (fun i => List.map (fun y => nums[i]! + y) (List.drop (i + 1) nums)) (List.range nums.length) := by
        rcases hij with ⟨ hij₁, hij₂, hij₃ ⟩ ; simp_all +decide [ List.mem_flatMap ] ;
        use i; simp_all +decide [ List.mem_iff_get ] ; (
        exact ⟨ by linarith, ⟨ ⟨ j - ( i + 1 ), by rw [ List.length_drop ] ; norm_num; omega ⟩, by simpa [ add_assoc, Nat.add_sub_of_le ( by linarith : i + 1 ≤ j ) ] using hij₃ ⟩ ⟩);
      exact List.count_pos_iff.mpr h_count;
    -- Since there is exactly one witness pair, the count of the target in the pairwise sums is exactly 1.
    have h_count_eq_one : List.count target (List.flatMap (fun i => List.map (fun y => nums[i]! + y) (List.drop (i + 1) nums)) (List.range nums.length)) = Finset.card (Finset.filter (fun p => nums[p.1]! + nums[p.2]! = target) (Finset.filter (fun p => p.1 < p.2) (Finset.product (Finset.range nums.length) (Finset.range nums.length)))) := by
      have h_count_eq_one : ∀ i ∈ List.range nums.length, List.count target (List.map (fun y => nums[i]! + y) (List.drop (i + 1) nums)) = Finset.card (Finset.filter (fun j => nums[i]! + nums[j]! = target) (Finset.Ico (i + 1) nums.length)) := by
        intros i hi
        have h_count_eq_one : List.count target (List.map (fun y => nums[i]! + y) (List.drop (i + 1) nums)) = Finset.card (Finset.filter (fun j => nums[i]! + nums[j]! = target) (Finset.Ico (i + 1) nums.length)) := by
          have h_count_eq_one : List.count target (List.map (fun y => nums[i]! + y) (List.drop (i + 1) nums)) = List.countP (fun y => nums[i]! + y = target) (List.drop (i + 1) nums) := by
            rw [ List.count ];
            rw [ List.countP_map ] ; aesop
          rw [ h_count_eq_one, List.countP_eq_length_filter ];
          rw [ Finset.card_filter ];
          rw [ Finset.sum_Ico_eq_sum_range ];
          rw [ show List.drop ( i + 1 ) nums = List.map ( fun k => nums[i + 1 + k]! ) ( List.range ( nums.length - ( i + 1 ) ) ) from ?_, List.filter_map ] ; aesop;
          refine' List.ext_get _ _ <;> simp +decide [ List.get ];
          exact fun n hn => by rw [ List.getElem?_eq_getElem ( by omega ) ] ; rfl;
        exact h_count_eq_one;
      have h_count_eq_one : List.count target (List.flatMap (fun i => List.map (fun y => nums[i]! + y) (List.drop (i + 1) nums)) (List.range nums.length)) = Finset.sum (Finset.range nums.length) (fun i => Finset.card (Finset.filter (fun j => nums[i]! + nums[j]! = target) (Finset.Ico (i + 1) nums.length))) := by
        rw [ ← Finset.sum_congr rfl h_count_eq_one ];
        induction' nums.length with n ih <;> simp +decide [ Finset.sum_range_succ, List.range_succ ] at *;
        exact ih;
      -- The sum of the counts for each i is equal to the cardinality of the set of pairs because each pair (i, j) is counted exactly once in the sum.
      have h_sum_eq_card : Finset.sum (Finset.range nums.length) (fun i => Finset.card (Finset.filter (fun j => nums[i]! + nums[j]! = target) (Finset.Ico (i + 1) nums.length))) = Finset.card (Finset.filter (fun p => nums[p.1]! + nums[p.2]! = target) (Finset.filter (fun p => p.1 < p.2) (Finset.product (Finset.range nums.length) (Finset.range nums.length)))) := by
        rw [ show ( Finset.filter ( fun p => nums[p.1]! + nums[p.2]! = target ) ( Finset.filter ( fun p => p.1 < p.2 ) ( Finset.product ( Finset.range nums.length ) ( Finset.range nums.length ) ) ) ) = Finset.biUnion ( Finset.range nums.length ) ( fun i => Finset.image ( fun j => ( i, j ) ) ( Finset.filter ( fun j => nums[i]! + nums[j]! = target ) ( Finset.Ico ( i + 1 ) nums.length ) ) ) from ?_, Finset.card_biUnion ];
        · exact Finset.sum_congr rfl fun _ _ => by rw [ Finset.card_image_of_injective ] ; exact fun x y hxy => by injection hxy;
        · exact fun i hi j hj hij => Finset.disjoint_left.mpr fun x hx₁ hx₂ => hij <| by aesop;
        · ext ⟨i, j⟩; simp [Finset.mem_biUnion, Finset.mem_image];
          exact ⟨ fun h => ⟨ h.1.1.1, ⟨ by linarith, h.1.1.2 ⟩, h.2 ⟩, fun h => ⟨ ⟨ ⟨ h.1, h.2.1.2 ⟩, by linarith ⟩, h.2.2 ⟩ ⟩;
      rw [h_count_eq_one, h_sum_eq_card];
    refine' ⟨ _, _ ⟩;
    · contrapose! h_count; interval_cases _ : nums.length <;> simp_all +decide ;
    · rw [ h_count_eq_one, Finset.card_eq_one ];
      exact ⟨ ⟨ i, j ⟩, Finset.eq_singleton_iff_unique_mem.mpr ⟨ by
        -- By definition of IsTwoSumWitness, we know that i < j and nums[i]! + nums[j]! = target.
        obtain ⟨hij_lt, hij_sum⟩ := hij;
        exact Finset.mem_filter.mpr ⟨ Finset.mem_filter.mpr ⟨ Finset.mem_product.mpr ⟨ Finset.mem_range.mpr ( by linarith ), Finset.mem_range.mpr ( by linarith ) ⟩, hij_lt ⟩, hij_sum.2 ⟩, fun p hp => by
        simp +zetaDelta at *;
        exact Prod.ext ( h₂ _ _ _ _ ⟨ hp.1.2, hp.1.1.2, by simpa [ List.getElem?_eq_getElem, hp.1.1.1, hp.1.1.2 ] using hp.2 ⟩ hij |>.1 ) ( h₂ _ _ _ _ ⟨ hp.1.2, hp.1.1.2, by simpa [ List.getElem?_eq_getElem, hp.1.1.1, hp.1.1.2 ] using hp.2 ⟩ hij |>.2 ) ⟩ ⟩

theorem postcondition_equiv (nums : List Int) (target : Int) (result : Prod Nat Nat) : LLMSpec.precondition nums target →
  (VerinaSpec.twoSum_postcond nums target result ↔ LLMSpec.postcondition nums target result) := by
  intro h;
  -- By definition of `LLMSpec.precondition`, we know that there exists a unique pair (i, j) such that i < j, j < nums.length, and nums[i]! + nums[j]! = target.
  obtain ⟨i, j, hij, h_unique⟩ : ∃ i j, i < j ∧ j < nums.length ∧ nums[i]! + nums[j]! = target ∧ ∀ i' j', i' < j' → j' < nums.length → nums[i']! + nums[j']! = target → i' = i ∧ j' = j := by
    obtain ⟨ ⟨ i, j, hij, h_unique ⟩, h_unique' ⟩ := h;
    exact ⟨ i, j, hij, h_unique.1, h_unique.2, fun i' j' hij' hj' h => h_unique' i' j' i j ⟨ hij', hj', h ⟩ ⟨ hij, h_unique.1, h_unique.2 ⟩ ⟩;
  simp [VerinaSpec.twoSum_postcond, LLMSpec.postcondition, h_unique];
  -- By definition of `IsTwoSumWitness`, we know that if the result is a valid witness, then there exists a unique pair (i, j) such that i < j, j < nums.length, and nums[i]! + nums[j]! = target.
  simp [LLMSpec.IsTwoSumWitness];
  grind

end Proof