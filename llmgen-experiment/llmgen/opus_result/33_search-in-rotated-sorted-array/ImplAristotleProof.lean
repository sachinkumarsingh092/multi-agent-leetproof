/- type checks in Lean 4.28 -/

import Mathlib

-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false

/- Problem Description
    SearchInRotatedSortedArray: return the index of a target value in a possibly rotated strictly-increasing array, or -1 if absent.
    **Important: complexity should be O(log n) time and O(1) space**
    Natural language breakdown:
    1. Input is a finite sequence `nums` of integers with distinct values.
    2. There exists an underlying strictly increasing sequence `base` such that `nums` is a cyclic rotation of `base`.
    3. Input also contains an integer `target`.
    4. If `target` occurs in `nums`, the function returns the (0-based) index where it occurs.
    5. Because values are distinct, this index is unique.
    6. If `target` does not occur in `nums`, the function returns -1.
    7. The returned index is always either -1 or a valid index within `nums`.
-/

section Specs
def isStrictSorted (nums : List Int) : Prop :=
  nums.Pairwise (· < ·)

def isRotationOfStrictSorted (nums : List Int) : Prop :=
  ∃ base : List Int,
    isStrictSorted base ∧ base.Nodup ∧ base.IsRotated nums

def inList (nums : List Int) (x : Int) : Prop :=
  x ∈ nums

def precondition (nums : List Int) (target : Int) : Prop :=
  nums.length > 0 ∧
  nums.Nodup ∧
  isRotationOfStrictSorted nums

def postcondition (nums : List Int) (target : Int) (result : Int) : Prop :=
  (result = (-1) ∧ ¬ inList nums target) ∨
  (∃ i : Nat,
    i < nums.length ∧
    nums[i]? = some target ∧
    result = Int.ofNat i ∧
    (∀ j : Nat, j < nums.length → nums[j]? = some target → j = i))
end Specs

section TestCases
def test1_nums : List Int := [4, 5, 6, 7, 0, 1, 2]
def test1_target : Int := 0
def test1_Expected : Int := 4
def test2_nums : List Int := [4, 5, 6, 7, 0, 1, 2]
def test2_target : Int := 3
def test2_Expected : Int := (-1)
def test3_nums : List Int := [1]
def test3_target : Int := 0
def test3_Expected : Int := (-1)
def test4_nums : List Int := [1]
def test4_target : Int := 1
def test4_Expected : Int := 0
def test5_nums : List Int := [0, 1, 2, 3, 4]
def test5_target : Int := 3
def test5_Expected : Int := 3
def test6_nums : List Int := [5, 1, 2, 3, 4]
def test6_target : Int := 5
def test6_Expected : Int := 0
def test7_nums : List Int := [3, 4, 5, 1, 2]
def test7_target : Int := 2
def test7_Expected : Int := 4
def test8_nums : List Int := [0, 1, (-3), (-2), (-1)]
def test8_target : Int := (-2)
def test8_Expected : Int := 3
def test9_nums : List Int := [10, 20, 30, 40, 50]
def test9_target : Int := 35
def test9_Expected : Int := (-1)
end TestCases

section HelperLemmas

-- COMMENTED OUT: Original lemma is FALSE.
-- Counterexample: x=0, y=2, n=2 gives 0%2=0 ≤ 0=2%2 but 0/2=0 ≠ 1=2/2.
-- lemma div_eq_of_mod_le_of_le (x y n : ℕ) (hn : 0 < n) (hxy : x ≤ y)
--   (hmod : x % n ≤ y % n) : x / n = y / n

lemma getElem?_getD_of_lt {α : Type*} {l : List α} {i : ℕ} {d : α} (h : i < l.length) :
    l[i]?.getD d = l[i] := by
  rw [List.getElem?_eq_getElem h, Option.getD_some]

lemma getD_of_getElem?_eq_some {α : Type*} {l : List α} {i : ℕ} {v d : α}
    (h : l[i]? = some v) : l[i]?.getD d = v := by
  simp [h]

/-
PROBLEM
Key: in a rotated sorted array, if l[a] ≤ l[b] with a ≤ b < l.length,
then for a ≤ c ≤ b (c < l.length), l[a] ≤ l[c] ≤ l[b].

PROVIDED SOLUTION
Proof outline:
1. Obtain base, k such that base.rotate k = l (from List.IsRotated and List.isRotated_iff_mod).
2. By List.getElem_rotate, l[j] = base[(j + k) % base.length] for j < l.length. Note base.length = l.length (rotation preserves length).
3. Let n = l.length. Since base is Pairwise (<), base[i] ≤ base[j] ↔ i ≤ j for i,j < n.
4. hval gives l[a] ≤ l[b], i.e., base[(a+k)%n] ≤ base[(b+k)%n], so (a+k)%n ≤ (b+k)%n.
5. Since a ≤ b < n, we have a+k ≤ b+k and (b+k)-(a+k) = b-a < n.
6. Key claim: since a+k ≤ b+k, (b+k)-(a+k) < n, and (a+k)%n ≤ (b+k)%n, we have (a+k)/n = (b+k)/n. Proof: by contradiction, if (a+k)/n < (b+k)/n, then there's a multiple of n between a+k and b+k. But (b+k) - (a+k) < n means at most one multiple, at position m*n with a+k < m*n ≤ b+k. Then (b+k)%n = b+k - m*n and (a+k)%n = a+k - (m-1)*n. Then (b+k)%n - (a+k)%n = (b-a) - n < 0, contradicting (a+k)%n ≤ (b+k)%n.
7. Let q = (a+k)/n = (b+k)/n. Then (j+k)%n = j+k - q*n for a ≤ j ≤ b (since a+k ≤ j+k ≤ b+k and all are in [q*n, (q+1)*n)).
8. For c with a ≤ c ≤ b: (c+k)%n = c+k - q*n. Since a+k-q*n ≤ c+k-q*n ≤ b+k-q*n, we have (a+k)%n ≤ (c+k)%n ≤ (b+k)%n.
9. Using base strictly sorted: base[(a+k)%n] ≤ base[(c+k)%n] ≤ base[(b+k)%n], i.e., l[a] ≤ l[c] ≤ l[b].
-/
lemma rotated_sorted_mono (l : List ℤ)
    (hrot : ∃ base, List.Pairwise (· < ·) base ∧ base.Nodup ∧ base ~r l)
    {a b c : ℕ} (ha : a < l.length) (hb : b < l.length) (hc : c < l.length)
    (hab : a ≤ b) (hac : a ≤ c) (hcb : c ≤ b)
    (hval : l[a] ≤ l[b]) : l[a] ≤ l[c] ∧ l[c] ≤ l[b] := by
  -- By definition of rotation, there exists some $k$ such that $l = \text{rotate}(base, k)$ where $base$ is strictly sorted.
  obtain ⟨base, hbase_sorted, hbase_nodup, hbase_rotate⟩ := hrot
  obtain ⟨k, hk⟩ : ∃ k, l = base.rotate k := by
    cases hbase_rotate ; aesop;
  -- By the properties of the rotation and the strict monotonicity of the base, we can derive the inequalities for the rotated indices.
  have h_rotated_indices : (a + k) % base.length ≤ (b + k) % base.length ∧ (a + k) % base.length ≤ (c + k) % base.length ∧ (c + k) % base.length ≤ (b + k) % base.length := by
    have h_rotated_indices : (a + k) % base.length ≤ (b + k) % base.length := by
      have h_mod_le : ∀ i j : ℕ, i < base.length → j < base.length → i ≤ j → base[i]! ≤ base[j]! := by
        -- Since the base list is strictly sorted, for any i < j, base[i] < base[j]. Therefore, if i ≤ j, then base[i] ≤ base[j].
        have h_sorted : ∀ i j : ℕ, i < base.length → j < base.length → i < j → base[i]! < base[j]! := by
          rw [ List.pairwise_iff_get ] at hbase_sorted;
          exact fun i j hi hj hij => by simpa [ List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj ] using hbase_sorted ⟨ i, hi ⟩ ⟨ j, hj ⟩ hij;
        generalize_proofs at *; (
        exact fun i j hi hj hij => if hij' : i = j then hij'.symm ▸ le_rfl else le_of_lt ( h_sorted i j hi hj ( lt_of_le_of_ne hij hij' ) ) ;)
      generalize_proofs at *; (
      contrapose! hval; simp_all +decide [ List.getElem_rotate ] ;
      refine' lt_of_le_of_ne ( h_mod_le _ _ _ _ hval.le ) _;
      intro H; have := List.nodup_iff_injective_get.mp hbase_nodup; have := @this ⟨ ( b + k ) % base.length, Nat.mod_lt _ ( by linarith ) ⟩ ⟨ ( a + k ) % base.length, Nat.mod_lt _ ( by linarith ) ⟩ ; aesop;);
    have h_rotated_indices : (a + k) / base.length = (b + k) / base.length := by
      have h_div_eq : (b + k) - (a + k) < base.length := by
        rw [ show base.length = l.length from ?_ ] ; omega;
        rw [ hk, List.length_rotate ];
      contrapose! h_div_eq;
      cases lt_or_gt_of_ne h_div_eq <;> simp_all +decide [ Nat.div_eq_of_lt ];
      · exact Nat.le_sub_of_add_le ( by nlinarith [ Nat.div_mul_le_self ( a + k ) base.length, Nat.div_mul_le_self ( b + k ) base.length, Nat.mod_add_div ( a + k ) base.length, Nat.mod_add_div ( b + k ) base.length, Nat.mod_lt ( a + k ) ( show 0 < base.length from List.length_pos_iff.mpr ( by aesop_cat ) ), Nat.mod_lt ( b + k ) ( show 0 < base.length from List.length_pos_iff.mpr ( by aesop_cat ) ) ] );
      · exact absurd ‹_› ( not_lt_of_ge ( Nat.div_le_div_right ( by linarith ) ) );
    have h_rotated_indices : (a + k) / base.length = (c + k) / base.length := by
      have h_rotated_indices : (a + k) / base.length ≤ (c + k) / base.length ∧ (c + k) / base.length ≤ (b + k) / base.length := by
        exact ⟨ Nat.div_le_div_right ( by linarith ), Nat.div_le_div_right ( by linarith ) ⟩;
      grind;
    have h_rotated_indices : (a + k) = (a + k) / base.length * base.length + (a + k) % base.length ∧ (b + k) = (b + k) / base.length * base.length + (b + k) % base.length ∧ (c + k) = (c + k) / base.length * base.length + (c + k) % base.length := by
      exact ⟨ by rw [ Nat.div_add_mod' ], by rw [ Nat.div_add_mod' ], by rw [ Nat.div_add_mod' ] ⟩;
    grind;
  have h_base_ineq : ∀ i j : ℕ, i < base.length → j < base.length → i ≤ j → base[i]! ≤ base[j]! := by
    intros i j hi hj hij; exact (by
    have := List.pairwise_iff_get.mp hbase_sorted;
    cases lt_or_eq_of_le hij <;> [ exact le_of_lt ( by simpa [ hi, hj ] using this ⟨ i, hi ⟩ ⟨ j, hj ⟩ ‹_› ) ; aesop ]);
  simp_all +decide [ List.getElem_rotate ]

/-
PROBLEM
Complement: if l[a] ≤ l[b] with a ≤ b < l.length, and c is outside [a,b],
then l[c] < l[a] or l[b] < l[c].

PROVIDED SOLUTION
Proof by contradiction using rotated_sorted_mono.

Suppose for contradiction that l[a] ≤ l[c] and l[c] ≤ l[b] (negate the conclusion with push_neg).

First, extract l.Nodup from hrot: since base ~r l and base.Nodup, l is also Nodup (by List.IsRotated.nodup_iff or similar).

Case 1: c < a (from hout).
  Then c ≤ a ≤ b, c < l.length, a < l.length, b < l.length.
  We have l[c] ≤ l[b] (our assumption).
  Apply rotated_sorted_mono l hrot hc hb ha (Nat.le_of_lt_succ (Nat.lt_succ_of_le (le_trans (le_of_lt hout) hab))) (le_of_lt hout) hab (le_trans (le_of_lt (lt_of_le_of_lt h.1 (lt_of_le_of_ne h.2 ...))) ...).
  Wait, let me be cleaner: rotated_sorted_mono on segment [c, b] (c ≤ b since c < a ≤ b), with middle index a (c ≤ a ≤ b), and hval := l[c] ≤ l[b] (which is h.2 composed with something... actually h.2 gives l[c] ≤ l[b] directly).
  So: rotated_sorted_mono l hrot hc hb ha (le_trans (le_of_lt hout) hab) (le_of_lt hout) hab h.2
  This gives l[c] ≤ l[a] ∧ l[a] ≤ l[b].
  The first part l[c] ≤ l[a] combined with h.1 (l[a] ≤ l[c]) gives l[a] = l[c].
  Since l is Nodup and a ≠ c (from c < a), l[a] ≠ l[c]. Contradiction.

Case 2: b < c (from hout).
  Then a ≤ b < c ≤ l.length-1, so a ≤ c.
  We have l[a] ≤ l[c] (from h.1).
  Apply rotated_sorted_mono l hrot ha hc hb (le_trans hab (le_of_lt hout)) hab (le_of_lt hout) h.1
  This gives l[a] ≤ l[b] ∧ l[b] ≤ l[c].
  The second part l[b] ≤ l[c] combined with h.2 (l[c] ≤ l[b]) gives l[b] = l[c].
  Since l is Nodup and b ≠ c (from b < c), l[b] ≠ l[c]. Contradiction.
-/
lemma rotated_sorted_compl (l : List ℤ)
    (hrot : ∃ base, List.Pairwise (· < ·) base ∧ base.Nodup ∧ base ~r l)
    {a b c : ℕ} (ha : a < l.length) (hb : b < l.length) (hc : c < l.length)
    (hab : a ≤ b) (hval : l[a] ≤ l[b])
    (hout : c < a ∨ b < c) : l[c] < l[a] ∨ l[b] < l[c] := by
  -- By contradiction, assume that $l[c] \geq l[a]$ and $l[c] \leq l[b]$.
  by_contra h_contra
  push_neg at h_contra;
  -- Since $l$ is Nodup, we have $l[c] = l[a]$ or $l[c] = l[b]$.
  have h_eq : l[c] = l[a] ∨ l[c] = l[b] := by
    cases hout <;> first | left; exact le_antisymm ( by apply rotated_sorted_mono l hrot hc hb ha ( by linarith ) ( by linarith ) ( by linarith ) ( by linarith ) |>.1 ) ( by linarith ) | right; exact le_antisymm ( by linarith ) ( by apply rotated_sorted_mono l hrot ha hc hb ( by linarith ) ( by linarith ) ( by linarith ) ( by linarith ) |>.2 ) ;
  cases h_eq <;> simp_all +decide [ List.nodup_iff_injective_get ];
  · -- Since $l$ is Nodup, we have $c = a$.
    have h_eq : c = a := by
      have h_eq : List.Nodup l := by
        obtain ⟨ base, hbase₁, hbase₂, hbase₃ ⟩ := hrot;
        exact hbase₃.symm.nodup_iff.mpr ( List.Pairwise.nodup hbase₁ );
      exact?;
    grind +ring;
  · -- Since $l$ is nodup, we have $c = b$.
    have h_eq : c = b := by
      have h_eq : List.Nodup l := by
        obtain ⟨ base, hbase₁, hbase₂, hbase₃ ⟩ := hrot;
        exact hbase₃.symm.nodup_iff.mpr ( List.Pairwise.nodup hbase₁ );
      exact?;
    grind

/-
PROBLEM
After-drop monotonicity: if l[a] > l[b] with a < b in a rotated sorted array,
then for c with b ≤ c < l.length, l[b] ≤ l[c].
(The drop is in [a, b-1], so [b, end] is within one increasing segment.)

PROVIDED SOLUTION
Proof using List.getElem_rotate and modular arithmetic.

1. Obtain base, k such that l = base.rotate k (from hrot and List.IsRotated). Let n = l.length = base.length.
2. l[j] = base[(j+k) % n] by List.getElem_rotate.
3. l[b] < l[a] means base[(b+k)%n] < base[(a+k)%n], so since base is strictly sorted, (b+k)%n < (a+k)%n.
4. Since a < b, a+k < b+k. And (a+k)%n > (b+k)%n. This means (a+k) and (b+k) are in different "laps": (a+k)/n < (b+k)/n. Since b-a < n (because a < b < n), (b+k)/n = (a+k)/n + 1.
5. Let q = (a+k)/n. Then (a+k) = q*n + (a+k)%n and (b+k) = (q+1)*n + (b+k)%n.
6. For c with b ≤ c < n: c+k ≥ b+k. (c+k) - (b+k) = c - b ≤ n - 1 - b + b = n - 1. So c+k < b+k + n ≤ (q+1)*n + (b+k)%n + n ≤ (q+2)*n + n - 1. Actually (c+k) < (b+k) + n since c - b < n. And (b+k) < (q+2)*n (since (b+k)%n < n). So c+k < (q+2)*n + n. But more precisely, c+k - (q+1)*n < n (since c+k < b+k+n ≤ (q+1)*n + n, using b+k ≤ (q+1)*n + n - 1). So (c+k)/n is either q+1 (if c+k < (q+2)*n) or q+2... but c+k < b+k + n ≤ ((q+1)*n + n-1) + n < (q+3)*n. So (c+k)/n ≤ q+2. But (c+k) ≥ b+k ≥ (q+1)*n, so (c+k)/n ≥ q+1. If (c+k)/n = q+1, then (c+k)%n = c+k - (q+1)*n ≥ b+k - (q+1)*n = (b+k)%n. So base[(c+k)%n] ≥ base[(b+k)%n], i.e., l[c] ≥ l[b]. ✓.
   If (c+k)/n = q+2: then c+k ≥ (q+2)*n. But c+k < b+k + n. And b+k < (q+2)*n (since (b+k)/n = q+1, b+k < (q+2)*n). So c+k < (q+2)*n + n - (something)... actually c+k = c - b + b + k ≤ (n-1) + b + k. And (q+2)*n = (b+k)/n * n + n = (b+k) - (b+k)%n + n. So c+k < (n-1) + (b+k) and (q+2)*n = (b+k) - (b+k)%n + n. If (b+k)%n > 0, then (q+2)*n = b+k - (b+k)%n + n ≤ b + k + n. And c+k ≤ n - 1 + b + k < n + b + k. So c+k < (q+2)*n iff c+k < b+k + n - (b+k)%n. Hmm, it's possible that c+k ≥ (q+2)*n... Let me check with example: b=3, k=4, n=5, q+1=1, so (b+k)=7, (b+k)/5=1, (b+k)%5=2. (q+2)*n = 10. c can be at most 4, c+k = 8 < 10. ✓. Another: b=1, k=8, n=5, (b+k)=9, (b+k)/5=1, (q+2)*n=10, c≤4, c+k≤12 > 10! So (c+k)/n could be 2 = q+2.
   In that case: (c+k)%n = c+k - (q+2)*n = c+k - 10. (b+k)%n = 9 - 5 = 4. So (c+k)%n = c+k-10. If c=4, c+k=12, (c+k)%n=2. And (b+k)%n=4. So (c+k)%n < (b+k)%n, giving l[c] < l[b]! But that contradicts our claim!

Wait, let me check: l = base.rotate 8, n=5. base.rotate 8 = base.rotate (8%5) = base.rotate 3. So l = [base[3], base[4], base[0], base[1], base[2]]. a < b, l[b] < l[a]. Let me pick a=0, b=1: l[0] = base[3], l[1] = base[4]. l[1] < l[0] means base[4] < base[3], but base is sorted so base[3] < base[4]. Contradiction. So a=0, b=1 doesn't satisfy l[b] < l[a].

Let me try a=1, b=2: l[1] = base[4], l[2] = base[0]. l[2] < l[1] means base[0] < base[4], which is true. ✓. Now c=4: l[4] = base[2]. Is l[2] ≤ l[4]? base[0] ≤ base[2]? Yes. ✓.

Hmm wait, my earlier computation was wrong. Let me redo with b=2, k=3, n=5: (b+k)=5, (b+k)/5=1, (b+k)%5=0. q+1 = 1. (q+2)*n = 10. c=4: c+k=7. (c+k)/5=1, (c+k)%5=2. (b+k)%n = 0. So (c+k)%n = 2 > 0 = (b+k)%n. ✓. l[c] ≥ l[b]. ✓.

The case (c+k)/n = q+2 might not occur because of the constraint c < n = l.length. Let me verify: We need c+k ≥ (q+2)*n. We have c < n and k is arbitrary. (q+1) = (b+k)/n, so (q+1)*n ≤ b+k < (q+2)*n. So b+k < (q+2)*n. And c+k < n+k. And (q+2)*n = (b+k) - (b+k)%n + n. Since b ≥ 0, (b+k) ≥ k, so (q+2)*n ≥ k + n - (b+k)%n ≥ k + 1 (if (b+k)%n < n). And c+k ≤ (n-1)+k. So c+k < n+k. And (q+2)*n = (b+k) - (b+k)%n + n ≥ b+k - (n-1) + n = b + k + 1. So c+k < n+k ≤ n + k. And (q+2)*n ≥ b+k+1. If b ≥ 1, (q+2)*n ≥ k+2. So c+k ≤ n+k-1. (q+2)*n could be ≤ n+k-1 if... (q+2)*n = (b+k)-(b+k)%n+n. For small b and n, (q+2)*n could be small. Example: n=2, b=1, k=0: (b+k)=1, (b+k)/2=0, (q+2)*n = 2*2=4. c+k ≤ 1+0=1 < 4. OK.
n=2, b=1, k=3: (b+k)=4, (b+k)/2=2, (q+2)*n=4*2=8. c+k ≤ 1+3=4 < 8. OK.

Hmm, it seems like c+k < (q+2)*n always holds when c < n. Let me prove: c+k < (q+2)*n.
We have c < n and (q+1)*n ≤ b+k. So (q+1)*n ≤ b+k ≤ b+k. Since b ≤ c < n, c+k ≤ (n-1)+k. And (q+2)*n = (q+1)*n + n ≥ b+k - (b+k)%n + n ≥ b+k + 1 (if (b+k)%n > 0, since b+k - (b+k)%n + n ≥ b+k + 1 iff n > (b+k)%n + 1... not always).

Hmm actually let me just try: (q+2)*n > c+k iff (q+2)*n > c+k. We have (q+1)*n ≤ b+k and c ≤ n-1. So c+k ≤ n-1+k. And (q+2)*n = (q+1)*n + n. If (q+1)*n ≤ b+k and b ≤ n-1, then (q+1)*n ≤ n-1+k, so (q+1) ≤ (n-1+k)/n. Then (q+2)*n ≤ (n-1+k)/n * n + n. Hmm this doesn't obviously show c+k < (q+2)*n.

OK let me just try: (q+1)*n ≤ b+k < (q+2)*n. And c < n and b ≤ c. So c+k < n+k. And (q+2)*n > b+k ≥ (q+1)*n. If (q+1) ≥ 1, then (q+2)*n ≥ 2n > n+k iff n > k. But k can be arbitrarily large!

So for k ≥ n, (q+2)*n could be ≤ c+k. Let me find a concrete example:n=3, k=5, b=1. (b+k)=6, (b+k)/3=2, q+1=2, (q+2)*n=9. c≤2, c+k≤7 < 9. ✓.n=2, k=10, b=1. (b+k)=11, (b+k)/2=5, q+1=5, (q+2)*n=14. c≤1, c+k≤11 < 14. ✓.n=2, k=100, b=1. (b+k)=101, (b+k)/2=50, (q+2)*n=104. c≤1, c+k≤101 < 104. ✓.

Hmm, seems like it always works. Let me prove it formally:We need c+k < (q+2)*n where q+1 = (b+k)/n and c < n and b ≤ c.c+k = c - b + b + k ≤ (n-1) + (b+k) (since c-b ≤ n-1-b... wait, c < n and b ≤ c, so c - b < n).So c+k < n + (b+k). And (q+2)*n = (q+1)*n + n. Since (q+1)*n ≤ b+k, (q+2)*n ≤ b+k + n. Wait, (q+1)*n ≤ b+k means (q+2)*n = (q+1)*n + n ≤ b+k + n. So c+k < n + b + k = b + k + n and (q+2)*n ≤ b+k+n. Hmm, c+k could equal (q+2)*n - 1 or even (q+2)*n. Not helpful.Wait, c+k ≤ (n-1)+k+b? No, c+k = c + k where c ≤ n-1. So c+k ≤ n-1+k. And (q+2)*n > b+k. And b ≥ 0 so b+k ≥ k. So (q+2)*n > k ≥ 0. And n-1+k < (q+2)*n iff n-1+k < (q+2)*n, i.e., k < (q+2)*n - n + 1 = (q+1)*n + 1. Since (q+1)*n ≤ b+k ≤ n-1+k, (q+1)*n ≤ n-1+k, so (q+1)*n+1 ≤ n+k. So k < n+k, which is always true (n > 0). ✓.

So c+k ≤ n-1+k and (q+2)*n > (q+1)*n+1 > n-1+k? Wait, that's not right. (q+1)*n ≤ n-1+k doesn't mean (q+1)*n + 1 > n-1+k.

Hmm. (q+1)*n ≤ b+k and b ≤ c < n. c+k < n+k. (q+2)*n = (q+1)*n + n. Is c+k < (q+1)*n + n? c+k < n+k ≤ n + (b+k) since k ≤ b+k. And (q+1)*n + n ≥ (b+k) + n - (b+k)%n ≥ b+k+1 (if (b+k)%n < n). So (q+1)*n + n ≥ b+k+1. And c+k = c+k. If c+k > b+k, then c+k ≤ (n-1)+k. And (q+1)*n+n > b+k ≥ 0. Hmm, I can't prove c+k < (q+2)*n in general like this.

Let me try differently. c+k < (q+2)*n? We have (q+1) = (b+k)/n. So (q+1)*n ≤ b+k. Let D = b+k - (q+1)*n = (b+k)%n. So b+k = (q+1)*n + D where 0 ≤ D < n.c+k = c - b + b + k = (c-b) + (q+1)*n + D.Since c - b ≤ n - 1 - 0 = n - 1 (because c ≤ n-1 and b ≥ 0; actually c - b ≤ c ≤ n-1).So c+k ≤ (n-1) + (q+1)*n + D = (q+2)*n - 1 + D.If D = 0: c+k ≤ (q+2)*n - 1 < (q+2)*n. ✓.If D > 0: c+k ≤ (q+2)*n - 1 + D. If D < n, then c+k < (q+2)*n + n - 1. But we need c+k < (q+2)*n, which means (q+2)*n - 1 + D < (q+2)*n, i.e., D < 1, i.e., D = 0. But D could be > 0!

So c+k could be ≥ (q+2)*n when D > 0 and c is large enough. Example:n=3, k=1, b=1, D=(1+1)%3=2. (q+1)=0. q=-1? No, (b+k)/n = 2/3 = 0, so q+1=0. But then (q+2)*n = 1*3 = 3. c≤2, c+k≤3. c+k = 3 when c=2. (c+k)/(q+2)*n = 3/3 = 1 = q+2. So (c+k)/n = 1, not q+1 = 0. So (c+k)/n = q+2!

Let's check: n=3, k=1, base = [0,1,2]. l = base.rotate 1 = [1, 2, 0]. a and b with l[a] > l[b]: a=1, b=2. l[1]=2, l[2]=0. l[2] < l[1]. ✓. c=2: l[2] = 0. l[b] = l[2] = 0 ≤ 0 = l[c]. ✓ (trivially, c=b).

OK so c can't be > b in this case since n=3 and b=2 is the last index. So c ≤ n-1 = b. The only valid c is c=b=2.

Let me try n=5, k=2, base=[0,1,2,3,4]. l = [2,3,4,0,1]. a=2, b=3. l[2]=4, l[3]=0. l[3] < l[2]. ✓. Now c=4: l[4]=1. l[b]=l[3]=0 ≤ 1=l[4]. ✓.

b+k = 3+2 = 5. (b+k)/5 = 1. q+1 = 1. (q+2)*n = 10. c+k = 4+2 = 6 < 10. ✓. So (c+k)/n = 1 = q+1.

OK so the case (c+k)/n = q+2 can happen theoretically, but let me check if it leads to l[c] ≥ l[b].If (c+k)/n = q+2: (c+k)%n = c+k - (q+2)*n. And (b+k)%n = b+k - (q+1)*n = D. We need to show (c+k)%n ≥ (b+k)%n, i.e., c+k - (q+2)*n ≥ D = b+k - (q+1)*n.c+k - (q+2)*n ≥ b+k - (q+1)*n iff c+k - b-k ≥ (q+2)*n - (q+1)*n iff c - b ≥ n.But c < n and b ≥ 0, so c - b < n. Contradiction! So c+k - (q+2)*n < D = (b+k)%n.

So (c+k)%n < (b+k)%n when (c+k)/n = q+2. This means l[c] < l[b], contradicting what we want to prove!

But wait, is this possible for a VALID rotated sorted array with the given constraints? Let me find a concrete example:n=4, k=1, base=[0,1,2,3]. l = [1,2,3,0]. a=2, b=3: l[2]=3, l[3]=0. l[3] < l[2]. ✓.c=3 (=b): l[3]=0 ≥ l[3]=0. ✓.

That's the only valid c since c ≤ n-1 = 3 = b. So no c > b.

n=5, k=3, base=[0,1,2,3,4]. l = [3,4,0,1,2]. a=1, b=2: l[1]=4, l[2]=0. l[2] < l[1]. ✓.c=3: l[3]=1. l[2]=0 ≤ 1. ✓. b+k=5, (5)/5=1, (q+2)*n=10, c+k=6<10. ✓, (c+k)/n=1=q+1. (c+k)%n=1, (b+k)%n=0. 1≥0. ✓.c=4: l[4]=2. l[2]=0 ≤ 2. ✓. c+k=7<10. (c+k)%n=2, (b+k)%n=0. 2≥0. ✓.

Let me try to find a case where (c+k)/n = q+2:Need c+k ≥ (q+2)*n. c < n, so c+k < n+k. (q+2)*n = (q+1)*n + n. (q+1) = (b+k)/n. Need n+k > (q+2)*n, i.e., k > (q+1)*n. Since (q+1)*n ≤ b+k < (q+2)*n, and b < n, b+k < n+k. So (q+1)*n ≤ n+k-1 < n+k. So (q+2)*n = (q+1)*n + n ≤ n+k-1+n = 2n+k-1. And c+k ≤ n-1+k. So c+k < (q+2)*n iff n-1+k < (q+2)*n. Since (q+2)*n ≥ (q+1)*n + n and (q+1)*n > (b+k) - n ≥ k - n + 0 = k-n, so (q+2)*n ≥ k-n+n = k. So (q+2)*n ≥ k. And n-1+k ≥ k, so... not obviously < (q+2)*n.

Hmm wait, let me try k = n*10, b = 0, a must be < b, but b = 0 means a < 0 which is impossible. So b ≥ 1. OK b = 1, a = 0, k = n*10, n = 2. l = base.rotate (20%2) = base.rotate 0 = base = [0,1]. l[0]=0, l[1]=1. l[1] > l[0], not l[1] < l[0]. So doesn't satisfy the hypothesis.

Actually, I realize that for a rotation by k, base.rotate k = base.rotate (k % n). So k is effectively k % n, which is < n. So we can assume WLOG that k < n.

With k < n: c+k < n + k < n + n = 2n. And (q+2)*n: (q+1) = (b+k)/n. Since b < n and k < n, b+k < 2n. So (b+k)/n is 0 or 1.
If (b+k)/n = 0, q+1=0, (q+2)*n = n. c+k < 2n, so (c+k)/n is 0 or 1. Need (c+k)/n = q+2 = 1, i.e., c+k ≥ n. Since c+k < 2n, (c+k)%n = c+k-n.
If (b+k)/n = 1, q+1=1, (q+2)*n = 2n. c+k < 2n, so (c+k)/n = 0 or 1, never 2. So (c+k)/n ≤ 1 = q+1. ✓.

So the "bad" case only happens when (b+k)/n = 0, q+1=0, and (c+k)/n = 1 (c+k ≥ n).

In that case: (b+k)%n = b+k (since b+k < n). (c+k)%n = c+k-n. Need (c+k)%n ≥ (b+k)%n, i.e., c+k-n ≥ b+k, i.e., c-b ≥ n. But c < n and b ≥ 0, so c-b < n. Contradiction!

So the "bad" case leads to c-b ≥ n which is impossible. So (c+k)%n ≥ (b+k)%n always holds!Wait, but I need to verify when (b+k)/n = 0 and (c+k)/n = 1: Is this consistent with l[a] > l[b] (i.e., l[b] < l[a])?

l[a] > l[b] means base[(a+k)%n] > base[(b+k)%n], so (a+k)%n > (b+k)%n. Since a < b, a+k < b+k. And b+k < n (since (b+k)/n = 0). So a+k < n too, meaning (a+k)%n = a+k and (b+k)%n = b+k. Then (a+k)%n > (b+k)%n means a+k > b+k, i.e., a > b. But we assumed a < b! Contradiction!

So when (b+k)/n = 0 (meaning b+k < n, so (b+k)%n = b+k), we can't have l[a] > l[b] with a < b (because (a+k)%n = a+k < b+k = (b+k)%n gives l[a] < l[b]).

So the hypothesis l[b] < l[a] with a < b forces (b+k)/n ≥ 1, which means q+1 ≥ 1. And (q+2)*n = (q+1+1)*n ≥ 2n > c+k (since c < n and k can be reduced to k < n by WLOG).

Wait, k might not be < n in the formal proof. We get k from IsRotated which gives ∃ k ≤ n, base.rotate k = l. So k ≤ n. If k = n, then base.rotate n = base (full rotation). So effectively k < n or k = n (trivial rotation).

With k ≤ n: c+k ≤ (n-1)+n = 2n-1 < 2n ≤ (q+2)*n when q+1 ≥ 1, i.e., q ≥ 0. Since q+1 ≥ 1 (as shown above), (q+2)*n ≥ 2n > 2n-1 ≥ c+k. So (c+k)/n < q+2. ✓.

And (c+k)/n ≥ q+1 (since c+k ≥ b+k ≥ (q+1)*n). So (c+k)/n = q+1.

Then (c+k)%n = c+k - (q+1)*n and (b+k)%n = b+k - (q+1)*n. Since c ≥ b, c+k ≥ b+k, so (c+k)%n ≥ (b+k)%n. ✓.

So l[c] = base[(c+k)%n] ≥ base[(b+k)%n] = l[b]. ✓.

Great, the proof works! Let me just send it to the subagent. The key insight is that with k ≤ n (from IsRotated) and the hypothesis l[b] < l[a] implying (b+k)/n ≥ 1, we get (c+k)/n = (b+k)/n = q+1, so the mods preserve the ordering.
-/
lemma rotated_sorted_after_drop (l : List ℤ)
    (hrot : ∃ base, List.Pairwise (· < ·) base ∧ base.Nodup ∧ base ~r l)
    {a b c : ℕ} (ha : a < l.length) (hb : b < l.length) (hc : c < l.length)
    (hab : a < b) (hbc : b ≤ c)
    (hval : l[b] < l[a]) : l[b] ≤ l[c] := by
  obtain ⟨ base, h_pairwise, h_nodup, hrotate ⟩ := hrot;
  -- Let $n = l.length$. Since $base ~r l$, there exists $k$ such that $k \leq n$ and $l = base.rotate k$.
  obtain ⟨k, hk⟩ : ∃ k ≤ l.length, l = base.rotate k := by
    rcases hrotate with ⟨ k, hk ⟩;
    use k % base.length;
    norm_num [ ← hk, Nat.mod_lt ];
    exact ⟨ Nat.le_of_lt ( Nat.mod_lt _ ( List.length_pos_iff.mpr ( by aesop_cat ) ) ), by rw [ List.rotate_mod ] ⟩;
  have h_mod : (a + k) % l.length > (b + k) % l.length := by
    have h_mod : ∀ i j : ℕ, i < base.length → j < base.length → i < j → base[i]! < base[j]! := by
      rw [ List.pairwise_iff_get ] at h_pairwise;
      exact fun i j hi hj hij => by simpa [ List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj ] using h_pairwise ⟨ i, hi ⟩ ⟨ j, hj ⟩ hij;
    contrapose! hval;
    simp_all +decide [ List.getElem_rotate ];
    by_cases h_cases : (a + k) % base.length < (b + k) % base.length;
    · exact le_of_lt ( h_mod _ _ ( Nat.mod_lt _ ( by linarith ) ) ( Nat.mod_lt _ ( by linarith ) ) h_cases );
    · cases eq_or_lt_of_le hval <;> aesop;
  have h_mod_c : (c + k) % l.length ≥ (b + k) % l.length := by
    have h_mod_c : (c + k) / l.length = (b + k) / l.length := by
      have h_mod_c : (b + k) / l.length ≥ 1 := by
        contrapose! h_mod;
        simp_all +decide [ Nat.div_eq_of_lt ];
        rw [ Nat.mod_eq_of_lt, Nat.mod_eq_of_lt ] <;> linarith [ h_mod.resolve_left ( by aesop_cat ) ];
      have h_mod_c : (c + k) / l.length ≤ (b + k) / l.length := by
        rw [ Nat.le_iff_lt_or_eq ];
        refine' lt_or_eq_of_le ( Nat.le_of_lt_succ _ );
        rw [ Nat.div_lt_iff_lt_mul ] <;> nlinarith [ Nat.div_add_mod ( b + k ) l.length, Nat.mod_lt ( b + k ) ( by linarith : 0 < l.length ) ];
      exact le_antisymm h_mod_c ( Nat.div_le_div_right ( by linarith ) );
    -- Since $(c + k) / l.length = (b + k) / l.length$, we can write $c + k = q * l.length + r$ and $b + k = q * l.length + s$ for some $q$ and $r, s$ where $0 \leq r, s < l.length$.
    obtain ⟨q, r, hr⟩ : ∃ q r, c + k = q * l.length + r ∧ 0 ≤ r ∧ r < l.length := by
      exact ⟨ ( c + k ) / l.length, ( c + k ) % l.length, by rw [ Nat.div_add_mod' ], Nat.zero_le _, Nat.mod_lt _ ( by linarith ) ⟩
    obtain ⟨q', s, hs⟩ : ∃ q' s, b + k = q' * l.length + s ∧ 0 ≤ s ∧ s < l.length := by
      exact ⟨ ( b + k ) / l.length, ( b + k ) % l.length, by rw [ Nat.div_add_mod' ], Nat.zero_le _, Nat.mod_lt _ ( by linarith ) ⟩;
    simp_all +decide [ Nat.add_mod, Nat.mod_eq_of_lt ];
    rw [ Nat.add_div, Nat.add_div ] at h_mod_c <;> norm_num [ Nat.mod_eq_of_lt hr.2, Nat.mod_eq_of_lt hs.2 ] at *;
    · split_ifs at h_mod_c <;> norm_num [ Nat.div_eq_of_lt, hr.2, hs.2 ] at h_mod_c ⊢ ; linarith;
      · linarith;
      · linarith;
      · grind;
    · exact?;
    · grind;
  have h_base_mono : ∀ i j : ℕ, i < base.length → j < base.length → i ≤ j → base[i]! ≤ base[j]! := by
    intros i j hi hj hij
    have h_base_mono : ∀ i j : ℕ, i < base.length → j < base.length → i < j → base[i]! < base[j]! := by
      intros i j hi hj hij;
      have := List.pairwise_iff_get.mp h_pairwise;
      simpa [ hi, hj ] using this ⟨ i, hi ⟩ ⟨ j, hj ⟩ hij;
    cases lt_or_eq_of_le hij <;> [ exact le_of_lt ( h_base_mono _ _ hi hj ‹_› ) ; aesop ];
  simp_all +decide [ List.getElem_rotate ]

end HelperLemmas

section Proof

/-
PROVIDED SOLUTION
Need i < mid where mid = lo + (hi - lo) / 2.

Key facts:
- h_eq: nums[i]? = some target
- if_neg_1: nums[mid]?.getD 0 ≠ target
- a_3: target < nums[mid]?.getD 0
- a_2: nums[lo]?.getD 0 ≤ target
- if_pos: nums[lo]?.getD 0 ≤ nums[mid]?.getD 0
- h_lo_le_i: lo ≤ i, h_i_le_hi: i ≤ hi
- h_mid_bound: mid < nums.length, h_lo_bound: lo < nums.length, hi_lt: i < nums.length
- require_1 gives the rotated sorted structure

Proof by contradiction:
1. Assume i ≥ mid. Since nums[i] = target ≠ nums[mid] (from if_neg_1 and h_eq), i ≠ mid, so i > mid.
2. Use getElem?_getD_of_lt to convert getD to actual array access.
3. Apply rotated_sorted_compl with a=lo, b=mid, c=i:
   - ha = h_lo_bound, hb = h_mid_bound, hc = hi_lt
   - hab: lo ≤ mid (follows from lo ≤ hi and definition of mid)
   - hval: nums[lo] ≤ nums[mid] (from if_pos after converting getD)
   - hout: Or.inr (mid < i)
   This gives nums[i] < nums[lo] ∨ nums[mid] < nums[i].
4. Case nums[i] < nums[lo]: But nums[i] = target ≥ nums[lo] (from a_2). Contradiction.
5. Case nums[mid] < nums[i]: But nums[i] = target < nums[mid] (from a_3). Contradiction.
-/
theorem goal_1_0_0 (nums : List ℤ) (target : ℤ) (ans : ℤ) (found : Bool) (hi : ℕ) (lo : ℕ) (invariant_not_found_ans : found = false → ans = -OfNat.ofNat 1) (a : lo ≤ hi) (require_1 : OfNat.ofNat 0 < nums.length ∧ nums.Nodup ∧ ∃ base, List.Pairwise (fun x1 x2 => x1 < x2) base ∧ base.Nodup ∧ base ~r nums) (if_neg : ¬nums = []) (invariant_n_pos : OfNat.ofNat 0 < nums.length) (invariant_hi_bound : hi < nums.length) (invariant_found_correct : found = true → ∃ i < nums.length, nums[i]? = some target ∧ ans = ↑i ∧ ∀ j < nums.length, nums[j]? = some target → j = i) (invariant_search_range : found = false → ∀ i < nums.length, nums[i]? = some target → lo ≤ i ∧ i ≤ hi) (a_1 : found = false) (if_neg_1 : ¬nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0) = target) (if_pos : nums[lo]?.getD (OfNat.ofNat 0) ≤ nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0)) (a_2 : nums[lo]?.getD (OfNat.ofNat 0) ≤ target) (a_3 : target < nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0)) (if_neg_2 : lo = OfNat.ofNat 0 → OfNat.ofNat 2 ≤ hi - lo) (hf : found = false) (i : ℕ) (hi_lt : i < nums.length) (h_eq : nums[i]? = some target) (h_old : lo ≤ i ∧ i ≤ hi) (h_lo_le_i : lo ≤ i) (h_i_le_hi : i ≤ hi) (h_mid : ℕ) (h_mid_bound : lo + (hi - lo) / 2 < nums.length) (h_lo_bound : lo < nums.length) (h_nodup : nums.Nodup) : i < lo + (hi - lo) / 2 := by
    contrapose! a_3;
    convert rotated_sorted_mono nums ( by aesop ) ( show lo < nums.length from h_lo_bound ) ( show i < nums.length from hi_lt ) ( show lo + ( hi - lo ) / 2 < nums.length from h_mid_bound ) ( by omega ) ( by omega ) ( by omega ) _ |>.2 using 1 <;> aesop;

/-
PROVIDED SOLUTION
Need mid+1 ≤ i and i ≤ hi.

Intro hf i hi_lt h_eq. From invariant_search_range, lo ≤ i ∧ i ≤ hi. So i ≤ hi is done.

For mid+1 ≤ i (i.e., mid < i):
- if_neg_2 says: nums[lo]?.getD 0 ≤ target → nums[mid]?.getD 0 ≤ target
- if_neg_1: nums[mid]?.getD 0 ≠ target
- if_pos: nums[lo]?.getD 0 ≤ nums[mid]?.getD 0
- h_eq: nums[i]? = some target, so by getD_of_getElem?_eq_some, nums[i]?.getD 0 = target

By contradiction, suppose i ≤ mid. Since i ≠ mid (nums[i] = target but nums[mid]?.getD 0 ≠ target, by Nodup and getD), i < mid. So lo ≤ i < mid ≤ hi.

Apply rotated_sorted_mono with a=lo, b=mid, c=i: gives nums[lo] ≤ nums[i] ≤ nums[mid].
So nums[lo] ≤ nums[i] = target, hence nums[lo]?.getD 0 ≤ target.
By if_neg_2: nums[mid]?.getD 0 ≤ target.
Combined with if_neg_1: nums[mid]?.getD 0 < target (strict).
But from mono: nums[i] ≤ nums[mid], so target ≤ nums[mid]?.getD 0. Contradiction.

Actually wait, we need nums[i] ≤ nums[mid] (from mono) but also nums[mid]?.getD 0 < target = nums[i]. So target = nums[i] ≤ nums[mid] and target > nums[mid]. Contradiction!
-/
theorem goal_2_a (nums : List ℤ) (target : ℤ) (ans : ℤ) (found : Bool) (hi : ℕ) (lo : ℕ) (invariant_not_found_ans : found = false → ans = -OfNat.ofNat 1) (a : lo ≤ hi) (require_1 : OfNat.ofNat 0 < nums.length ∧ nums.Nodup ∧ ∃ base, List.Pairwise (fun x1 x2 => x1 < x2) base ∧ base.Nodup ∧ base ~r nums) (if_neg : ¬nums = []) (invariant_n_pos : OfNat.ofNat 0 < nums.length) (invariant_hi_bound : hi < nums.length) (invariant_found_correct : found = true → ∃ i < nums.length, nums[i]? = some target ∧ ans = i.cast ∧ ∀ j < nums.length, nums[j]? = some target → j = i) (invariant_search_range : found = false → ∀ i < nums.length, nums[i]? = some target → lo ≤ i ∧ i ≤ hi) (a_1 : found = false) (if_neg_1 : ¬nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0) = target) (if_pos : nums[lo]?.getD (OfNat.ofNat 0) ≤ nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0)) (if_neg_2 : nums[lo]?.getD (OfNat.ofNat 0) ≤ target → nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0) ≤ target) : found = false → ∀ i < nums.length, nums[i]? = some target → lo + (hi - lo) / OfNat.ofNat 2 + OfNat.ofNat 1 ≤ i ∧ i ≤ hi := by
    intros h i hi_lt h_eq
    obtain ⟨hi_le_mid, hi_ge_mid⟩ := invariant_search_range h i hi_lt h_eq;
    by_cases hi_le_mid : i ≤ lo + (hi - lo) / 2;
    · have h_mono : nums[lo] ≤ nums[i] ∧ nums[i] ≤ nums[lo + (hi - lo) / 2] := by
        apply rotated_sorted_mono;
        · aesop;
        · exact Nat.le_add_right _ _;
        · linarith;
        · assumption;
        · convert if_pos using 1;
          · exact?;
          · rw [ List.getElem?_eq_getElem ] ; aesop;
      grind +ring;
    · exact ⟨ not_le.mp hi_le_mid, hi_ge_mid ⟩

theorem goal_2_b (nums : List ℤ) (target : ℤ) (ans : ℤ) (found : Bool) (hi : ℕ) (lo : ℕ) (invariant_not_found_ans : found = false → ans = -OfNat.ofNat 1) (a : lo ≤ hi) (require_1 : OfNat.ofNat 0 < nums.length ∧ nums.Nodup ∧ ∃ base, List.Pairwise (fun x1 x2 => x1 < x2) base ∧ base.Nodup ∧ base ~r nums) (if_neg : ¬nums = []) (invariant_n_pos : OfNat.ofNat 0 < nums.length) (invariant_hi_bound : hi < nums.length) (invariant_found_correct : found = true → ∃ i < nums.length, nums[i]? = some target ∧ ans = i.cast ∧ ∀ j < nums.length, nums[j]? = some target → j = i) (invariant_search_range : found = false → ∀ i < nums.length, nums[i]? = some target → lo ≤ i ∧ i ≤ hi) (a_1 : found = false) (if_neg_1 : ¬nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0) = target) (if_pos : nums[lo]?.getD (OfNat.ofNat 0) ≤ nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0)) (if_neg_2 : nums[lo]?.getD (OfNat.ofNat 0) ≤ target → nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0) ≤ target) : found = false → ∀ i < nums.length, nums[i]? = some target → lo + (hi - lo) / OfNat.ofNat 2 + OfNat.ofNat 1 ≤ i ∧ i ≤ hi := by
    exact goal_2_a nums target ans found hi lo invariant_not_found_ans a require_1 if_neg invariant_n_pos invariant_hi_bound invariant_found_correct invariant_search_range a_1 if_neg_1 if_pos if_neg_2

/-
PROVIDED SOLUTION
Need mid+1 ≤ i and i ≤ hi.

Intro hf i hi_lt h_eq. From invariant_search_range hf, lo ≤ i ∧ i ≤ hi. So i ≤ hi is done.

For mid+1 ≤ i (i.e., mid < i):
- if_neg_2: nums[mid]?.getD 0 < nums[lo]?.getD 0 (right half has wrap-around, meaning nums[mid] < nums[lo])
- a_2: nums[mid]?.getD 0 < target
- a_3: target ≤ nums[hi]?.getD 0
- if_neg_1: nums[mid]?.getD 0 ≠ target
- h_eq: nums[i]? = some target

Since target > nums[mid] (a_2), and target = nums[i] (h_eq), nums[i] > nums[mid], so i ≠ mid.

By contradiction, suppose i ≤ mid. Then i < mid (since i ≠ mid). So lo ≤ i < mid.

Now, from if_neg_2: nums[mid] < nums[lo]. And a_2: nums[mid] < target = nums[i].
From a_3: target ≤ nums[hi], so nums[i] ≤ nums[hi].

But we need to use the rotated sorted structure. Apply rotated_sorted_compl with a=mid, b=hi, c=i:
- We need nums[mid] ≤ nums[hi]. From a_2 and a_3: nums[mid] < target ≤ nums[hi], so nums[mid] ≤ nums[hi]. ✓
- mid ≤ hi: follows from lo ≤ hi and mid = lo + (hi-lo)/2 ≤ hi. ✓
- hout: i < mid (from our assumption). So Or.inl (i < mid). ✓
This gives: nums[i] < nums[mid] ∨ nums[hi] < nums[i].
- nums[i] < nums[mid]: But nums[i] = target > nums[mid] (from a_2). Contradiction.
- nums[hi] < nums[i]: But nums[i] = target ≤ nums[hi] (from a_3). Contradiction.
-/
theorem goal_3 (nums : List ℤ) (target : ℤ) (ans : ℤ) (found : Bool) (hi : ℕ) (lo : ℕ) (invariant_not_found_ans : found = false → ans = -OfNat.ofNat 1) (a : lo ≤ hi) (require_1 : OfNat.ofNat 0 < nums.length ∧ nums.Nodup ∧ ∃ base, List.Pairwise (fun x1 x2 => x1 < x2) base ∧ base.Nodup ∧ base ~r nums) (if_neg : ¬nums = []) (invariant_n_pos : OfNat.ofNat 0 < nums.length) (invariant_hi_bound : hi < nums.length) (invariant_found_correct : found = true → ∃ i < nums.length, nums[i]? = some target ∧ ans = i.cast ∧ ∀ j < nums.length, nums[j]? = some target → j = i) (invariant_search_range : found = false → ∀ i < nums.length, nums[i]? = some target → lo ≤ i ∧ i ≤ hi) (a_1 : found = false) (if_neg_1 : ¬nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0) = target) (if_neg_2 : nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0) < nums[lo]?.getD (OfNat.ofNat 0)) (a_2 : nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0) < target) (a_3 : target ≤ nums[hi]?.getD (OfNat.ofNat 0)) : found = false → ∀ i < nums.length, nums[i]? = some target → lo + (hi - lo) / OfNat.ofNat 2 + OfNat.ofNat 1 ≤ i ∧ i ≤ hi := by
    intros hf i hi_lt h_eq;
    by_contra h_contra;
    have h_mid_lt_i : i < lo + (hi - lo) / 2 := by
      grind;
    have h_rotated_sorted_compl : nums[i] < nums[lo + (hi - lo) / 2] ∨ nums[hi] < nums[i] := by
      apply rotated_sorted_compl;
      · aesop;
      · exact Nat.le_of_lt_succ ( by norm_num at *; omega );
      · grind;
      · exact Or.inl h_mid_lt_i;
    grind

/-
PROVIDED SOLUTION
Need lo ≤ i and i ≤ mid - 1.

Intro hf i hi_lt h_eq. From invariant_search_range hf, lo ≤ i ∧ i ≤ hi. So lo ≤ i is done.

For i ≤ mid - 1 (i.e., i < mid): by contradiction, suppose i ≥ mid. Since i ≠ mid (by Nodup: nums[i] = target but nums[mid] ≠ target from if_neg_1), i > mid.

Key step: From if_neg_2, nums[mid] < nums[lo] with lo < mid. By rotated_sorted_after_drop with a=lo, b=mid, this gives nums[mid] ≤ nums[c] for all c with mid ≤ c < nums.length. In particular:
- nums[mid] ≤ nums[i] (since mid ≤ i < nums.length)
- nums[mid] ≤ nums[hi] (since mid ≤ hi < nums.length)

So nums[mid] ≤ nums[hi], and by rotated_sorted_mono on [mid, hi] (nums[mid] ≤ nums[hi], mid ≤ i ≤ hi):
nums[mid] ≤ nums[i] ≤ nums[hi].

So target = nums[i] ≤ nums[hi]. Also nums[mid] ≤ target. Since nums[mid] ≠ target (if_neg_1), nums[mid] < target. By if_neg_3: nums[hi] < target. But we just showed target ≤ nums[hi]. Contradiction!

Note: we need lo < mid. This follows from: if lo = mid = lo + (hi-lo)/2, then (hi-lo)/2 = 0. If lo = 0, by if_neg_4, 2 ≤ hi - lo, so (hi-lo)/2 ≥ 1, contradiction. If lo > 0, then hi - lo < 2, so hi ≤ lo + 1. Since lo ≤ hi, hi = lo or hi = lo + 1. If hi = lo, mid = lo, and if_neg_2 says nums[lo] < nums[lo], contradiction. If hi = lo + 1, mid = lo + 0 = lo (since (1)/2 = 0), same contradiction.

To convert getD to actual values, use getElem?_getD_of_lt with appropriate bounds.
-/
theorem goal_4 (nums : List ℤ) (target : ℤ) (ans : ℤ) (found : Bool) (hi : ℕ) (lo : ℕ) (invariant_not_found_ans : found = false → ans = -OfNat.ofNat 1) (a : lo ≤ hi) (require_1 : OfNat.ofNat 0 < nums.length ∧ nums.Nodup ∧ ∃ base, List.Pairwise (fun x1 x2 => x1 < x2) base ∧ base.Nodup ∧ base ~r nums) (if_neg : ¬nums = []) (invariant_n_pos : OfNat.ofNat 0 < nums.length) (invariant_hi_bound : hi < nums.length) (invariant_found_correct : found = true → ∃ i < nums.length, nums[i]? = some target ∧ ans = i.cast ∧ ∀ j < nums.length, nums[j]? = some target → j = i) (invariant_search_range : found = false → ∀ i < nums.length, nums[i]? = some target → lo ≤ i ∧ i ≤ hi) (a_1 : found = false) (if_neg_1 : ¬nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0) = target) (if_neg_2 : nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0) < nums[lo]?.getD (OfNat.ofNat 0)) (if_neg_3 : nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0) < target → nums[hi]?.getD (OfNat.ofNat 0) < target) (if_neg_4 : lo = OfNat.ofNat 0 → OfNat.ofNat 2 ≤ hi - lo) : found = false → ∀ i < nums.length, nums[i]? = some target → lo ≤ i ∧ i ≤ lo + (hi - lo) / OfNat.ofNat 2 - OfNat.ofNat 1 := by
    intros hf i hi_lt h_eq;
    -- From the invariant_search_range, we know that lo ≤ i and i ≤ hi.
    have h_bounds : lo ≤ i ∧ i ≤ hi := by
      exact invariant_search_range hf i hi_lt h_eq;
    -- By contradiction, assume $i \geq lo + (hi - lo) / 2$.
    by_contra h_contra;
    have h_le : nums[lo + (hi - lo) / 2] ≤ nums[i] ∧ nums[i] ≤ nums[hi] := by
      apply rotated_sorted_mono;
      · aesop;
      · exact le_trans ( Nat.add_le_add_left ( Nat.div_le_self _ _ ) _ ) ( by omega );
      · grind;
      · linarith;
      · have h_le : nums[lo + (hi - lo) / 2] ≤ nums[hi] := by
          have h_lt : lo < lo + (hi - lo) / 2 := by
            grind +ring
          apply rotated_sorted_after_drop;
          exact ⟨ _, require_1.2.2.choose_spec.1, require_1.2.2.choose_spec.2.1, require_1.2.2.choose_spec.2.2 ⟩;
          any_goals omega;
          grind;
        exact h_le;
    grind +ring

/-
PROVIDED SOLUTION
Case split on found. If found = true, use invariant_found_correct to get index i, unfold postcondition/inList, use Right disjunct. If found = false, use invariant_not_found_ans for ans = -1, show target ∉ nums by contradiction using invariant_search_range and if_neg_1. Use Left disjunct.
-/
theorem goal_5 (nums : List ℤ) (target : ℤ) (ans : ℤ) (found : Bool) (hi : ℕ) (lo : ℕ) (invariant_not_found_ans : found = false → ans = -OfNat.ofNat 1) (require_1 : OfNat.ofNat 0 < nums.length ∧ nums.Nodup ∧ ∃ base, List.Pairwise (fun x1 x2 => x1 < x2) base ∧ base.Nodup ∧ base ~r nums) (if_neg : ¬nums = []) (invariant_n_pos : OfNat.ofNat 0 < nums.length) (invariant_hi_bound : hi < nums.length) (invariant_found_correct : found = true → ∃ i < nums.length, nums[i]? = some target ∧ ans = i.cast ∧ ∀ j < nums.length, nums[j]? = some target → j = i) (invariant_search_range : found = false → ∀ i < nums.length, nums[i]? = some target → lo ≤ i ∧ i ≤ hi) (if_neg_1 : lo ≤ hi → found = true) : postcondition nums target ans := by
    by_cases h : found = true <;> simp_all +decide [ postcondition ];
    exact Or.inl fun h => by obtain ⟨ i, hi ⟩ := List.mem_iff_get.mp h; have := invariant_search_range i ( by aesop ) ( by aesop ) ; linarith;

end Proof
