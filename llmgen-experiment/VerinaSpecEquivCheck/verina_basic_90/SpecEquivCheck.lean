import Mathlib.Tactic

namespace VerinaSpec


def get2d (a : Array (Array Int)) (i j : Int) : Int :=
  (a[Int.toNat i]!)[Int.toNat j]!

def SlopeSearch_precond (a : Array (Array Int)) (key : Int) : Prop :=
  a.size > 0 ∧
  (a[0]!).size > 0 ∧  -- non-empty inner arrays
  List.Pairwise (·.size = ·.size) a.toList ∧
  a.all (fun x => List.Pairwise (· ≤ ·) x.toList) ∧
  (List.range (a[0]!.size)).all (fun i =>
    List.Pairwise (· ≤ ·) (a.map (fun x => x[i]!)).toList
  )

def SlopeSearch_postcond (a : Array (Array Int)) (key : Int) (result: (Int × Int)) :=
  let (m, n) := result;
  (m ≥ 0 ∧ m < a.size ∧ n ≥ 0 ∧ n < (a[0]!).size ∧ get2d a m n = key) ∨
  (m = -1 ∧ n = -1 ∧ a.all (fun x => x.all (fun e => e ≠ key)))

end VerinaSpec

namespace LLMSpec

-- Number of columns; defined safely even for empty outer arrays.
-- When `a.size = 0`, we define `ncols a = 0`.
-- When `a.size > 0`, we define `ncols a = (a[0]!).size`.
def ncols (a : Array (Array Int)) : Nat :=
  if h : a.size > 0 then
    (a[0]!).size
  else
    0

-- Matrix has at least one row, and all rows have the same positive length.
def isRectangularNonempty (a : Array (Array Int)) : Prop :=
  a.size > 0 ∧
  ncols a > 0 ∧
  (∀ (r : Nat), r < a.size → a[r]!.size = ncols a)

-- Row-wise nondecreasing ordering.
def rowsNondecreasing (a : Array (Array Int)) : Prop :=
  ∀ (r : Nat) (c1 : Nat) (c2 : Nat),
    r < a.size → c1 < c2 → c2 < ncols a → (a[r]!)[c1]! ≤ (a[r]!)[c2]!

-- Column-wise nondecreasing ordering.
def colsNondecreasing (a : Array (Array Int)) : Prop :=
  ∀ (c : Nat) (r1 : Nat) (r2 : Nat),
    c < ncols a → r1 < r2 → r2 < a.size → (a[r1]!)[c]! ≤ (a[r2]!)[c]!

-- The key appears somewhere in the matrix.
def keyOccurs (a : Array (Array Int)) (key : Int) : Prop :=
  ∃ (r : Nat) (c : Nat),
    r < a.size ∧ c < ncols a ∧ (a[r]!)[c]! = key

-- Preconditions: rectangular non-empty matrix, sorted by rows and by columns.
def precondition (a : Array (Array Int)) (key : Int) : Prop :=
  isRectangularNonempty a ∧
  rowsNondecreasing a ∧
  colsNondecreasing a

-- Postcondition:
-- Either the key does not occur and result is (-1,-1),
-- or the key occurs and result is an (Int.ofNat r, Int.ofNat c) pointing to a key cell.
def postcondition (a : Array (Array Int)) (key : Int) (result : Int × Int) : Prop :=
  ((¬ keyOccurs a key) ∧ result = (-1, -1)) ∨
  (∃ (r : Nat) (c : Nat),
    r < a.size ∧
    c < ncols a ∧
    result = (Int.ofNat r, Int.ofNat c) ∧
    (a[r]!)[c]! = key)

end LLMSpec

section Proof

theorem precondition_equiv (a : Array (Array Int)) (key : Int) :
  VerinaSpec.SlopeSearch_precond a key ↔ LLMSpec.precondition a key := by
  sorry

theorem postcondition_equiv (a : Array (Array Int)) (key : Int) (result: (Int × Int)) :
  LLMSpec.precondition a key →
  (VerinaSpec.SlopeSearch_postcond a key result ↔ LLMSpec.postcondition a key result) := by
  sorry

end Proof
