import Velvet.Std
import Extensions.Testing
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem: onlineMax

section Specs

register_specdef_allow_recursion

def precondition (a : Array Int) (x : Nat) : Prop :=
  a.size > 0 ∧ x > 0 ∧ x < a.size  -- x must be at least 1 (as stated in description)

instance instDecidablePrecond (a : Array Int) (x : Nat) : Decidable (precondition a x) := by
  unfold precondition
  infer_instance

def postcondition (a : Array Int) (x : Nat) (result : Int × Nat) :=
  let (m, p) := result;
(x ≤ p ∧ p < a.size) ∧
(∀ i, i < x → a[i]! ≤ m) ∧
(∃ i, i < x ∧ a[i]! = m) ∧
((p < a.size - 1) → (∀ i, i < p → a[i]! < a[p]!)) ∧
((∀ i, x ≤ i → i < a.size → a[i]! ≤ m) → p = a.size - 1)

end Specs

section Impl

def findBest (a : Array Int) (x : Nat) (i : Nat) (best : Int) : Int :=
  if i < x then
    let newBest := if a[i]! > best then a[i]! else best
    findBest a x (i + 1) newBest
  else best

def findP (a : Array Int) (x : Nat) (m : Int) (i : Nat) : Nat :=
  if i < a.size then
    if a[i]! > m then i else findP a x m (i + 1)
  else a.size - 1

def onlineMax (a : Array Int) (x : Nat) : Int × Nat :=
  let best := a[0]!
  let m := findBest a x 1 best;
  let p := findP a x m x;
  (m, p)

end Impl

section TestCases

def test1_a : Array Int := #[3, 7, 5, 2, 9]
def test1_x : Nat := 3
def test1_Expected : Int × Nat := (7, 4)

def test2_a : Array Int := #[10, 10, 5, 1]
def test2_x : Nat := 2
def test2_Expected : Int × Nat := (10, 3)

def test3_a : Array Int := #[1, 3, 3, 3, 1]
def test3_x : Nat := 2
def test3_Expected : Int × Nat := (3, 4)

def test4_a : Array Int := #[5, 4, 4, 6, 2]
def test4_x : Nat := 2
def test4_Expected : Int × Nat := (5, 3)

def test5_a : Array Int := #[2, 8, 7, 7, 7]
def test5_x : Nat := 3
def test5_Expected : Int × Nat := (8, 4)

def test6_a : Array Int := #[-16, 11, -18, 16, 9, 0]
def test6_x : Nat := 4
def test6_Expected : Int × Nat := (16, 5)

def test7_a : Array Int := #[20, -16, -3, 7]
def test7_x : Nat := 3
def test7_Expected : Int × Nat := (20, 3)

def test8_a : Array Int := #[0, 1, 13, -11, 9, 20, 10, -2, 11, 6, -6, 12, 12, -20]
def test8_x : Nat := 8
def test8_Expected : Int × Nat := (20, 13)

def test9_a : Array Int := #[-13, 4, 5, 4, 18, 0, -10]
def test9_x : Nat := 5
def test9_Expected : Int × Nat := (18, 6)

def test10_a : Array Int := #[14, -3, 8, -18, 5, -1, -18, -3, -5]
def test10_x : Nat := 8
def test10_Expected : Int × Nat := (14, 8)

def test11_a : Array Int := #[4, -8, -6, -17, 5, -4, -7, 17, 16, 11, -9, 3, -10, 7]
def test11_x : Nat := 6
def test11_Expected : Int × Nat := (5, 7)

def test12_a : Array Int := #[-15, 12, -10, 12, 3, -10, 17, -3, 10, 3, -2, 14, 17, 20, -4, 19, -2, -10, -17, 15]
def test12_x : Nat := 13
def test12_Expected : Int × Nat := (17, 13)

def test13_a : Array Int := #[4, 8, -6, -4, -20, 2, 20, 10, 16, -14, 2, -14, 13, -18, -20, 5]
def test13_x : Nat := 11
def test13_Expected : Int × Nat := (20, 15)

def test14_a : Array Int := #[-8, -7, 18, 20, 10, 15, -12, 19, -5, 13, 8, -20, 0, -13, -2]
def test14_x : Nat := 6
def test14_Expected : Int × Nat := (20, 14)

def test15_a : Array Int := #[10, 7, -15, 11, -14, -19, 5, -15, -10, -9, -4, -19, -1, -18, 9, -7, 16, 9, 18]
def test15_x : Nat := 17
def test15_Expected : Int × Nat := (16, 18)

def test16_a : Array Int := #[9, 20, 9, -12, 20, 15, 8, 20, 2, 3, 15, 0, 13, 2, -9, -1, 14, 0, -20]
def test16_x : Nat := 2
def test16_Expected : Int × Nat := (20, 18)

def test17_a : Array Int := #[-20, -16, -17, 3, -10, 19, 12, 8, -9, -5, -11, -20]
def test17_x : Nat := 8
def test17_Expected : Int × Nat := (19, 11)

def test18_a : Array Int := #[6, -6, 15, 6, 16, -7, -8, -15, -8, 17]
def test18_x : Nat := 2
def test18_Expected : Int × Nat := (6, 2)

def test19_a : Array Int := #[-2, 18, -7, 10, 13]
def test19_x : Nat := 4
def test19_Expected : Int × Nat := (18, 4)

def test20_a : Array Int := #[-10, 7, -17, -14, -13, 11, 4, -5, -17, 16, 4]
def test20_x : Nat := 6
def test20_Expected : Int × Nat := (11, 9)

def test21_a : Array Int := #[1, 4, 14, 8, 18, -6, -1, 8, 9, 15, 11]
def test21_x : Nat := 2
def test21_Expected : Int × Nat := (4, 2)

def test22_a : Array Int := #[-8, 0, 1, -14, 7, -15, 1, -18, 6, -16, -12, -3, -8, -10, -11, -17, 12, 9, 11, -14]
def test22_x : Nat := 15
def test22_Expected : Int × Nat := (7, 16)

def test23_a : Array Int := #[12, 19, -3, 10, -14, -20, -13, 7, 14, 3]
def test23_x : Nat := 9
def test23_Expected : Int × Nat := (19, 9)

def test24_a : Array Int := #[-18, -19, 13, 10, 13, 3, 17, 8, 20, -8, -4, 13, -15]
def test24_x : Nat := 3
def test24_Expected : Int × Nat := (13, 6)

def test25_a : Array Int := #[2, -6, -18, -8, 11, -16, 16, -2, -19, -14, 17, 3, 10, -9, -13, -9, -1, -11, 10, 7]
def test25_x : Nat := 18
def test25_Expected : Int × Nat := (17, 19)

def test26_a : Array Int := #[-2, 9, -5, 19, 1, -12, 4, -11, 1]
def test26_x : Nat := 3
def test26_Expected : Int × Nat := (9, 3)

def test27_a : Array Int := #[-18, 20, 16, 1, 17, -19, 2, -4, -15, 14, -10, -15, -11, -19, -14, 1]
def test27_x : Nat := 9
def test27_Expected : Int × Nat := (20, 15)

def test28_a : Array Int := #[-13, -9, 20, 19, -13, 15, -18, -7, -15, 14, 9, 1, -14, -13, -9, 4, -11, 0, 10, -19]
def test28_x : Nat := 2
def test28_Expected : Int × Nat := (-9, 2)

def test29_a : Array Int := #[8, -18, 17, 10, 5, 2, -11, -11, 14, 0, 2, -19, 12, 3, 7, 11, -14, 5, 16, 14]
def test29_x : Nat := 4
def test29_Expected : Int × Nat := (17, 19)

def test30_a : Array Int := #[13, -9, 6, 14, 11, -20, 19, 18, -4, -16, 7, -10]
def test30_x : Nat := 4
def test30_Expected : Int × Nat := (14, 6)

def test31_a : Array Int := #[-4, 8, 20, 7, -5, -18, 14, 13, 19, 14, 4, 3, -16, 3, 7, 9, -5, -5, 13, -5]
def test31_x : Nat := 14
def test31_Expected : Int × Nat := (20, 19)

def test32_a : Array Int := #[-12, 2, -13, 6, -13, 17, 16, 4, 2, -3, -9, 0, 18, 0]
def test32_x : Nat := 10
def test32_Expected : Int × Nat := (17, 12)

def test33_a : Array Int := #[19, -6, 6, 0, -4, 17, 17, 1, 3, -16, 12]
def test33_x : Nat := 2
def test33_Expected : Int × Nat := (19, 10)

def test34_a : Array Int := #[1, -18, 10, -7, -11, 18, 10, 6, -1, -1, -13, -13, -8, 5, -10]
def test34_x : Nat := 3
def test34_Expected : Int × Nat := (10, 5)

def test35_a : Array Int := #[-8, -20, 18, -11, 15, 14, 18, 15, 17, -14, 3, -9, -12, -19, 14, -8, 17, -13, 11, -8]
def test35_x : Nat := 19
def test35_Expected : Int × Nat := (18, 19)
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test4 (result : Int × Nat) :
  result ≠ test4_Expected →
  ¬ postcondition test4_a test4_x result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  plausible'_mut (seeds := #[test4_Expected]) (config := { numInst := 100000 })
