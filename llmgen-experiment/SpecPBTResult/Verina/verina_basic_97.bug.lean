import Velvet.Std
import Extensions.Testing
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem: TestArrayElements

section Specs

register_specdef_allow_recursion

def precondition (a : Array Int) (j : Nat) : Prop :=
  j < a.size

instance instDecidablePrecond (a : Array Int) (j : Nat) : Decidable (precondition a j) := by
  unfold precondition
  infer_instance

def postcondition (a : Array Int) (j : Nat) (result : Array Int) :=
  (result[j]! = 60) ∧ (∀ k, k < a.size → k ≠ j → result[k]! = a[k]!)

end Specs

section Impl

def TestArrayElements (a : Array Int) (j : Nat) : Array Int :=
  a.set! j 60

end Impl

section TestCases

def test1_a : Array Int := #[1, 2, 3, 4, 5]
def test1_j : Nat := 2
def test1_Expected : Array Int := #[1, 2, 60, 4, 5]

def test2_a : Array Int := #[60, 30, 20]
def test2_j : Nat := 1
def test2_Expected : Array Int := #[60, 60, 20]

def test3_a : Array Int := #[10, 20, 30]
def test3_j : Nat := 0
def test3_Expected : Array Int := #[60, 20, 30]

def test4_a : Array Int := #[5, 10, 15]
def test4_j : Nat := 2
def test4_Expected : Array Int := #[5, 10, 60]

def test5_a : Array Int := #[0]
def test5_j : Nat := 0
def test5_Expected : Array Int := #[60]

def test6_a : Array Int := #[-13, -9, -5, 4, -20, 14, -14, -3, 19, -14, -13, 2, -2, -7, 4, 19, -9, -4, -10, -5]
def test6_j : Nat := 0
def test6_Expected : Array Int := #[60, -9, -5, 4, -20, 14, -14, -3, 19, -14, -13, 2, -2, -7, 4, 19, -9, -4, -10, -5]

def test7_a : Array Int := #[-13, 16, 19, 18, -2, -14, -18, -9, -6]
def test7_j : Nat := 2
def test7_Expected : Array Int := #[-13, 16, 60, 18, -2, -14, -18, -9, -6]

def test8_a : Array Int := #[4, 12, -11, -11, -6, 13, -5, -9, -3, -16, 19, -13, 5, 6, -12]
def test8_j : Nat := 14
def test8_Expected : Array Int := #[4, 12, -11, -11, -6, 13, -5, -9, -3, -16, 19, -13, 5, 6, 60]

def test9_a : Array Int := #[9, -14, 14, -4, 3, 8, 13, 5, 20, 2, 0, -13, 15, -20]
def test9_j : Nat := 8
def test9_Expected : Array Int := #[9, -14, 14, -4, 3, 8, 13, 5, 60, 2, 0, -13, 15, -20]

def test10_a : Array Int := #[13, 18, -1, 3, 20, -11, -3, -8, -18, -3, -4, 16, 17, -9, 1, -2, 8, -15, -8, -14]
def test10_j : Nat := 6
def test10_Expected : Array Int := #[13, 18, -1, 3, 20, -11, 60, -8, -18, -3, -4, 16, 17, -9, 1, -2, 8, -15, -8, -14]

def test11_a : Array Int := #[-12, -3, -10, -1, -2, 11, -12, -20, 16, 16, -1, -9, 15, 1, -1, -9, 6, -9, 2, 1]
def test11_j : Nat := 9
def test11_Expected : Array Int := #[-12, -3, -10, -1, -2, 11, -12, -20, 16, 60, -1, -9, 15, 1, -1, -9, 6, -9, 2, 1]

def test12_a : Array Int := #[-8, 8, 9, 15, -20, 3, -15, 0, -10]
def test12_j : Nat := 2
def test12_Expected : Array Int := #[-8, 8, 60, 15, -20, 3, -15, 0, -10]

def test13_a : Array Int := #[6, 1, 20, 2, -7, 10, 2, -7, 19, 16, 19, -12, 1, -11, 16, -7, -5, -3, -2, -6]
def test13_j : Nat := 14
def test13_Expected : Array Int := #[6, 1, 20, 2, -7, 10, 2, -7, 19, 16, 19, -12, 1, -11, 60, -7, -5, -3, -2, -6]

def test14_a : Array Int := #[1, -16, 9, -3, 14, 3, -2, 6, 13, -17, 10, -10, -8, -10, 19, -9, 20, -4, 0, 16]
def test14_j : Nat := 6
def test14_Expected : Array Int := #[1, -16, 9, -3, 14, 3, 60, 6, 13, -17, 10, -10, -8, -10, 19, -9, 20, -4, 0, 16]

def test15_a : Array Int := #[18, 8, 16, -7, -4, -2, -8, -19, -7, 9, -4, -20, 16, 3, 14, -3, -4, 18, 0, -2]
def test15_j : Nat := 12
def test15_Expected : Array Int := #[18, 8, 16, -7, -4, -2, -8, -19, -7, 9, -4, -20, 60, 3, 14, -3, -4, 18, 0, -2]

def test16_a : Array Int := #[-1, -9, -12, -2, 0, 14, 13]
def test16_j : Nat := 0
def test16_Expected : Array Int := #[60, -9, -12, -2, 0, 14, 13]

def test17_a : Array Int := #[3, 18, 2, -10, -18, 7, 5, -10, -3, 0, -10]
def test17_j : Nat := 5
def test17_Expected : Array Int := #[3, 18, 2, -10, -18, 60, 5, -10, -3, 0, -10]

def test18_a : Array Int := #[-8, 6, -16, -11, 9, 20, -11, 17, -10, 9, 3, -7, -20, 19, -3]
def test18_j : Nat := 11
def test18_Expected : Array Int := #[-8, 6, -16, -11, 9, 20, -11, 17, -10, 9, 3, 60, -20, 19, -3]

def test19_a : Array Int := #[18, -20, -16, -2, -6, 5, -8, -16, -2, 3, 18, -16, 18, -16, -14, -2, -9, 4, -6, -13]
def test19_j : Nat := 7
def test19_Expected : Array Int := #[18, -20, -16, -2, -6, 5, -8, 60, -2, 3, 18, -16, 18, -16, -14, -2, -9, 4, -6, -13]

def test20_a : Array Int := #[-8, -13, 13, -2, 5, -7, 12, 1, 10]
def test20_j : Nat := 7
def test20_Expected : Array Int := #[-8, -13, 13, -2, 5, -7, 12, 60, 10]

def test21_a : Array Int := #[15, 20, 13, 15, -1, -10, 16, 14, 6, 13]
def test21_j : Nat := 5
def test21_Expected : Array Int := #[15, 20, 13, 15, -1, 60, 16, 14, 6, 13]

def test22_a : Array Int := #[-11, 10, -12, -13, -1, -15, -12, 0, 6, -15, -9, 14, 8, -10, -1, 11, -18, 20, 12]
def test22_j : Nat := 0
def test22_Expected : Array Int := #[60, 10, -12, -13, -1, -15, -12, 0, 6, -15, -9, 14, 8, -10, -1, 11, -18, 20, 12]

def test23_a : Array Int := #[-6, 11, -1, -16, 7, -9, -9, 6, 7, 10, 20, 17, 6, 7, -14, -20, 17, 7, -5, -3]
def test23_j : Nat := 18
def test23_Expected : Array Int := #[-6, 11, -1, -16, 7, -9, -9, 6, 7, 10, 20, 17, 6, 7, -14, -20, 17, 7, 60, -3]

def test24_a : Array Int := #[9, -16, 8, 2, -8, -15, -4, 18, 0, 18, 18, 15, 12, -13]
def test24_j : Nat := 3
def test24_Expected : Array Int := #[9, -16, 8, 60, -8, -15, -4, 18, 0, 18, 18, 15, 12, -13]

def test25_a : Array Int := #[7, -5, -4, -17, 9, -1, -5, -10, -19, -16, -11, 15, 8, -11, 19, 7, -17, 16, -15]
def test25_j : Nat := 17
def test25_Expected : Array Int := #[7, -5, -4, -17, 9, -1, -5, -10, -19, -16, -11, 15, 8, -11, 19, 7, -17, 60, -15]

def test26_a : Array Int := #[-15, 5, -18, 6, 18, -11, 20, -12, 10, -9, -14, -5, 7, -18, -20]
def test26_j : Nat := 2
def test26_Expected : Array Int := #[-15, 5, 60, 6, 18, -11, 20, -12, 10, -9, -14, -5, 7, -18, -20]

def test27_a : Array Int := #[-1, 11, 14, 18, -15, -15, 10, 0, 16, -5, -15, -5, -11, 15, -19, 8, 14, -13, 9]
def test27_j : Nat := 4
def test27_Expected : Array Int := #[-1, 11, 14, 18, 60, -15, 10, 0, 16, -5, -15, -5, -11, 15, -19, 8, 14, -13, 9]

def test28_a : Array Int := #[-6, -11, 18, 1, -15, 20, -13, 9, 0, 4, -19, -17, 4, -2, -9, -16, -17, -14, -15, -7]
def test28_j : Nat := 11
def test28_Expected : Array Int := #[-6, -11, 18, 1, -15, 20, -13, 9, 0, 4, -19, 60, 4, -2, -9, -16, -17, -14, -15, -7]

def test29_a : Array Int := #[-3, 9, -11, 9, -12, 16, -12, -4, 9, -4, 10, 10, -13, -9, 5, -11, -12, -1, 1]
def test29_j : Nat := 14
def test29_Expected : Array Int := #[-3, 9, -11, 9, -12, 16, -12, -4, 9, -4, 10, 10, -13, -9, 60, -11, -12, -1, 1]

def test30_a : Array Int := #[3, 18, 16, 15, -17, 3, 0, 3, 10, -5, 10, -16, 15, -10, -3]
def test30_j : Nat := 6
def test30_Expected : Array Int := #[3, 18, 16, 15, -17, 3, 60, 3, 10, -5, 10, -16, 15, -10, -3]

def test31_a : Array Int := #[0, 19, -3, 9, 0, 8, 1, -9, -18, -15, -17, -4, -7, 10, -10, -4]
def test31_j : Nat := 3
def test31_Expected : Array Int := #[0, 19, -3, 60, 0, 8, 1, -9, -18, -15, -17, -4, -7, 10, -10, -4]

def test32_a : Array Int := #[1, -16, 5, -19, -2, -13, -7, -12, 6, 4]
def test32_j : Nat := 9
def test32_Expected : Array Int := #[1, -16, 5, -19, -2, -13, -7, -12, 6, 60]

def test33_a : Array Int := #[-8, -8, 17, 16, -9]
def test33_j : Nat := 0
def test33_Expected : Array Int := #[60, -8, 17, 16, -9]

def test34_a : Array Int := #[-18, -10, 7, 19, -17, 7, 7, -13, -4, 2, 15, -1, 4, 14]
def test34_j : Nat := 13
def test34_Expected : Array Int := #[-18, -10, 7, 19, -17, 7, 7, -13, -4, 2, 15, -1, 4, 60]

def test35_a : Array Int := #[-11, 13, -1, -1, 6, 5, -15, -14, -13, -17, 11, -4, 15]
def test35_j : Nat := 5
def test35_Expected : Array Int := #[-11, 13, -1, -1, 6, 60, -15, -14, -13, -17, 11, -4, 15]
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test1 (result : Array Int) :
  result ≠ test1_Expected →
  ¬ postcondition test1_a test1_j result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  plausible'_mut (seeds := #[test1_Expected]) (config := { numInst := 100000 })
