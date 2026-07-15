import Velvet.Std
import Extensions.Testing
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem: UpdateElements

section Specs

register_specdef_allow_recursion

def precondition (a : Array Int) : Prop :=
  a.size ≥ 8

instance instDecidablePrecond (a : Array Int) : Decidable (precondition a) := by
  unfold precondition
  infer_instance

def postcondition (a : Array Int) (result : Array Int) :=
  result[4]! = (a[4]!) + 3 ∧
result[7]! = 516 ∧
(∀ i, i < a.size → i ≠ 4 → i ≠ 7 → result[i]! = a[i]!)

end Specs

section Impl

def UpdateElements (a : Array Int) : Array Int :=
  let a1 := a.set! 4 ((a[4]!) + 3)
  let a2 := a1.set! 7 516
  a2

end Impl

section TestCases

def test1_a : Array Int := #[0, 1, 2, 3, 4, 5, 6, 7, 8]
def test1_Expected : Array Int := #[0, 1, 2, 3, 7, 5, 6, 516, 8]

def test2_a : Array Int := #[10, 20, 30, 40, 50, 60, 70, 80]
def test2_Expected : Array Int := #[10, 20, 30, 40, 53, 60, 70, 516]

def test3_a : Array Int := #[-1, -2, -3, -4, -5, -6, -7, -8, -9, -10]
def test3_Expected : Array Int := #[-1, -2, -3, -4, -2, -6, -7, 516, -9, -10]

def test4_a : Array Int := #[0, 0, 0, 0, 0, 0, 0, 0]
def test4_Expected : Array Int := #[0, 0, 0, 0, 3, 0, 0, 516]

def test5_a : Array Int := #[5, 5, 5, 5, 5, 5, 5, 5]
def test5_Expected : Array Int := #[5, 5, 5, 5, 8, 5, 5, 516]

def test6_a : Array Int := #[-2, 20, 20, 3, 4, -13, 14, -9, -17, -18, -15, -9, -10]
def test6_Expected : Array Int := #[-2, 20, 20, 3, 7, -13, 14, 516, -17, -18, -15, -9, -10]

def test7_a : Array Int := #[14, 2, -15, 1, 4, 20, -8, -6, 10, -18, 6, -10, 1, -4, -1, -5, -15, -1, -3]
def test7_Expected : Array Int := #[14, 2, -15, 1, 7, 20, -8, 516, 10, -18, 6, -10, 1, -4, -1, -5, -15, -1, -3]

def test8_a : Array Int := #[19, -12, -3, 18, 9, 20, -5, -1, -19, 11, -17, -6, 12]
def test8_Expected : Array Int := #[19, -12, -3, 18, 12, 20, -5, 516, -19, 11, -17, -6, 12]

def test9_a : Array Int := #[-19, -20, 2, -17, 4, 12, 0, 11, 10, 16, 2, -5, -16, -10, -17, 12, -4, 2]
def test9_Expected : Array Int := #[-19, -20, 2, -17, 7, 12, 0, 516, 10, 16, 2, -5, -16, -10, -17, 12, -4, 2]

def test10_a : Array Int := #[-3, -8, 2, 15, 19, -5, -4, -2, 16]
def test10_Expected : Array Int := #[-3, -8, 2, 15, 22, -5, -4, 516, 16]

def test11_a : Array Int := #[-19, -17, -20, -6, -7, 6, -8, -11, 13]
def test11_Expected : Array Int := #[-19, -17, -20, -6, -4, 6, -8, 516, 13]

def test12_a : Array Int := #[16, 4, -6, -11, -1, 18, -17, 0, -18, 20, -1, -15, -3, 18, -19, -6, 3, 10]
def test12_Expected : Array Int := #[16, 4, -6, -11, 2, 18, -17, 516, -18, 20, -1, -15, -3, 18, -19, -6, 3, 10]

def test13_a : Array Int := #[-7, 1, 9, -20, 16, -3, -10, -3, -10, -12]
def test13_Expected : Array Int := #[-7, 1, 9, -20, 19, -3, -10, 516, -10, -12]

def test14_a : Array Int := #[-3, -10, -7, -18, -17, -10, 19, 11, 13, -3, 15, -1, -4, 0, -10]
def test14_Expected : Array Int := #[-3, -10, -7, -18, -14, -10, 19, 516, 13, -3, 15, -1, -4, 0, -10]

def test15_a : Array Int := #[20, -17, 8, -20, 19, 17, -12, -5, 5, 14, -1, -12, 9, -8, 20, 4, 13, 5, -19]
def test15_Expected : Array Int := #[20, -17, 8, -20, 22, 17, -12, 516, 5, 14, -1, -12, 9, -8, 20, 4, 13, 5, -19]

def test16_a : Array Int := #[8, -5, -11, 5, 7, -4, 18, 7, 5, -7, -16, 6, -3, 3, -19]
def test16_Expected : Array Int := #[8, -5, -11, 5, 10, -4, 18, 516, 5, -7, -16, 6, -3, 3, -19]

def test17_a : Array Int := #[15, -19, -20, 14, 13, -13, -20, 19, -16, 17, 9]
def test17_Expected : Array Int := #[15, -19, -20, 14, 16, -13, -20, 516, -16, 17, 9]

def test18_a : Array Int := #[-10, 6, -17, 15, 4, -18, 2, -11, 9, -12]
def test18_Expected : Array Int := #[-10, 6, -17, 15, 7, -18, 2, 516, 9, -12]

def test19_a : Array Int := #[-17, -20, 1, -7, -1, -19, -20, 18, -20, 6, -8, 17, 0]
def test19_Expected : Array Int := #[-17, -20, 1, -7, 2, -19, -20, 516, -20, 6, -8, 17, 0]

def test20_a : Array Int := #[12, -19, -15, 9, 9, -13, 19, -14, -5, 9, 14, -10, 16, 0, 11, -6, 2, 4, 17, 18]
def test20_Expected : Array Int := #[12, -19, -15, 9, 12, -13, 19, 516, -5, 9, 14, -10, 16, 0, 11, -6, 2, 4, 17, 18]

def test21_a : Array Int := #[-2, 1, 2, 20, -2, 13, 3, -11, -16, -9, -11, -1, 8, 18, 0, 15, 10, -9, 8, -13]
def test21_Expected : Array Int := #[-2, 1, 2, 20, 1, 13, 3, 516, -16, -9, -11, -1, 8, 18, 0, 15, 10, -9, 8, -13]

def test22_a : Array Int := #[3, 14, -16, 11, 4, 16, 20, 2, 3, 14, 17, 0, 7, -11, -8]
def test22_Expected : Array Int := #[3, 14, -16, 11, 7, 16, 20, 516, 3, 14, 17, 0, 7, -11, -8]

def test23_a : Array Int := #[-17, 3, -16, -7, 17, 16, 10, 10, -2, 1, -12, -12, -17, 9, -18]
def test23_Expected : Array Int := #[-17, 3, -16, -7, 20, 16, 10, 516, -2, 1, -12, -12, -17, 9, -18]

def test24_a : Array Int := #[20, 12, -20, 1, 15, 7, -8, 4, -12, 10, 20, 4, -18, -5, 13, -5, -1, 8, -16]
def test24_Expected : Array Int := #[20, 12, -20, 1, 18, 7, -8, 516, -12, 10, 20, 4, -18, -5, 13, -5, -1, 8, -16]

def test25_a : Array Int := #[12, -17, -1, 7, 19, 16, 3, 12, -18, 14, 9, 0, 3, -20, -20, -15, -8, -4]
def test25_Expected : Array Int := #[12, -17, -1, 7, 22, 16, 3, 516, -18, 14, 9, 0, 3, -20, -20, -15, -8, -4]

def test26_a : Array Int := #[-18, 17, -18, -1, 1, -9, 0, 9, -18, 17, -1, 11]
def test26_Expected : Array Int := #[-18, 17, -18, -1, 4, -9, 0, 516, -18, 17, -1, 11]

def test27_a : Array Int := #[9, -5, -17, -15, -16, -11, 9, 8, 20, 20, 11, 1, -1, 6, -13, -12, 20, 0, 2, 0]
def test27_Expected : Array Int := #[9, -5, -17, -15, -13, -11, 9, 516, 20, 20, 11, 1, -1, 6, -13, -12, 20, 0, 2, 0]

def test28_a : Array Int := #[2, 7, -18, 12, 2, -7, 9, -12, -17, 7, 20, 0, 1, -2, 1, 4, -11]
def test28_Expected : Array Int := #[2, 7, -18, 12, 5, -7, 9, 516, -17, 7, 20, 0, 1, -2, 1, 4, -11]

def test29_a : Array Int := #[18, -20, -10, 1, 14, -5, 9, -10, -10, 2, -20, -20, 20, 4]
def test29_Expected : Array Int := #[18, -20, -10, 1, 17, -5, 9, 516, -10, 2, -20, -20, 20, 4]

def test30_a : Array Int := #[-5, 15, -10, -11, 17, -2, -20, 0, 3, -5, 9, 13, -7, 7, 19, 1, -9, 1, 7, 16]
def test30_Expected : Array Int := #[-5, 15, -10, -11, 20, -2, -20, 516, 3, -5, 9, 13, -7, 7, 19, 1, -9, 1, 7, 16]

def test31_a : Array Int := #[-11, -17, 6, -7, -2, -16, -15, 3, 12, 14, -13]
def test31_Expected : Array Int := #[-11, -17, 6, -7, 1, -16, -15, 516, 12, 14, -13]

def test32_a : Array Int := #[15, -8, 5, -6, 4, 12, -15, 9, 17, -5, -5, 12, 3, -17, 14, -9]
def test32_Expected : Array Int := #[15, -8, 5, -6, 7, 12, -15, 516, 17, -5, -5, 12, 3, -17, 14, -9]

def test33_a : Array Int := #[-16, 8, 8, -10, -13, 5, 9, -3, -5, 8, 20, -20, 14, -7, 13]
def test33_Expected : Array Int := #[-16, 8, 8, -10, -10, 5, 9, 516, -5, 8, 20, -20, 14, -7, 13]

def test34_a : Array Int := #[-9, -9, -6, -11, 2, 4, 7, -10, -10, 17, 3, 4, 7, -12, -10, 9, -19, -6]
def test34_Expected : Array Int := #[-9, -9, -6, -11, 5, 4, 7, 516, -10, 17, 3, 4, 7, -12, -10, 9, -19, -6]

def test35_a : Array Int := #[-7, 2, 20, -6, 15, -20, -6, -18]
def test35_Expected : Array Int := #[-7, 2, 20, -6, 18, -20, -6, 516]
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test1 (result : Array Int) :
  result ≠ test1_Expected →
  ¬ postcondition test1_a result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  plausible'_mut (seeds := #[test1_Expected]) (config := { numInst := 100000 })
