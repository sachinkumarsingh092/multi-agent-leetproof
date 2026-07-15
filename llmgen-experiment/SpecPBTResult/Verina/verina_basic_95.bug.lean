import Velvet.Std
import Extensions.Testing
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem: swap

section Specs

register_specdef_allow_recursion

def precondition (arr : Array Int) (i : Int) (j : Int) : Prop :=
  i ≥ 0 ∧
j ≥ 0 ∧
Int.toNat i < arr.size ∧
Int.toNat j < arr.size

instance instDecidablePrecond (arr : Array Int) (i : Int) (j : Int) : Decidable (precondition arr i j) := by
  unfold precondition
  infer_instance

def postcondition (arr : Array Int) (i : Int) (j : Int) (result : Array Int) :=
  (result[Int.toNat i]! = arr[Int.toNat j]!) ∧
(result[Int.toNat j]! = arr[Int.toNat i]!) ∧
(∀ (k : Nat), k < arr.size → k ≠ Int.toNat i → k ≠ Int.toNat j → result[k]! = arr[k]!)

end Specs

section Impl

def swap (arr : Array Int) (i : Int) (j : Int) : Array Int :=
  let i_nat := Int.toNat i
  let j_nat := Int.toNat j
  let arr1 := arr.set! i_nat (arr[j_nat]!)
  let arr2 := arr1.set! j_nat (arr[i_nat]!)
  arr2

end Impl

section TestCases

def test1_arr : Array Int := #[1, 2, 3, 4, 5]
def test1_i : Int := 1
def test1_j : Int := 3
def test1_Expected : Array Int := #[1, 4, 3, 2, 5]

def test2_arr : Array Int := #[10, 20, 30, 40]
def test2_i : Int := 0
def test2_j : Int := 3
def test2_Expected : Array Int := #[40, 20, 30, 10]

def test3_arr : Array Int := #[7, 8, 9]
def test3_i : Int := 1
def test3_j : Int := 2
def test3_Expected : Array Int := #[7, 9, 8]

def test4_arr : Array Int := #[1, 2, 3, 4]
def test4_i : Int := 0
def test4_j : Int := 0
def test4_Expected : Array Int := #[1, 2, 3, 4]

def test5_arr : Array Int := #[-1, -2, -3]
def test5_i : Int := 0
def test5_j : Int := 2
def test5_Expected : Array Int := #[-3, -2, -1]

def test6_arr : Array Int := #[-8, 3, -1, -11, -18, 5, 4, -18, 8, 18, 15, -9, 12, -17, 14, -12, 12, -17, 7]
def test6_i : Int := 2
def test6_j : Int := 17
def test6_Expected : Array Int := #[-8, 3, -17, -11, -18, 5, 4, -18, 8, 18, 15, -9, 12, -17, 14, -12, 12, -1, 7]

def test7_arr : Array Int := #[-3, 3, -20, -19, -17, 16, 10, -7, -13]
def test7_i : Int := 6
def test7_j : Int := 3
def test7_Expected : Array Int := #[-3, 3, -20, 10, -17, 16, -19, -7, -13]

def test8_arr : Array Int := #[-7, 11, 0, -16, 14, 20, -18, 14, 6, 10, -6, 12]
def test8_i : Int := 9
def test8_j : Int := 3
def test8_Expected : Array Int := #[-7, 11, 0, 10, 14, 20, -18, 14, 6, -16, -6, 12]

def test9_arr : Array Int := #[4, 11, 6, 15, 15, 17, 3, 19, 13, 20, -16, -8, -18, 1, -8]
def test9_i : Int := 0
def test9_j : Int := 6
def test9_Expected : Array Int := #[3, 11, 6, 15, 15, 17, 4, 19, 13, 20, -16, -8, -18, 1, -8]

def test10_arr : Array Int := #[-8, -14, 2, -6, -17, 17, 15, -7, -13, -3, 9, 19, 20, -15, 3, 2, 10]
def test10_i : Int := 1
def test10_j : Int := 11
def test10_Expected : Array Int := #[-8, 19, 2, -6, -17, 17, 15, -7, -13, -3, 9, -14, 20, -15, 3, 2, 10]

def test11_arr : Array Int := #[19, -11, -19, -17, 17, 5, 16, 16, -16, 8, -6, 9, -1, 9, -18, -15, -14, 13, 10, -12]
def test11_i : Int := 12
def test11_j : Int := 1
def test11_Expected : Array Int := #[19, -1, -19, -17, 17, 5, 16, 16, -16, 8, -6, 9, -11, 9, -18, -15, -14, 13, 10, -12]

def test12_arr : Array Int := #[15, -7, 3, 14, 7, 15, 7, 3, 5, -1, -13, -3, -19, 15, -14, -2, -2, -11, -12]
def test12_i : Int := 3
def test12_j : Int := 2
def test12_Expected : Array Int := #[15, -7, 14, 3, 7, 15, 7, 3, 5, -1, -13, -3, -19, 15, -14, -2, -2, -11, -12]

def test13_arr : Array Int := #[10, 2, 9, -1, 0, 4, -20, -9, -12, 12]
def test13_i : Int := 3
def test13_j : Int := 2
def test13_Expected : Array Int := #[10, 2, -1, 9, 0, 4, -20, -9, -12, 12]

def test14_arr : Array Int := #[16, 16, -10, -12, 4, -19, 9, -11, 19]
def test14_i : Int := 4
def test14_j : Int := 3
def test14_Expected : Array Int := #[16, 16, -10, 4, -12, -19, 9, -11, 19]

def test15_arr : Array Int := #[6, 20, 9, -20, -1, 12, -13, 3, -17, -3, -18, 12, 19, -8]
def test15_i : Int := 2
def test15_j : Int := 7
def test15_Expected : Array Int := #[6, 20, 3, -20, -1, 12, -13, 9, -17, -3, -18, 12, 19, -8]

def test16_arr : Array Int := #[-11, -14, -2, -3, -9, -15, -11, 2, -5, -12, 5, 5, -5, 18, 12]
def test16_i : Int := 12
def test16_j : Int := 7
def test16_Expected : Array Int := #[-11, -14, -2, -3, -9, -15, -11, -5, -5, -12, 5, 5, 2, 18, 12]

def test17_arr : Array Int := #[20, -13, 19, 6, 1, -15, -2, -9, 16, -12, 0, -6, -20, 1, 17, 12]
def test17_i : Int := 14
def test17_j : Int := 12
def test17_Expected : Array Int := #[20, -13, 19, 6, 1, -15, -2, -9, 16, -12, 0, -6, 17, 1, -20, 12]

def test18_arr : Array Int := #[-4, 20, -10, 7, -1, 0, 1, 9, -8, 4, 11, -11, -15, 12, -20, -10, -13, 8, 7, 13]
def test18_i : Int := 19
def test18_j : Int := 2
def test18_Expected : Array Int := #[-4, 20, 13, 7, -1, 0, 1, 9, -8, 4, 11, -11, -15, 12, -20, -10, -13, 8, 7, -10]

def test19_arr : Array Int := #[16, -19, -11, 11, -6, 13, -18, -4, -20, 17, -16, -19, 4, -11, 17, 3, 19, 13, 9, -7]
def test19_i : Int := 3
def test19_j : Int := 5
def test19_Expected : Array Int := #[16, -19, -11, 13, -6, 11, -18, -4, -20, 17, -16, -19, 4, -11, 17, 3, 19, 13, 9, -7]

def test20_arr : Array Int := #[19, -18, -20, -16, 2, -8, 15, -19, 9, -4, 17, -17, -18]
def test20_i : Int := 4
def test20_j : Int := 0
def test20_Expected : Array Int := #[2, -18, -20, -16, 19, -8, 15, -19, 9, -4, 17, -17, -18]

def test21_arr : Array Int := #[18, 7, 9, -4, 20, 19, 9, 13, 15, 4, 17, -12, 2, -12, -12, 16]
def test21_i : Int := 2
def test21_j : Int := 12
def test21_Expected : Array Int := #[18, 7, 2, -4, 20, 19, 9, 13, 15, 4, 17, -12, 9, -12, -12, 16]

def test22_arr : Array Int := #[5, 3, 14, 12, 20, -16, -18, -19, -1]
def test22_i : Int := 4
def test22_j : Int := 7
def test22_Expected : Array Int := #[5, 3, 14, 12, -19, -16, -18, 20, -1]

def test23_arr : Array Int := #[15, 16, -2, 3, -11, -3, -5, -9, -4, 0, 2, 5, -9, -20, -9, 18, -19, 18]
def test23_i : Int := 10
def test23_j : Int := 8
def test23_Expected : Array Int := #[15, 16, -2, 3, -11, -3, -5, -9, 2, 0, -4, 5, -9, -20, -9, 18, -19, 18]

def test24_arr : Array Int := #[9, -4, -3, 19, -14]
def test24_i : Int := 1
def test24_j : Int := 2
def test24_Expected : Array Int := #[9, -3, -4, 19, -14]

def test25_arr : Array Int := #[-2, -20, -2, -4, 13, -5, 13, 10, 4, 5, -19, 6, 10, 8, 18, 15, -11]
def test25_i : Int := 9
def test25_j : Int := 4
def test25_Expected : Array Int := #[-2, -20, -2, -4, 5, -5, 13, 10, 4, 13, -19, 6, 10, 8, 18, 15, -11]

def test26_arr : Array Int := #[-7, -19, -6, 19, -3, 12, 7, 10, 16, 18, -11, 12, 16, -11, -6, -6, -12]
def test26_i : Int := 8
def test26_j : Int := 1
def test26_Expected : Array Int := #[-7, 16, -6, 19, -3, 12, 7, 10, -19, 18, -11, 12, 16, -11, -6, -6, -12]

def test27_arr : Array Int := #[-20, 8, 6, 20, -13, -9, -15, 11, -8, -10, 10, 1, -9, -6, 4, -4, -1]
def test27_i : Int := 6
def test27_j : Int := 11
def test27_Expected : Array Int := #[-20, 8, 6, 20, -13, -9, 1, 11, -8, -10, 10, -15, -9, -6, 4, -4, -1]

def test28_arr : Array Int := #[-7, -18, -12, 7, 20, -13, -20, 10]
def test28_i : Int := 0
def test28_j : Int := 1
def test28_Expected : Array Int := #[-18, -7, -12, 7, 20, -13, -20, 10]

def test29_arr : Array Int := #[-14, -20, 4, 11, -1, 9, 16, 9, 5, 6, 6, 13, -4, -10]
def test29_i : Int := 6
def test29_j : Int := 2
def test29_Expected : Array Int := #[-14, -20, 16, 11, -1, 9, 4, 9, 5, 6, 6, 13, -4, -10]

def test30_arr : Array Int := #[5, -1, -2, 12, -9, 18, -12, 14, 11, 11, -8, 14, 13, 19, 18, 2, 18, -18]
def test30_i : Int := 11
def test30_j : Int := 13
def test30_Expected : Array Int := #[5, -1, -2, 12, -9, 18, -12, 14, 11, 11, -8, 19, 13, 14, 18, 2, 18, -18]

def test31_arr : Array Int := #[1, -12, 13, 5, 6, 6, 19, 5, 11, 10, 1, -15, -4, 20]
def test31_i : Int := 10
def test31_j : Int := 2
def test31_Expected : Array Int := #[1, -12, 1, 5, 6, 6, 19, 5, 11, 10, 13, -15, -4, 20]

def test32_arr : Array Int := #[-4, 10, -18, -16, 7, 18, 14, 8, 6, -2, 13, 11, 6, 15, 20, -6, 19, 18, -14, 15]
def test32_i : Int := 6
def test32_j : Int := 13
def test32_Expected : Array Int := #[-4, 10, -18, -16, 7, 18, 15, 8, 6, -2, 13, 11, 6, 14, 20, -6, 19, 18, -14, 15]

def test33_arr : Array Int := #[17, 20, 9, -13, 14, -13]
def test33_i : Int := 2
def test33_j : Int := 3
def test33_Expected : Array Int := #[17, 20, -13, 9, 14, -13]

def test34_arr : Array Int := #[-10, -13, 2, -13, -6, -11, 0, -13, 19, -19, -19, 13, 1, -18, 19, 14, -17, 1, -2]
def test34_i : Int := 4
def test34_j : Int := 15
def test34_Expected : Array Int := #[-10, -13, 2, -13, 14, -11, 0, -13, 19, -19, -19, 13, 1, -18, 19, -6, -17, 1, -2]

def test35_arr : Array Int := #[11, -1, -9, -8, -10, -3, -5, 0, -11, 7, 5, 10, 2, 7, -16, -3, -2]
def test35_i : Int := 15
def test35_j : Int := 11
def test35_Expected : Array Int := #[11, -1, -9, -8, -10, -3, -5, 0, -11, 7, 5, -3, 2, 7, -16, 10, -2]
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test1 (result : Array Int) :
  result ≠ test1_Expected →
  ¬ postcondition test1_arr test1_i test1_j result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  plausible'_mut (seeds := #[test1_Expected]) (config := { numInst := 100000 })
