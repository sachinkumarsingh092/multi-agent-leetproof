import Velvet.Std
import Extensions.Testing
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem: replace

section Specs

register_specdef_allow_recursion

def precondition (arr : Array Int) (k : Int) : Prop :=
  True

instance instDecidablePrecond (arr : Array Int) (k : Int) : Decidable (precondition arr k) := by
  unfold precondition
  infer_instance

def postcondition (arr : Array Int) (k : Int) (result : Array Int) :=
  (∀ i : Nat, i < arr.size → (arr[i]! > k → result[i]! = -1)) ∧
(∀ i : Nat, i < arr.size → (arr[i]! ≤ k → result[i]! = arr[i]!))

end Specs

section Impl

def replace_loop (oldArr : Array Int) (k : Int) : Nat → Array Int → Array Int
| i, acc =>
  if i < oldArr.size then
    if (oldArr[i]!) > k then
      replace_loop oldArr k (i+1) (acc.set! i (-1))
    else
      replace_loop oldArr k (i+1) acc
  else
    acc

def replace (arr : Array Int) (k : Int) : Array Int :=
  replace_loop arr k 0 arr

end Impl

section TestCases

def test1_arr : Array Int := #[1, 5, 3, 10]
def test1_k : Int := 4
def test1_Expected : Array Int := #[1, -1, 3, -1]

def test2_arr : Array Int := #[-1, 0, 1, 2]
def test2_k : Int := 2
def test2_Expected : Array Int := #[-1, 0, 1, 2]

def test3_arr : Array Int := #[100, 50, 100]
def test3_k : Int := 100
def test3_Expected : Array Int := #[100, 50, 100]

def test4_arr : Array Int := #[-5, -2, 0, 3]
def test4_k : Int := -3
def test4_Expected : Array Int := #[-5, -1, -1, -1]

def test5_arr : Array Int := #[1, 2, 3]
def test5_k : Int := 5
def test5_Expected : Array Int := #[1, 2, 3]

def test6_arr : Array Int := #[13, 11, -10, 0, 10, -16, 8, -2, 1, -13, 20, -2]
def test6_k : Int := 13
def test6_Expected : Array Int := #[13, 11, -10, 0, 10, -16, 8, -2, 1, -13, -1, -2]

def test7_arr : Array Int := #[7, -8, 8, -4, 19, -2, -17, 0, 12, 0, -15, -3, -10, 10, -14, -14]
def test7_k : Int := 18
def test7_Expected : Array Int := #[7, -8, 8, -4, -1, -2, -17, 0, 12, 0, -15, -3, -10, 10, -14, -14]

def test8_arr : Array Int := #[12, -5, -5, -2, 0, -13, 15, 15, 2, 12, -4]
def test8_k : Int := -12
def test8_Expected : Array Int := #[-1, -1, -1, -1, -1, -13, -1, -1, -1, -1, -1]

def test9_arr : Array Int := #[6, 5, 9, -8, -19, 13, -8, -1, 0, -10, 9, 15, 14, 12, -15, -12, 18]
def test9_k : Int := 15
def test9_Expected : Array Int := #[6, 5, 9, -8, -19, 13, -8, -1, 0, -10, 9, 15, 14, 12, -15, -12, -1]

def test10_arr : Array Int := #[-5, 13, -12, 9, 11, -12, 12, 3, 11, 3, 0, -7, -17, -20, 0, -9, -11, -11]
def test10_k : Int := 20
def test10_Expected : Array Int := #[-5, 13, -12, 9, 11, -12, 12, 3, 11, 3, 0, -7, -17, -20, 0, -9, -11, -11]

def test11_arr : Array Int := #[14, 7, -15, 2, -16, -17, -2]
def test11_k : Int := -16
def test11_Expected : Array Int := #[-1, -1, -1, -1, -16, -17, -1]

def test12_arr : Array Int := #[15, 11, 14, 7, -9, -15, -3, -4, 20, -9, 16, 11, -15]
def test12_k : Int := -3
def test12_Expected : Array Int := #[-1, -1, -1, -1, -9, -15, -3, -4, -1, -9, -1, -1, -15]

def test13_arr : Array Int := #[15, -11, -13, -12, -15, 11, 9, -12, -10]
def test13_k : Int := 20
def test13_Expected : Array Int := #[15, -11, -13, -12, -15, 11, 9, -12, -10]

def test14_arr : Array Int := #[-2]
def test14_k : Int := -1
def test14_Expected : Array Int := #[-2]

def test15_arr : Array Int := #[-19, 5, -18, -2, 19, -9, 2, 11, 0, 2]
def test15_k : Int := -13
def test15_Expected : Array Int := #[-19, -1, -18, -1, -1, -1, -1, -1, -1, -1]

def test16_arr : Array Int := #[-7]
def test16_k : Int := -19
def test16_Expected : Array Int := #[-1]

def test17_arr : Array Int := #[3, 7, 6, -6, 9, -13, -19, -3, 8]
def test17_k : Int := -7
def test17_Expected : Array Int := #[-1, -1, -1, -1, -1, -13, -19, -1, -1]

def test18_arr : Array Int := #[-9, 12, -3, -19, 1, 5]
def test18_k : Int := 13
def test18_Expected : Array Int := #[-9, 12, -3, -19, 1, 5]

def test19_arr : Array Int := #[-8, 0, -1, 20]
def test19_k : Int := 3
def test19_Expected : Array Int := #[-8, 0, -1, -1]

def test20_arr : Array Int := #[-18, 6, 19, 11, -5, 10, 1, 2, 1, -16, -4, -20, -11, 18, 16, -6, 5]
def test20_k : Int := -10
def test20_Expected : Array Int := #[-18, -1, -1, -1, -1, -1, -1, -1, -1, -16, -1, -20, -11, -1, -1, -1, -1]

def test21_arr : Array Int := #[12, 2, 4, 11, -2, 11, -7, 14, 8, 11, -5, -11, 15]
def test21_k : Int := -20
def test21_Expected : Array Int := #[-1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1]

def test22_arr : Array Int := #[10, -10, 0, 11, -10]
def test22_k : Int := -9
def test22_Expected : Array Int := #[-1, -10, -1, -1, -10]

def test23_arr : Array Int := #[-6, 2, -8, -14, -10, 4, 18, 14, -20, 9, 17]
def test23_k : Int := 0
def test23_Expected : Array Int := #[-6, -1, -8, -14, -10, -1, -1, -1, -20, -1, -1]

def test24_arr : Array Int := #[-16, -8, -16, 6, -7, -8, -19, 4, 3, 15, -11]
def test24_k : Int := -18
def test24_Expected : Array Int := #[-1, -1, -1, -1, -1, -1, -19, -1, -1, -1, -1]

def test25_arr : Array Int := #[11, 7, -8, -8]
def test25_k : Int := 9
def test25_Expected : Array Int := #[-1, 7, -8, -8]

def test26_arr : Array Int := #[-15, -17, 15, -18]
def test26_k : Int := -1
def test26_Expected : Array Int := #[-15, -17, -1, -18]

def test27_arr : Array Int := #[1, 19, -17, 3, 1, -8]
def test27_k : Int := -8
def test27_Expected : Array Int := #[-1, -1, -17, -1, -1, -8]

def test28_arr : Array Int := #[]
def test28_k : Int := -19
def test28_Expected : Array Int := #[]

def test29_arr : Array Int := #[14, 0, -3, 18, 12, -3, 3, -17, -2, -4, 12, 14, 5, 15]
def test29_k : Int := 13
def test29_Expected : Array Int := #[-1, 0, -3, -1, 12, -3, 3, -17, -2, -4, 12, -1, 5, -1]

def test30_arr : Array Int := #[-11, -11, -16, -13, -9, -14, 11, -7, -6, -3, 19, 7, -20]
def test30_k : Int := -17
def test30_Expected : Array Int := #[-1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -20]

def test31_arr : Array Int := #[19]
def test31_k : Int := -1
def test31_Expected : Array Int := #[-1]

def test32_arr : Array Int := #[2, 1, 8, 8]
def test32_k : Int := 17
def test32_Expected : Array Int := #[2, 1, 8, 8]

def test33_arr : Array Int := #[2, -16, -15, 17, -3, -10, -6, -13, -19, 14, -18, -7, 11]
def test33_k : Int := 6
def test33_Expected : Array Int := #[2, -16, -15, -1, -3, -10, -6, -13, -19, -1, -18, -7, -1]

def test34_arr : Array Int := #[7, -7, 12, 18, 1, 4, 9, 15, -4, 20, -19, -4, 12, -14, -15, 16, -15, -3, -10]
def test34_k : Int := -9
def test34_Expected : Array Int := #[-1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -19, -1, -1, -14, -15, -1, -15, -1, -10]

def test35_arr : Array Int := #[2, 8, 11, 20, -8, -15, 9, 3, -9, 20, -8]
def test35_k : Int := 1
def test35_Expected : Array Int := #[-1, -1, -1, -1, -8, -15, -1, -1, -9, -1, -8]
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test1 (result : Array Int) :
  result ≠ test1_Expected →
  ¬ postcondition test1_arr test1_k result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  plausible'_mut (seeds := #[test1_Expected]) (config := { numInst := 100000 })
