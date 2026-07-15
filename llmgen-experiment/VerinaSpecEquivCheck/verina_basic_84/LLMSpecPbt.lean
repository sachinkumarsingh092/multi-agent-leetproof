import Velvet.Std
import Extensions.Tactics
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false
set_option pp.funBinderTypes true
set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

/- Problem Description
    ReplaceAboveThreshold: Create a new array where elements greater than a threshold k are replaced by -1.
    Natural language breakdown:
    1. Input is an array of integers arr and an integer threshold k.
    2. The output is an array of integers with the same size as arr.
    3. For each valid index i:
       a. If arr[i] > k, then output[i] = -1.
       b. If arr[i] ≤ k, then output[i] = arr[i].
    4. The input array may be empty; k may be any integer.
    5. There are no additional preconditions.
-/

section Specs
def precondition (arr : Array Int) (k : Int) : Prop :=
  True

def postcondition (arr : Array Int) (k : Int) (result : Array Int) : Prop :=
  result.size = arr.size ∧
  (∀ (i : Nat), i < arr.size →
    result[i]! = (if arr[i]! > k then (-1 : Int) else arr[i]!))
end Specs

section Impl
method ReplaceAboveThreshold (arr : Array Int) (k : Int)
  return (result : Array Int)
  require precondition arr k
  ensures postcondition arr k result
  do
  pure arr

prove_correct ReplaceAboveThreshold by sorry
end Impl

section TestCases
-- Test case 1: typical mix around threshold
def test1_arr : Array Int := #[1, 5, 3, 8]
def test1_k : Int := 4
def test1_Expected : Array Int := #[1, -1, 3, -1]

-- Test case 2: empty array
def test2_arr : Array Int := #[]
def test2_k : Int := 0
def test2_Expected : Array Int := #[]

-- Test case 3: singleton, value greater than k
def test3_arr : Array Int := #[10]
def test3_k : Int := 9
def test3_Expected : Array Int := #[-1]

-- Test case 4: singleton, value equal to k (kept)
def test4_arr : Array Int := #[7]
def test4_k : Int := 7
def test4_Expected : Array Int := #[7]

-- Test case 5: includes -1, 0, 1; threshold 0
def test5_arr : Array Int := #[-1, 0, 1]
def test5_k : Int := 0
def test5_Expected : Array Int := #[-1, 0, -1]

-- Test case 6: all values ≤ k (unchanged)
def test6_arr : Array Int := #[-5, -2, 0, 3]
def test6_k : Int := 10
def test6_Expected : Array Int := #[-5, -2, 0, 3]

-- Test case 7: all values > k (all replaced)
def test7_arr : Array Int := #[2, 3, 4]
def test7_k : Int := 1
def test7_Expected : Array Int := #[-1, -1, -1]

-- Test case 8: negative threshold
def test8_arr : Array Int := #[-10, -3, 0, 2]
def test8_k : Int := (-4)
def test8_Expected : Array Int := #[-10, -1, -1, -1]

-- Test case 9: k very small (everything replaced except possibly very negative)
def test9_arr : Array Int := #[-100, -1, 0, 100]
def test9_k : Int := (-50)
def test9_Expected : Array Int := #[-100, -1, -1, -1]
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test9' (result : Array Int) :
  result ≠ test9_Expected →
  ¬ postcondition test9_arr test9_k result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test9_Expected]) (config := { numInst := 100000 })
