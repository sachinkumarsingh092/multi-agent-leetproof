import SpecPBTResult.Clever.CleverAllImports
import Velvet.Std
import Extensions.Testing
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem: problem_79

section Specs

register_specdef_allow_recursion

def problem_spec
-- function signature
(implementation: Nat → String)
-- inputs
(decimal: Nat) :=
-- spec
let spec (result: String) :=
  4 < result.length ∧
  result.drop (result.length - 2) = "db" ∧
  result.take 2 = "db" ∧
  let resultTrimmed := (result.toList.drop 2).dropLast.dropLast.map (fun c => c.toNat - '0'.toNat)
  decimal = Nat.ofDigits 2 resultTrimmed.reverse
-- program termination
∃ result, implementation decimal = result ∧
spec result

def precondition (decimal : Nat) : Prop :=
  True

instance instDecidablePrecond (decimal : Nat) : Decidable (precondition decimal) := by
  unfold precondition
  infer_instance

def postcondition (decimal : Nat) (result : String) :=
  4 < result.length ∧
    result.drop (result.length - 2) = "db" ∧
    result.take 2 = "db" ∧
    let resultTrimmed := (result.toList.drop 2).dropLast.dropLast.map (fun c => c.toNat - '0'.toNat)
    decimal = Nat.ofDigits 2 resultTrimmed.reverse

end Specs

section Impl

def implementation (decimal: Nat) : String :=
"db" ++ (Nat.toDigits 2 decimal).asString ++ "db"

end Impl

section TestCases

def test1_decimal : Nat := 15
def test1_Expected : String := "db1111db"

def test2_decimal : Nat := 32
def test2_Expected : String := "db100000db"

def test3_decimal : Nat := 11
def test3_Expected : String := "db1011db"

def test4_decimal : Nat := 8
def test4_Expected : String := "db1000db"

def test5_decimal : Nat := 18
def test5_Expected : String := "db10010db"

def test6_decimal : Nat := 1
def test6_Expected : String := "db1db"

def test7_decimal : Nat := 18
def test7_Expected : String := "db10010db"

def test8_decimal : Nat := 6
def test8_Expected : String := "db110db"

def test9_decimal : Nat := 6
def test9_Expected : String := "db110db"

def test10_decimal : Nat := 14
def test10_Expected : String := "db1110db"

def test11_decimal : Nat := 3
def test11_Expected : String := "db11db"

def test12_decimal : Nat := 17
def test12_Expected : String := "db10001db"

def test13_decimal : Nat := 14
def test13_Expected : String := "db1110db"

def test14_decimal : Nat := 18
def test14_Expected : String := "db10010db"

def test15_decimal : Nat := 3
def test15_Expected : String := "db11db"

def test16_decimal : Nat := 20
def test16_Expected : String := "db10100db"

def test17_decimal : Nat := 4
def test17_Expected : String := "db100db"
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test2 (result : String) :
  result ≠ test2_Expected →
  ¬ postcondition test2_decimal result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  plausible'_mut (seeds := #[test2_Expected]) (config := { numInst := 100000 })
