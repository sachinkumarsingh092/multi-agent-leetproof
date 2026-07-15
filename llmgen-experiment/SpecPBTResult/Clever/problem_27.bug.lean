import SpecPBTResult.Clever.CleverAllImports
import Velvet.Std
import Extensions.Testing
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem: problem_27

section Specs

register_specdef_allow_recursion

variable (string : String)

def problem_spec
-- function signature
(implementation: String → String)
-- inputs
(string: String) :=
-- spec
let spec (result: String) :=
let chars_in_result := result.toList;
let chars_in_string := string.toList;
chars_in_result.length = string.length ∧
(∀ i, i < chars_in_result.length →
  let c := chars_in_result.get! i;
  let c' := chars_in_string.get! i;
  (c.isUpper → c'.isLower) ∧
  (c.isLower → c'.isUpper) ∧
  ((¬ c.isUpper ∧ ¬ c.isLower) → c = c')
);
-- program termination
∃ result, implementation string = result ∧
spec result

def precondition (string : String) : Prop :=
  True

instance instDecidablePrecond (string : String) : Decidable (precondition string) := by
  unfold precondition
  infer_instance

def postcondition (string : String) (result : String) :=
  let chars_in_result := result.toList;
  let chars_in_string := string.toList;
  chars_in_result.length = string.length ∧
  (∀ i, i < chars_in_result.length →
    let c := chars_in_result.get! i;
    let c' := chars_in_string.get! i;
    (c.isUpper → c'.isLower) ∧
    (c.isLower → c'.isUpper) ∧
    ((¬ c.isUpper ∧ ¬ c.isLower) → c = c')
  )

end Specs

section Impl

def implementation (string: String) : String :=
string.map (λ c => if c.isUpper then c.toLower else c.toUpper)

end Impl

section TestCases

def test1_string : String := "Hello"
def test1_Expected : String := "hELLO"

def test2_string : String := ""
def test2_Expected : String := ""

def test3_string : String := "2\x12;\x10;"
def test3_Expected : String := "2\x12;\x10;"

def test4_string : String := "cA,1\x00cc1/"
def test4_Expected : String := "Ca,1\x00CC1/"

def test5_string : String := ""
def test5_Expected : String := ""

def test6_string : String := "2`: 1;\x0c:"
def test6_Expected : String := "2`: 1;\x0c:"

def test7_string : String := "A\x0e/\x04B\x033cc`\x01:23BA\x0c"
def test7_Expected : String := "a\x0e/\x04b\x033CC`\x01:23ba\x0c"

def test8_string : String := "0\x000AB/\x011,Ba\x05`1B \\A"
def test8_Expected : String := "0\x000ab/\x011,bA\x05`1b \\a"

def test9_string : String := "\\A/b/Ac\\\x03`\x121\\;c"
def test9_Expected : String := "\\a/B/aC\\\x03`\x121\\;C"

def test10_string : String := "CB;\\\x11,\\21Ac;B\x10a\x03\x082cb"
def test10_Expected : String := "cb;\\\x11,\\21aC;b\x10A\x03\x082CB"

def test11_string : String := " \x0b3\t0a"
def test11_Expected : String := " \x0b3\t0A"

def test12_string : String := "2c::"
def test12_Expected : String := "2C::"

def test13_string : String := "0\x07``2\\;3"
def test13_Expected : String := "0\x07``2\\;3"

def test14_string : String := "\x0eb\x03b/\\12:,,0 "
def test14_Expected : String := "\x0eB\x03B/\\12:,,0 "

def test15_string : String := "02c0A\x0f0"
def test15_Expected : String := "02C0a\x0f0"

def test16_string : String := ":/c \\:"
def test16_Expected : String := ":/C \\:"
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test1 (result : String) :
  result ≠ test1_Expected →
  ¬ postcondition test1_string result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  plausible'_mut (seeds := #[test1_Expected]) (config := { numInst := 100000 })
