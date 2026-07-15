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
    ContainsZOrZ: Determine whether an input string contains the character 'z' or 'Z'.
    Natural language breakdown:
    1. The input is a string (a finite sequence of characters), possibly empty.
    2. The output is a Boolean value.
    3. The output is true exactly when the input contains at least one character equal to 'z' or equal to 'Z'.
    4. The output is false exactly when the input contains neither 'z' nor 'Z'.
    5. There are no preconditions: the method accepts any string.
-/

section Specs
-- Helper: view a string as the list of its characters.
-- Note: we keep the method interface as String to match the problem statement.
def toChars (s : String) : List Char :=
  s.data

def hasZ (s : String) : Prop :=
  ('z' ∈ toChars s) ∨ ('Z' ∈ toChars s)

def precondition (s : String) : Prop :=
  True

def postcondition (s : String) (result : Bool) : Prop :=
  (result = true ↔ hasZ s)
end Specs

section Impl
method ContainsZOrZ (s : String) return (result : Bool)
  require precondition s
  ensures postcondition s result
  do
    -- Convert once at the top if an implementation wants to operate on characters.
    let _cs : List Char := s.data
    pure false  -- placeholder body

end Impl

section TestCases
-- Test case 1: empty string
def test1_s : String := ""
def test1_Expected : Bool := false

-- Test case 2: singleton lowercase 'z'
def test2_s : String := "z"
def test2_Expected : Bool := true

-- Test case 3: singleton uppercase 'Z'
def test3_s : String := "Z"
def test3_Expected : Bool := true

-- Test case 4: no z/Z present
def test4_s : String := "abc"
def test4_Expected : Bool := false

-- Test case 5: contains lowercase 'z' in the middle
def test5_s : String := "azb"
def test5_Expected : Bool := true

-- Test case 6: contains uppercase 'Z' at the end
def test6_s : String := "xyZ"
def test6_Expected : Bool := true

-- Test case 7: contains both 'z' and 'Z'
def test7_s : String := "zZ"
def test7_Expected : Bool := true

-- Test case 8: characters near but not equal to z/Z
def test8_s : String := "y{Y"
def test8_Expected : Bool := false

-- Test case 9: multiple occurrences of lowercase 'z'
def test9_s : String := "zazb"
def test9_Expected : Bool := true

-- Recommend to validate: empty input, singleton z/Z, mixed-case occurrences
end TestCases
