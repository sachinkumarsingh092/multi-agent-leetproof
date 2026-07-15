import SpecPBTResult.Clever.CleverAllImports
import Velvet.Std
import Extensions.Testing
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem: problem_29

section Specs

register_specdef_allow_recursion

def problem_spec
-- function signature
(implementation: List String → String → List String)
-- inputs
(strings: List String)
(pref: String) :=
-- spec
let spec (result: List String) :=
result.all (λ s => s.startsWith pref) ∧
result.all (λ s => s ∈ strings) ∧
strings.all (λ s => s.startsWith pref → s ∈ result) ∧
∀ s : String, s ∈ result → result.count s = strings.count s;
-- program termination
∃ result, implementation strings pref = result ∧
spec result

def precondition (strings : List String) (pref : String) : Prop :=
  True

instance instDecidablePrecond (strings : List String) (pref : String) : Decidable (precondition strings pref) := by
  unfold precondition
  infer_instance

def postcondition (strings : List String) (pref : String) (result : List String) :=
  result.all (λ s => s.startsWith pref) ∧
  result.all (λ s => s ∈ strings) ∧
  strings.all (λ s => s.startsWith pref → s ∈ result) ∧
  ∀ s : String, s ∈ result →
    result.count s = strings.count s

end Specs

section Impl

def implementation (strings: List String) (pref: String) : List String :=
strings.filter (λ s => s.startsWith pref)

end Impl

section TestCases

def test1_strings : List String := []
def test1_pref : String := "a"
def test1_Expected : List String := []

def test2_strings : List String := ["abc", "bcd", "cde", "array"]
def test2_pref : String := "a"
def test2_Expected : List String := ["abc", "array"]

def test3_strings : List String := ["\x02`c \x0d:\x01/\\23C:/0", "bC\x0fB\\,C\t02`", "\n\x0b1\x0e", "3", "\x07,\x0bab",":\x0e3\x11\x07,\x0e\x03B\x14\x03:/A0", "\n\x13C 0\x0f1c,\x073`\x12/CC\\:3\n", "\x13B0\\", " 0b 3C\x11b3AB","\x0c3B`\x11CB`\x0cb0,\n"]
def test3_pref : String := "b\x0eAb\x003ab3A;"
def test3_Expected : List String := []

def test4_strings : List String := [":B;33a\t1a;", "\\", "b`bCCA\x14/\x13\x06/\x0e", "2", "\x07:1\x14C\x06AB\x05/A/\x14`"]
def test4_pref : String := "/  \\\x0e;A01`,\\;\\3,b,\x0f"
def test4_Expected : List String := []

def test5_strings : List String := ["\x031c11\t,`,c;,`", "`C,\x13\t;3aA\x06;\x02`\x02", "\x0e:c;", "b\x0f\x11;\\a\x11\\\x1132:,;A/`\\Aa","1\x08B`\x11\x0032\x012\\\nB b2/,/", "\x0b:0\n1c\x02\t\x04ab\x11B\x0f", "`0\x05b\\", "A", "c\n1","``\\\x10 \x00`\x12C\x0d\\", ":/\x0c33\x11A:C\x0b`/,:\x03", "\x0d`\x053:\x0f\x0f\\;\x0d \x13\x13a:ba0\t"]
def test5_pref : String := "3b"
def test5_Expected : List String := []

def test6_strings : List String := ["\x13\\ b\x07a,:\x0fC,;", "`0`C`B:0\x0f\x02\x07\x03Bc2c\x10;", " /\x040\x08acc; ", "3/ :aB 300", "A:c`c","\x143;\x0db001\t", ", \x0f", "", "1\x0d,\x10", "1\x0d\\; CB\x04B\x02B1,C", "`0b","\x13 \x0130\x10//A0:Ba\x0b\x0b`c\x0d\x0bc", "2\x00C0`2,\x14 c\t\x033 A\x02", "1 2`2", "b\\c3\x00Ab\x02 \x0b","\x03\x0d\x11b\x0cB\x04\\A\\c", ";Ab0C`C;\x10", "bbC\x12\x123C\x0d0\x0d3\x0eC \x030C,\t"]
def test6_pref : String := "\x10Bacc3\x0e\x0ea\\"
def test6_Expected : List String := []

def test7_strings : List String := ["0", "\x11\nA\x10b\x08B1\n\tA\x02\x0d3c", "0Cb1;\x10/", "\x0e/A1\x12`\x0b\x14`1","\x01,\x00\x12\x07baC\x07\x10\\Ca/a1;\x01\n", "B", "c0;\x0fAAbB1c`C\x040B\\", "/\x0fC;\x053A\x0b`C","\x01B\x14\x141CA;bbCB", "\x07", ";\x03\\:,A\x0b\x083`\x14B\\\x08", "/AB\x04`1A;0\x1121"]
def test7_pref : String := "A 1C"
def test7_Expected : List String := []

def test8_strings : List String := ["\x04,1a\x11\\;B\x13C 0\tB,\x11\x01/"]
def test8_pref : String := ",1"
def test8_Expected : List String := []

def test9_strings : List String := ["B`\x06/,;a b\\,BA/B1aCBC", "3C1`C0\x12A\x11\x0c\t:BA`,", "C/::\x01B33`", "2a;/0CC0 :\x12\x13\x02`B `","/a`/b\x0eaa;1ab\x11\x0c/02\t/B", "A2B,CB", "\x08\x04 \x10B `\n\x0b\x14\x12,c", "", "3\x11\x14\x0bc","C\\\x01\x0bAcC /;`a`b\n;", ":,2\x04b 1`,\x13\x103\x12\tB\x10\x10"]
def test9_pref : String := "0\x00\x05\x10C"
def test9_Expected : List String := []

def test10_strings : List String := ["`;:;\x0b\x07,b\\02`\x14\x0e2,`", "\x0cAA, `Ca\\\x02\x0d`\\a0\x0d\\\x14", "/b\x04\x132Ac0 \x12\x082\x0dA ,\\C\x03","\\a\x08, 322bc3\x05/0b", "", "\x06\x10\x0d:\x10:\x0dcb`\x050/`cc\x0c0\\", ";c\x08aA`A1C\x02\x06\x010B, \x13\x002","c`2\x03\x14\x0b\x030;\x12C;", " \t0c\x07\x04A0B\x0b\x01:1A\x01", "a//,cB3\nC\x0b0", ",B;B","CA\n\x03bBAAA\x031\n1\x10\x14", "BABc\\\x00", ";0\x0f 0Ac\x0e/cc\x10:A;c", "\x14aC\x04a\x11A\x08 B0c \n\x130","c`:B\x04Ab;\x0f", "\x14B", " 3b22 , A,;c", "\n0\x11:"]
def test10_pref : String := "3"
def test10_Expected : List String := []

def test11_strings : List String := ["\x13/\t\x03`B 21A\x0b\x10A/0", "\\\\\x10", "`3A  2\x00 ", "A;b`3bB B:aa/ 2", "/b\x13", "3:\\B2a/\x13\x052\\22","\x08\x0831a\\a/c\x14", "\x0f\x02\\\x02a\x10\x0d1/3\t,\x10c", ":\t\x01:c`/a,cA", "2:\x12\x001;ca:33\x0c2\x05", "c,3:"]
def test11_pref : String := "`\x0c\x1121\x0bB\x0f//3/"
def test11_Expected : List String := []

def test12_strings : List String := ["c1C", "2\x0ecc1C;", "\x0bcC ;1,c/0:3\x00A\x0fAC ", "\x01\x01B1`1\x0d3B,::", "\x06 \x0dab\x07\x030\x06cC"]
def test12_pref : String := "0,Cc\\/\x112/\x06 03"
def test12_Expected : List String := []

def test13_strings : List String := ["1c\tB\x0ea;\\c\x00/A", "cC\x03", "CC02\x0621", "\x02B\x14\x13abb/\tB,C2\x0f;;`\\2", "\x12", "`\x12 \x02\x12","\x10AB", "A\x13\x0c3 /b0AA"]
def test13_pref : String := "2\x12` /20\x12\x0fB\x08A`\x0f\x003"
def test13_Expected : List String := []

def test14_strings : List String := ["\x0ecc\x00", "A00/;", "3bC", " 3b", "c"]
def test14_pref : String := "2B\x12`\x031\\CABBC;\x05\t\t "
def test14_Expected : List String := []

def test15_strings : List String := ["\x0f`c`\x01A`` ` \\\\ ", "B:3 0A\x121c3\x14B\x13\x03\x0f", "Aaca:A1023B\n\x04A\t\x12a\x11/", "\\","1\x06\x04/\x04A\x0b2a,\x03;", "1c", "", "`\x03\x0c2", "32\x0fa3:", ",\\B,,\tA 0\x0d,\x01\x07`", ":1","1/\t\x0d\x08/3c\x13/BB\x07", "3Ba1c11\x00\\CAc3\x06;", "AAC\x0e1\x0c\x02 B01", "0\x05`C","b\x04\x0db \n0\\\x02B2cc:\x0e3\x0e", " :\x04\x0e", "3 b\x14A"]
def test15_pref : String := "/bCb,0\\A,  0`1\x12b;A\x07b"
def test15_Expected : List String := []

def test16_strings : List String := ["1b", "/\x03a\x0c", "C23B1\x04 C1\x06\t31\x14,0", "C3\x01\t1\\0", "2;;\x13\\\x0c;1B1a:1B2", "\x02,a\x130\x11","0\x0bA\\\t", ",;a\x07"]
def test16_pref : String := "\x02C20;C\x0d/`;0Ca/`B"
def test16_Expected : List String := []

def test17_strings : List String := [",``3\x01`BC\x00\x00", "3\\/\x0b\x04C;\x082;\x02/,\x102 1A ", "", "aA\x02\x12310\x06aC \x05", "2\x0733","2\x083\x04\x11", "\x05\x11a`a0\n\x0b;2\x11\x130:", "bB,3;``\x06:B;1\n`", "AAa,\x07\x0ca\\Bb2\t3/  3\x0ec:", ";:","\\;\x04B C,3\x05B", "C", ";b/B:2\x0c,c :\x0c1:aC\\ ", "2;1\x13::,"]
def test17_pref : String := "3aa::\x13,C\\C31a "
def test17_Expected : List String := []
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test2 (result : List String) :
  result ≠ test2_Expected →
  ¬ postcondition test2_strings test2_pref result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  plausible'_mut (seeds := #[test2_Expected]) (config := { numInst := 10000 })
