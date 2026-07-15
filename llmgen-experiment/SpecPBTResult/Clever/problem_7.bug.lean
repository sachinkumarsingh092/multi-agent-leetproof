import SpecPBTResult.Clever.CleverAllImports
import Velvet.Std
import Extensions.Testing
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem: problem_7

section Specs

register_specdef_allow_recursion

def problem_spec
-- function signature
(implementation: List String → String → List String)
-- inputs
(strings: List String)
(substring: String)
:=
-- spec
let spec (result: List String) :=
(∀ i, i < result.length → result[i]!.containsSubstr substring →
∀ j, j < strings.length ∧ strings[j]!.containsSubstr substring → strings[j]! ∈ result →
∀ j, j < result.length → result.count result[j]! = strings.count result[j]!);
-- program termination
∃ result, implementation strings substring = result ∧
spec result

def precondition (strings : List String) (substring : String) : Prop :=
  True

instance instDecidablePrecond (strings : List String) (substring : String) : Decidable (precondition strings substring) := by
  unfold precondition
  infer_instance

def postcondition (strings : List String) (substring : String) (result : List String) :=
  (∀ i, i < result.length → result[i]!.containsSubstr substring →
  ∀ j, j < strings.length ∧ strings[j]!.containsSubstr substring → strings[j]! ∈ result →
  ∀ j, j < result.length → result.count result[j]! = strings.count result[j]!)

end Specs

section Impl

def implementation (strings: List String) (substring: String): List String :=
strings.filter (fun x => x.containsSubstr substring)

end Impl

section TestCases

def test1_strings : List String := []
def test1_substring : String := "a"
def test1_Expected : List String := []

def test2_strings : List String := ["abc", "bacd", "cde", "array"]
def test2_substring : String := "a"
def test2_Expected : List String := ["abc", "bacd", "array"]

def test3_strings : List String := ["\x0d1: \x01,\x0220\x0cB\x0b;,3,,`B", "\t`\x02;Bb\x0f,a\\ ;", "/\x0c:", "\x02;Ab \x10\x06` \x021C:10\x11C\x0f0\x11","3c0\x0eb1A:\\;a\x10\x08c\x0b,\x01c", "303Cc2c\x0cB", "\x08,,", "\x06\x0f/\\2`Ba,b\x0fC`c/", "\\ca\\\\cAc", "\x08","2\x10Bc,3\x0d\x123", "\x02C3,C2/\x0e\x11c1\x0fa\x012", ";2A,:", "C\\\\b\x0c\x12\x10\\cC,\x11`3; ", "0","\\\t\x05 31\x05A\\`1\x0e\x03\\;Cb", "2\x00`\x0b`\x02b\\", "A", "\\\x0c0CA1`\x12\x11\x0e"]
def test3_substring : String := ":c:"
def test3_Expected : List String := []

def test4_strings : List String := ["\x11\x14", ",A", "\x12A3\x0c\x05", "\\3:0B3b\x0eab;", "\x08a2:c,\x13;/a1333\x0c;", "\tA\x03","3,c\t0c1\x00;:\\3C\x07C:bcc1", "\x04C2,\x131 :\x04\x04b22", ",", "\x0b\x0e\x0f", "B,`a\x02\\\x0fc\x11\x04\x0c/","aaB:2\x11b1A/", "c3", "\x0dc:\x0f\x13:B\x0b\\\x0b,cBC1b", ";,1\x14\x0b\\1B\x00"]
def test4_substring : String := " A/,A\x13\x0e"
def test4_Expected : List String := []

def test5_strings : List String := ["C", "C\x03\x00Bc\x11Aa0` `", "201\x0c1,2A;2a\x02,\x0bb`\x08\x0c", "\x10\x0b\x0b\x0b ", "b2\x01C`3b\x01 \x00;\x0c:"]
def test5_substring : String := ":2\x14\x03"
def test5_Expected : List String := []

def test6_strings : List String := ["\x11`\t:1\x023`,\x0f", "C\x12\x07c\\3\x14\\A\x13\x05Cb,,1\x0f", "", "c1\x02\\2 \\;11b3\x0f\x00",":b\n;01;,\x0baC\x14;`\x07", "3\x06\x02\x10\x14bBc2;", "`/b,", "2\t`,021\x01:3", "\x0333\x03:\n\x03BB ", "1\t2 320c","\x11b A` :\x0b1:,\x12;0/", "a\tC;C\x07`\nA", "\\C\x05b3`\x00\x00`\x022A\\\t3/\x00\x06","\\1\\1A0,\x0f,\x042a0A:\x0c\\", "\x07\x01bB\\BA\nB\x04", "", "A3a` C\t2c\x040b,", "\x00\na", ":\x01", "\n\x04"]
def test6_substring : String := "0c3\x14`;,\x0f a, "
def test6_Expected : List String := []

def test7_strings : List String := ["\x14/03\x03;\\ B\x0eBA", ",;BCa\x0c:\x01:\tC\x03", "3\x0e`\x040:c", ",\x081;\\,\x02", "b B", "ca/\x03`\x14:"]
def test7_substring : String := "3\x08\\\nC0A\x0e\x07\n\\b\x12A3ac"
def test7_Expected : List String := []

def test8_strings : List String := ["\x0b\x12;`\x13\x0b:\n\x111`aBa:\x06", "\x083;a:\x11 \x07\x12:\\\\B\x01;:b", "\x060a\x05\t`b1\x14\x0001"]
def test8_substring : String := "0a\x08"
def test8_Expected : List String := []

def test9_strings : List String := [",2:\\\x0db\x00,\x03\t", "\\b \x04/b", "\x0d\x04,3"]
def test9_substring : String := "\x01"
def test9_Expected : List String := []

def test10_strings : List String := ["B/:2,C\x01B ", "\x11``\x0dCb"]
def test10_substring : String := "\x02C31B\x10a,`\x011"
def test10_Expected : List String := []

def test11_strings : List String := ["B3`", "\x120`;0a2AC\x0e1", "Ccbc1\x04\x13", "/C3\x0301b/`", "a2\x08`,Ac:,\x02;A","\\ \x00\x0d3\x00\x02:,,/\x12C\x12\t\x07/", "\x03C\n\x0b;;:\x10", "", "3\t\x03;\x0f AB1\x0fc bBc\x051",",3\x11 B \x0f"]
def test11_substring : String := "\\\\C\x10\x03/\\,"
def test11_Expected : List String := []

def test12_strings : List String := [":,bA2c;", "2,0a0\x14\\\x0fbC:B`0A", "3;0`", "a\x11acb", "`1\x04\x0b3\x0e\x14  `\x04`1\\2 ", "\\\x0602/\x11,/","\x04\\\x10\x0e\n`/1b,\x00\\/", "C\x051/\x0b;/ /BC:", "1\x0e\x02\x12,2;\nC;", " \x113:A"," \n\x02,\x13C\x12/0\x103B3/", "` \x0f3/b/a\\\x01"]
def test12_substring : String := "\x04\\/`;2:2:\x0f:b/\x14/\\"
def test12_Expected : List String := []

def test13_strings : List String := ["\\2", "0a3", "\x14\x08:B;\x03\\\x01\x00", " aA1\x04`\x07c0\x14Ca", "` :\x10B;``Ca", "\\:2\x12\\\\2\x00\\11","c\x0ca\x0e\x05\x06:c A\x08A2", "\x11C/CC3/,;b\x0c", "b\x02:;3A;`A\x002", "", "", "\x11\x04\x0e`CC;\\10:; "," 33,c\x00A,31 \x02", "B:;\\", "`BB\x14\x05,\x0e:\x04/:A/", "", ":`C:\x0b`", " \x0b02aC", "\\C \x02\n\x0eacaA,\tb`\\","\x0cA3\\\n1`"]
def test13_substring : String := ":b\x06\\2\x02B/cA3\x12\\C"
def test13_Expected : List String := []

def test14_strings : List String := ["0B\x13c\x00", "C", "C:2;11\x0cB;:\x04\x08B\x11", "\x011`\x08a\x14a\x042\x06C\n0,3\tC/\x07", " c,\\b\x0c\x03 ", ""]
def test14_substring : String := ""
def test14_Expected : List String := ["0B\x13c\x00", "C", "C:2;11\x0cB;:\x04\x08B\x11", "\x011`\x08a\x14a\x042\x06C\n0,3\tC/\x07", " c,\\b\x0c\x03 "]

def test15_strings : List String := ["C\x01`\\Ca\x00B\x04,\n\\C\n,C;3\x08", ":\x0dB;\x10;0\x123\x04cA\x0120,\x14", "C`b2\x12\x01\x13\x10:b2cB "]
def test15_substring : String := "\x0c/a\\c`a2121;\\ 1;"
def test15_Expected : List String := []

def test16_strings : List String := ["c01`\x0d22", "/\x05 \x0bc\x05;`\x02\x0720B;\x00\x0e", "B\x07:\\0Ab`\\", "\x08,:32`\\\x02","\\1:\x03 A\x13\x07\x07\\\x03", "2BBb c\\3\\0:\nA", "\x00\x0e3\\`3`:A\\b\\,\\1", "b`C1\\", "c0/`\x012CB", "\x053:;","\x13A0\n\x02 ,\x03B3A", "", "10\x061a/A\x03;\n\x0bA", "0a:\x03\x03\\", "", "c/\x07\x0d2b/230\x12AA32", ";0\t;a","0\\3\x14/B\x11`\t2C\x00A", "bb2/", "\\`,a0bbCC;B\x03\x00:\t"]
def test16_substring : String := "3Aa,:\x08ac2,002:BB"
def test16_Expected : List String := []

def test17_strings : List String := ["\x14 \\2C\\b `cA\x07\x0320\\a", ";20BB\x0bA\x08\\a", " \x04\x0dAc/", "1,\\1\\c`\x081c/0",",C `\\B0\t\x113;\x00 1a\x12", "", "\x073", ";,0/A\x0d", "/1`:a:"]
def test17_substring : String := "/B\x01\x0b\x0c,A\x14 A"
def test17_Expected : List String := []
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test1 (result : List String) :
  result ≠ test1_Expected →
  ¬ postcondition test1_strings test1_substring result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  plausible'_mut (seeds := #[test1_Expected]) (config := { numInst := 100000 })
