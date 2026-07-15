import Velvet.Std
import Extensions.Testing
import Extensions.VelvetPBT
import Extensions.SpecDSL
-- Never add new imports here

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    findRotations: minimum number of rotations (greater than 0) required to get the same string.
    Natural language breakdown:
    1. The input is a string `s`.
    2. Consider rotating `s` left by `k` positions, where `k` is a natural number.
    3. A rotation count `k` is valid if `k > 0` and rotating by `k` yields the original string.
    4. The result is the smallest positive `k` that is valid.
    5. For the empty string, any rotation yields the empty string; the smallest positive rotation count is 1.
    6. For any nonempty string of length `n`, rotating by `n` yields the original string, so a valid `k` exists.
    7. Therefore the result is always a positive integer.
-/

section Specs
-- Helper: left rotation of a string by `k` positions, defined via `List.rotate`.
-- We stay within computable, Mathlib-provided operations.
def strRotate (s : String) (k : Nat) : String :=
  String.mk (s.data.rotate k)

-- Helper: predicate that a given k is a positive rotation returning the same string.
def isGoodRotation (s : String) (k : Nat) : Prop :=
  0 < k ∧ strRotate s k = s

-- Precondition: none (total function)
def precondition (string : String) : Prop :=
  True

-- Postcondition: `res` is the minimal positive rotation count that returns the same string.
-- We specify uniqueness via:
-- 1) positivity
-- 2) correctness (rotation by res gives original)
-- 3) minimality among positive k
-- The result is an Int, but we constrain it to be a positive Nat via `Int.ofNat`.
def postcondition (string : String) (res : Int) : Prop :=
  ∃ (r : Nat),
    r > 0 ∧
    res = Int.ofNat r ∧
    strRotate string r = string ∧
    (∀ (k : Nat), k > 0 → strRotate string k = string → r ≤ k)
end Specs

section Impl
method findRotations (string : String)
  return (res : Int)
  require precondition string
  ensures postcondition string res
  do
    let n := string.data.length
    -- Empty string: by convention, smallest positive rotation count is 1
    if n = 0 then
      return 1
    else
      let mut k : Nat := 1
      let mut ans : Nat := n
      let mut found : Bool := false

      while (k ≤ n ∧ found = false)
        invariant "inv_k_bounds" (1 ≤ k ∧ k ≤ n + 1)
        invariant "inv_ans_bounds" (1 ≤ ans ∧ ans ≤ n)
        invariant "inv_no_good_before_k_if_not_found" (found = false → ∀ t : Nat, 0 < t → t < k → strRotate string t ≠ string)
        invariant "inv_rotate_n" (strRotate string n = string)
        invariant "inv_default_ans_if_not_found" (found = false → ans = n)
        invariant "inv_found_implies_good" (found = true → strRotate string ans = string)
        invariant "inv_found_implies_minimal" (found = true → ∀ t : Nat, 0 < t → t < ans → strRotate string t ≠ string)
        done_with (k > n ∨ found = true)
      do
        if strRotate string k = string then
          ans := k
          found := true
        else
          k := k + 1

      return Int.ofNat ans
end Impl

section TestCases
-- Test case 1: example: all characters same
-- "aaaa" repeats after 1 rotation
def test1_string : String := "aaaa"
def test1_Expected : Int := 1

-- Test case 2: example: two distinct characters
-- "ab" repeats after 2 rotations
def test2_string : String := "ab"
def test2_Expected : Int := 2

-- Test case 3: example: no smaller period than full length
-- "abc" repeats after 3 rotations
def test3_string : String := "abc"
def test3_Expected : Int := 3

-- Test case 4: empty string
-- smallest positive rotation count is 1
def test4_string : String := ""
def test4_Expected : Int := 1

-- Test case 5: single character string
-- repeats after 1 rotation
def test5_string : String := "x"
def test5_Expected : Int := 1

-- Test case 6: even length with period 2
-- "abab" repeats after 2 rotations
def test6_string : String := "abab"
def test6_Expected : Int := 2

-- Test case 7: period 3 inside length 6
-- "abcabc" repeats after 3 rotations
def test7_string : String := "abcabc"
def test7_Expected : Int := 3

-- Test case 8: mixed pattern with minimal period 4
-- "abcdabcd" repeats after 4 rotations
def test8_string : String := "abcdabcd"
def test8_Expected : Int := 4

-- Test case 9: no smaller period than length 4
-- "abca" repeats after 4 rotations
def test9_string : String := "abca"
def test9_Expected : Int := 4

-- IMPORTANT: All expected outputs MUST use format testN_Expected (capital E)
-- Recommend to validate: 1, 2, 6
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((findRotations test1_string).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((findRotations test2_string).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((findRotations test3_string).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((findRotations test4_string).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((findRotations test5_string).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((findRotations test6_string).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((findRotations test7_string).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((findRotations test8_string).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((findRotations test9_string).run), DivM.res test9_Expected ]
end Assertions

section Pbt
-- PBT disabled due to build error:
-- [ERROR] Line 171, Column 0
-- Message: unsolved goals
-- string : String
-- res : ℤ
-- ⊢ Decidable (postcondition string res)
-- Line: prove_postcondition_decidable_for findRotations
-- [ERROR] Line 173, Column 0
-- Message: aborting evaluation since the expression depends on the 'sorry' axiom, which can lead to runtime instability and crashes.
--
-- To attempt to evaluate anyway despite the risks, use the '#eval!' command.
-- Line: run_elab do

-- extract_program_for findRotations
-- prove_precondition_decidable_for findRotations
-- prove_postcondition_decidable_for findRotations
-- derive_tester_for findRotations
-- run_elab do
--   let g : Plausible.Gen (_ × Bool) := do
--     let arg_0 ← Plausible.SampleableExt.interpSample (String)
--     let res := findRotationsTester arg_0
--     pure ((arg_0), res)
--   for _ in [1: 200] do
--     let res ← Plausible.Gen.run g 20
--     unless res.2 do
--       IO.println s!"Postcondition violated for input {res.1}"
--       break

end Pbt

section Proof
set_option maxHeartbeats 10000000

velvet_plausible_test findRotations (config := { maxMs := some 5000 })


-- prove_correct findRotations by
  -- loom_solve <;> (try simp at *; expose_names)
end Proof
