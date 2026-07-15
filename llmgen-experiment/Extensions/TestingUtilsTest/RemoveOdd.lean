import Velvet.Std
import CaseStudies.TestingUtil
import Extensions.SpecDSL
import Extensions.Testing
import Extensions.VelvetPBT
-- Never add new imports here

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    MBPP ID 437: remove odd characters in a string
    Natural language breakdown:
    1. Input is a string `str`, viewed as an ordered sequence of characters.
    2. Characters are indexed from 0.
    3. An index is odd iff it has the form `2*k + 1` for some natural number `k`.
    4. The output string `res` contains exactly the characters of `str` at odd indices.
    5. The relative order of kept characters is preserved.
    6. Therefore, the output length is `str.length / 2`.
    7. For every `k` with `k < res.length`, the `k`-th output character equals
       the `(2*k + 1)`-th input character.
-/

section Specs
-- Helper: convert a string to an array of characters, for safe `Nat` indexing via `[i]!`.
-- We use Mathlib/Std operations already available via the existing imports.
def chars (s : String) : Array Char := s.toList.toArray

-- No preconditions.
def precondition (str : String) : Prop :=
  True

-- Postcondition: `res` is exactly the odd-indexed characters of `str` (0-based).
-- We characterize the output uniquely by:
-- (a) length relationship, and
-- (b) index-wise correspondence.
def postcondition (str : String) (res : String) : Prop :=
  res.length = str.length / 2 ∧
  ∀ (k : Nat), k < res.length →
    (chars res)[k]! = (chars str)[(2*k + 1)]!
end Specs

section Impl
method removeOddChars (str: String)
  return (res: String)
  require precondition str
  ensures postcondition str res
  do
  let a := chars str
  let mut out : Array Char := #[]
  let mut i : Nat := 1
  while i < a.size
    -- Bounds for safe indexing and to relate termination index to `a.size`.
    invariant "inv_bounds" 1 ≤ i ∧ i ≤ a.size + 1
    -- `i` is always the next odd index to read; `out.size` counts how many odds were taken.
    invariant "inv_step" i = 2 * out.size + 1
    -- `out` stores exactly the odd-indexed characters collected so far.
    invariant "inv_contents" ∀ (k : Nat), k < out.size → out[k]! = a[(2*k + 1)]!
    -- Definition bridge: `a` is the character array of the input.
    invariant "inv_a_def" a = chars str
    -- Bridge for postcondition length: `String.mk` length equals the array size.
    invariant "inv_out_len" (String.mk out.toList).length = out.size
    -- Bridge for postcondition element access: `chars` of the constructed string is `out`.
    invariant "inv_chars_mk" chars (String.mk out.toList) = out
    -- Bridge between array size and string length for the input.
    invariant "inv_chars_size_str" (chars str).size = str.length
    -- Count characterization: `out.size` is the number of odd indices already consumed.
    -- This is provable at init (out.size=0, i=1) and preserved by push/i+=2.
    -- At exit with `i >= a.size` it is sufficient to derive `out.size = a.size / 2`.
    invariant "inv_out_size_count" 2 * out.size ≤ a.size ∧ a.size ≤ 2 * out.size + 1
    done_with i >= a.size
  do
    out := out.push (a[i]!)
    i := i + 2
  let res : String := String.mk out.toList
  return res
end Impl

velvet_plausible_test removeOddChars (config := { maxMs := some 5000 })
