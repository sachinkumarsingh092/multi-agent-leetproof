import Velvet.Std
import Extensions.Tactics
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic

set_option maxHeartbeats 10000000
set_option pp.coercions false
set_option pp.funBinderTypes true
set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

/- Problem Description

chooseProposalValue: the Paxos proposer's Phase 2a value-selection rule,
implemented as a single pure, deterministic method.

Scope: This specification covers exactly one core, self-contained rule of
Paxos. The full Paxos protocol (multiple roles, message passing, persistent
state, failure handling) cannot be expressed as a single method for this
pipeline. Explicitly out of scope, planned as separate single-method runs:
acceptorPromise (Phase 1b), acceptorAccept (Phase 2b), nextProposalNumber
(proposal-number generation), isQuorum (majority quorum detection), and
learnerChosenValue (learner chosen-value detection). Networking, persistence,
timeouts, and leader election remain out of scope for all of these.

Purpose: After a proposer receives promise responses from a quorum of
acceptors, Paxos requires it to propose the value associated with the
highest-numbered previously accepted proposal among those responses; only if
no acceptor in the quorum has previously accepted any value may the proposer
use its own value.

Inputs:
- acceptedNums : Array Nat — proposal numbers of previously accepted proposals
  reported in the promise responses. Each entry corresponds positionally to
  the entry at the same index in acceptedVals. Only responses that actually
  reported a previously accepted proposal are included; responses reporting
  "nothing accepted yet" must be filtered out by the caller before invoking
  this method.
- acceptedVals : Array Int — the values of those previously accepted
  proposals, positionally aligned with acceptedNums.
- defaultVal : Int — the proposer's own desired value, used only when no
  acceptor reported a previously accepted proposal.

Output:
- result : Int — the value the proposer must propose in Phase 2a.

Preconditions (explicit):
- acceptedNums.size = acceptedVals.size. Behavior is unspecified if the
  lengths differ; callers must guarantee equal lengths.
- Proposal numbers are natural numbers; there is no upper bound.

Behavior:
- If both arrays are empty (no acceptor reported a prior acceptance), the
  result is defaultVal.
- Otherwise, the result is acceptedVals[i] where i is an index at which
  acceptedNums attains its maximum value.
- Tie-breaking (recorded assumption, reviewer may change): in standard Paxos,
  distinct acceptors reporting the same proposal number must have accepted the
  same value (a protocol invariant), so ties are semantically harmless. For
  determinism at the specification level, if the maximum proposal number
  occurs at multiple indices, the value at the FIRST (lowest) such index is
  returned.

Boundaries:
- The maximum is inclusive; an array of size 1 trivially selects its only
  value.
- Proposal number 0 is a legal accepted proposal number (recorded assumption:
  the caller does not reserve 0 as a sentinel; reviewer may change this).

Mutation and ordering:
- The method does not mutate its inputs. Input ordering matters only for the
  first-occurrence tie-break; otherwise the result is order-insensitive.

Determinism: Fully deterministic — identical inputs always produce identical
output.

Edge and degenerate cases:
- Empty inputs: returns defaultVal.
- Single element: returns that element's value regardless of defaultVal.
- All proposal numbers equal: returns the value at index 0.
- defaultVal is ignored whenever the arrays are non-empty, even if defaultVal
  is "better" by any measure.

Complexity requirement (implementation guidance, not expressible in the
contract): O(n) time in the length of the arrays, O(1) additional space.

Worked examples:
- acceptedNums = [3, 7, 5], acceptedVals = [10, 20, 30], defaultVal = 0:
  maximum proposal number is 7 at index 1, result = 20.
- acceptedNums = [], acceptedVals = [], defaultVal = 42: no prior acceptances,
  result = 42.
-/

section Specs
-- Index i is a valid selection index: acceptedNums attains its maximum at i,
-- and i is the first (lowest) index attaining that maximum.
def isFirstMaxIndex (acceptedNums : Array Nat) (i : Nat) : Prop :=
  i < acceptedNums.size ∧
  (∀ j : Nat, j < acceptedNums.size → acceptedNums[j]! ≤ acceptedNums[i]!) ∧
  (∀ j : Nat, j < i → acceptedNums[j]! < acceptedNums[i]!)

def precondition (acceptedNums : Array Nat) (acceptedVals : Array Int)
    (defaultVal : Int) : Prop :=
  acceptedNums.size = acceptedVals.size

def postcondition (acceptedNums : Array Nat) (acceptedVals : Array Int)
    (defaultVal : Int) (result : Int) : Prop :=
  if acceptedNums.size = 0 then
    -- Empty inputs: the proposer uses its own value.
    result = defaultVal
  else
    -- Non-empty inputs: result is the value at the first index attaining
    -- the maximum proposal number. This uniquely determines result.
    ∃ i : Nat, isFirstMaxIndex acceptedNums i ∧ result = acceptedVals[i]!
end Specs

section Impl
method chooseProposalValue (acceptedNums : Array Nat) (acceptedVals : Array Int)
    (defaultVal : Int)
  return (result : Int)
  require precondition acceptedNums acceptedVals defaultVal
  ensures postcondition acceptedNums acceptedVals defaultVal result
do
  if acceptedNums.size = 0 then
    return defaultVal
  else
    let mut bestIdx := 0
    let mut j := 1
    while j < acceptedNums.size
      -- Invariant 1: index bounds; bestIdx is always strictly below j, and j never exceeds size.
      -- Init: bestIdx=0 < 1=j and 1 ≤ size (size ≠ 0). Preserved: bestIdx becomes at most j, then j increments.
      invariant "bounds" bestIdx < j ∧ j ≤ acceptedNums.size
      -- Invariant 2: bestIdx attains the max among the first j elements.
      -- Init: only k=0, trivially ≤ itself. Preserved: if arr[j] > arr[bestIdx], new bestIdx=j dominates all; else arr[j] ≤ arr[bestIdx].
      invariant "max_so_far" ∀ k : Nat, k < j → acceptedNums[k]! ≤ acceptedNums[bestIdx]!
      -- Invariant 3: bestIdx is the first index attaining that max (all earlier indices are strictly smaller).
      -- Init: no k < 0. Preserved: bestIdx only updates on strict increase; then all k < j are ≤ old max < new max.
      invariant "first_max" ∀ k : Nat, k < bestIdx → acceptedNums[k]! < acceptedNums[bestIdx]!
      -- Decreasing: distance from j to array size shrinks each iteration since j increments.
      decreasing acceptedNums.size - j
    do
      if acceptedNums[j]! > acceptedNums[bestIdx]! then
        bestIdx := j
      j := j + 1
    return acceptedVals[bestIdx]!
end Impl

section TestCases
-- Test 1: worked example; maximum 7 at index 1.
def test1_acceptedNums : Array Nat := #[3, 7, 5]
def test1_acceptedVals : Array Int := #[10, 20, 30]
def test1_defaultVal : Int := 0
def test1_Expected : Int := 20

-- Test 2: empty inputs; returns defaultVal.
def test2_acceptedNums : Array Nat := #[]
def test2_acceptedVals : Array Int := #[]
def test2_defaultVal : Int := 42
def test2_Expected : Int := 42

-- Test 3: single element; returns its value regardless of defaultVal.
def test3_acceptedNums : Array Nat := #[5]
def test3_acceptedVals : Array Int := #[-7]
def test3_defaultVal : Int := 100
def test3_Expected : Int := -7

-- Test 4: all proposal numbers equal; first-index tie-break returns index 0.
def test4_acceptedNums : Array Nat := #[4, 4, 4]
def test4_acceptedVals : Array Int := #[11, 22, 33]
def test4_defaultVal : Int := 0
def test4_Expected : Int := 11

-- Test 5: maximum 9 occurs at indices 1 and 2; first occurrence wins.
def test5_acceptedNums : Array Nat := #[1, 9, 9, 2]
def test5_acceptedVals : Array Int := #[5, 6, 7, 8]
def test5_defaultVal : Int := 0
def test5_Expected : Int := 6

-- Test 6: maximum at the first index.
def test6_acceptedNums : Array Nat := #[10, 2, 3]
def test6_acceptedVals : Array Int := #[99, 1, 2]
def test6_defaultVal : Int := 0
def test6_Expected : Int := 99

-- Test 7: maximum at the last index.
def test7_acceptedNums : Array Nat := #[1, 2, 10]
def test7_acceptedVals : Array Int := #[1, 2, 99]
def test7_defaultVal : Int := 0
def test7_Expected : Int := 99

-- Test 8: proposal number 0 is a legal accepted proposal number.
def test8_acceptedNums : Array Nat := #[0]
def test8_acceptedVals : Array Int := #[55]
def test8_defaultVal : Int := 7
def test8_Expected : Int := 55

-- Test 9: large proposal numbers; negative values are legal.
def test9_acceptedNums : Array Nat := #[1000000, 999999]
def test9_acceptedVals : Array Int := #[-1, -2]
def test9_defaultVal : Int := 0
def test9_Expected : Int := -1

-- Test 10: maximum 8 occurs at indices 1 and 3; first occurrence wins.
def test10_acceptedNums : Array Nat := #[2, 8, 3, 8, 1]
def test10_acceptedVals : Array Int := #[4, 50, 6, 60, 7]
def test10_defaultVal : Int := -5
def test10_Expected : Int := 50
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((chooseProposalValue test1_acceptedNums test1_acceptedVals test1_defaultVal).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((chooseProposalValue test2_acceptedNums test2_acceptedVals test2_defaultVal).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((chooseProposalValue test3_acceptedNums test3_acceptedVals test3_defaultVal).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((chooseProposalValue test4_acceptedNums test4_acceptedVals test4_defaultVal).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((chooseProposalValue test5_acceptedNums test5_acceptedVals test5_defaultVal).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((chooseProposalValue test6_acceptedNums test6_acceptedVals test6_defaultVal).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((chooseProposalValue test7_acceptedNums test7_acceptedVals test7_defaultVal).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((chooseProposalValue test8_acceptedNums test8_acceptedVals test8_defaultVal).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((chooseProposalValue test9_acceptedNums test9_acceptedVals test9_defaultVal).run), DivM.res test9_Expected ]

-- Test case 10

#assert_same_evaluation #[((chooseProposalValue test10_acceptedNums test10_acceptedVals test10_defaultVal).run), DivM.res test10_Expected ]
end Assertions

section Pbt
velvet_plausible_test chooseProposalValue (config := { maxMs := some 20000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000


prove_correct chooseProposalValue by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at * <;> expose_names); try (conv => congr <;> simp) ; try rfl; try expose_names)
end Proof
