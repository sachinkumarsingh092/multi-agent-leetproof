import Velvet.Std
import Extensions.Testing
import CaseStudies.Tactic
import Mathlib.Data.Nat.Basic
import Plausible

set_option trace.Loom.debug true

/-!
# Buggy FindMax examples for testing plausible'

These examples contain intentionally wrong invariants to test
whether plausible' can find counterexamples.
-/

set_option maxHeartbeats 500000

theorem findmax_bug0
  (a : Array ℕ)
  (i : ℕ)
  (update : a[i]! > 2 → 1 = a[i]!):
  ∃ k < i, a[k]! = 1 := by  -- BUG: should be k < i + 1 or k ≤ i
  plausible' (config := { numInst := 20000, numRetries := 1 })

-- Bug 1: Wrong upper bound - claims i ≤ a.size - 1 instead of i ≤ a.size
theorem findmax_bug1
  (a : Array ℕ)
  (i m : ℕ)
  (requier1 : 0 < a.size)
  (init_i : i = 1)
  (init_m : m = a[0]!)
  (loop_cond : i < a.size)
  (invariant_pref_i_bounds : 1 ≤ i ∧ i ≤ a.size - 1)  -- BUG: should be i ≤ a.size
  (invariant_pref_m_upper : ∀ k < i, a[k]! ≤ m)
  (invariant_pref_m_witness : ∃ k < i, a[k]! = m) :
  1 ≤ i + 1 ∧ i + 1 ≤ a.size - 1 := by
  plausible' (config := { numInst := 10000, numRetries := 1 })

-- Bug 2: Missing witness after update - forgets to check if new element is the max
theorem findmax_bug2
  (a : Array ℕ)
  (i m m' : ℕ)
  (requier1 : 0 < a.size)
  (bounds : 1 ≤ i ∧ i < a.size)
  (old_witness : ∃ k < i, a[k]! = m)
  (update : a[i]! > m → m' = a[i]!)
  (update2 : ¬(a[i]! > m) → m' = m) :
  ∃ k < i, a[k]! = m' := by  -- BUG: should be k < i + 1 or k ≤ i
  plausible' (config := { numInst := 100000, numRetries := 1 })

-- Should pass
theorem findmax_bug3
  (a : Array ℕ)
  (i m : ℕ)
  (requier1 : 0 < a.size)
  (bounds : 1 ≤ i ∧ i ≤ a.size)
  (upper_bound : ∀ k < i, a[k]! ≤ m)
  (witness : ∃ k ≤ i, a[k]! = m)
  (done : a.size ≤ i) :
  ∃ k < a.size, a[k]! = m := by
  plausible' (config := { numInst := 10000, numRetries := 1 })

-- Should pass
theorem findmax_bug4
  (a : Array ℕ)
  (i m : ℕ)
  (requier1 : 0 < a.size)
  (bounds : 1 ≤ i ∧ i ≤ a.size)
  (upper_bound : ∀ k < i, a[k]! ≤ m)
  (done : a.size ≤ i) :
  ∀ k < a.size, a[k]! ≤ m := by
  plausible' (config := { numInst := 10000, numRetries := 1 })

-- Bug 5: Off-by-one in array bounds
theorem findmax_bug5
  (a : Array ℕ)
  (m : ℕ)
  (requier1 : 0 < a.size)
  (init : m = a[0]!) :
  ∃ k < a.size - 1, a[k]! = m := by  -- BUG: should be k < a.size
  plausible' (config := { numInst := 10000, numRetries := 1 })

-- Bug 6: Incorrect initial invariant
theorem findmax_bug6
  (a : Array ℕ)
  (m : ℕ)
  (requier1 : 0 < a.size)
  (init_m : m = a[0]!) :
  ∀ k < 1, a[k]! < m := by  -- BUG: should be ≤, and a[0]! = m
  plausible' (config := { numInst := 10000, numRetries := 1 })

-- Should pass
theorem findmax_bug7
  (a : Array ℕ)
  (i m : ℕ)
  (bounds : 1 ≤ i ∧ i ≤ a.size)
  (upper : ∀ k < i, a[k]! ≤ m)
  (witness : ∃ k, k < i - 1 ∧ a[k]! = m)
  (done : a.size ≤ i) :
  ∃ k < a.size, a[k]! = m := by
  -- grind is able to solve
  -- grind
  plausible' (config := { numInst := 10000, numRetries := 1 })

-- Bug 8: Strict vs non-strict inequality confusion
theorem findmax_bug8
  (a : Array ℕ)
  (i m : ℕ)
  (requier1 : 0 < a.size)
  (bounds : 1 < i ∧ i ≤ a.size)  -- BUG: should be 1 ≤ i
  (upper : ∀ k < i, a[k]! ≤ m)
  (witness : ∃ k < i, a[k]! = m) :
  1 < i + 1 ∧ i + 1 ≤ a.size := by
  plausible' (config := { numInst := 10000, numRetries := 1 })

-- Bug 9: Missing size constraint
theorem findmax_bug9
  (a : Array ℕ)
  (i m : ℕ)
  (init_i : i = 1)
  (init_m : m = a[0]!)  -- BUG: missing requier1 a.size > 0
  (witness : ∃ k < i, a[k]! = m) :
  1 ≤ i ∧ i ≤ a.size := by
  plausible' (config := { numInst := 10000, numRetries := 1 })

theorem findmax_bug10
  (a : Array ℕ)
  (i m m' : ℕ)
  (bounds : 1 ≤ i ∧ i < a.size)
  (upper : ∀ k < i, a[k]! ≤ m)
  (witness : ∃ k < i, a[k]! = m)
  (update : a[i]! ≤ m → m' = a[i]!)  -- BUG: swapped condition
  (no_update : a[i]! > m → m' = m) :
  ∀ k < i + 1, a[k]! ≤ m' := by
  plausible' (config := { numInst := 100000, numRetries := 1 })
