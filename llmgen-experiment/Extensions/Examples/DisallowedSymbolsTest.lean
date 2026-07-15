import Velvet.Std
import Extensions.DisallowedSymbols

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

namespace ExtensionsDisallowedSymbolsTest

-- Some helpers

def safeHelper (n : Nat) : Nat := n + 1
def forbiddenHelper (n : Nat) : Nat := n + 2

def plainForbidden (n : Nat) : Nat := forbiddenHelper n

attribute [disallowedSymbol] forbiddenHelper

method usesOnlySafe (n : Nat) return (res : Nat)
  ensures res = n + 1
  do
  return safeHelper n

method usesForbidden (n : Nat) return (res : Nat)
  ensures res = n + 2
  do
  return forbiddenHelper n

method usesForbiddenInInvariant (n : Nat) return (res : Nat)
  ensures res = n
  do
  let mut i := 0
  while i < n
    invariant forbiddenHelper i ≥ 0
    done_with i = n
  do
    i := i + 1
  return i

-- Positive checks
#ensure_no_disallowed_symbols usesOnlySafe
#ensure_no_disallowed_symbols_in_method usesOnlySafe
#ensure_no_disallowed_symbols_in_method usesForbiddenInInvariant

-- Generic checker does not ignore gadgets
/--
error: Disallowed symbols used in `ExtensionsDisallowedSymbolsTest.usesForbiddenInInvariant`: ExtensionsDisallowedSymbolsTest.forbiddenHelper
-/
#guard_msgs in
#ensure_no_disallowed_symbols usesForbiddenInInvariant

-- Negative check via registry
/--
error: Disallowed symbols used in `ExtensionsDisallowedSymbolsTest.usesForbidden`: ExtensionsDisallowedSymbolsTest.forbiddenHelper
-/
#guard_msgs in
#ensure_no_disallowed_symbols usesForbidden

-- Negative check via explicit list argument
/--
error: Disallowed symbols used in `ExtensionsDisallowedSymbolsTest.usesForbidden`: ExtensionsDisallowedSymbolsTest.forbiddenHelper
-/
#guard_msgs in
#ensure_no_disallowed_symbols usesForbidden using [forbiddenHelper]

-- Local ignore list: should pass
#ensure_no_disallowed_symbols usesForbidden ignoring [forbiddenHelper]
#ensure_no_disallowed_symbols usesForbidden using [forbiddenHelper] ignoring [forbiddenHelper]

-- Velvet-method only checker rejects non-method declarations
/--
error: Declaration `ExtensionsDisallowedSymbolsTest.plainForbidden` is not a Velvet method
-/
#guard_msgs in
#ensure_no_disallowed_symbols_in_method plainForbidden

-- Per-check ignore list works
#ensure_no_disallowed_symbols usesOnlySafe using [safeHelper] ignoring [safeHelper]
#ensure_no_disallowed_symbols usesForbidden using [forbiddenHelper] ignoring [forbiddenHelper]

end ExtensionsDisallowedSymbolsTest
