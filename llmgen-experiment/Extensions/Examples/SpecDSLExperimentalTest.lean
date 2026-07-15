import Velvet.Std
import Extensions.Attributes
import Extensions.SpecDSLExperimental

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

namespace ExtensionsSpecExperimentalTests

attribute [allowedSymbol] List.take List.map List.filter

-- Test cases
spec foo1 : Int := 5

spec fib (n: Nat) : Nat :=
  if n < 2 then 1 else
  fib (n - 1) + fib (n - 2)
  termination_by n

-- With type parameters
spec foo3 {α : Type} (x : α) : α := x

-- With pattern matching
/--
error: Unsupported syntax, only allowed syntax is with ':='
-/
#guard_msgs in
spec foo4 : Nat → Nat
  | 0 => 0
  | n + 1 => n

@[specHelper] def foo := 1
@[specHelper] def bar := 2

/--
info: Spec Helpers: [ExtensionsSpecExperimentalTests.foo1,
 ExtensionsSpecExperimentalTests.fib,
 ExtensionsSpecExperimentalTests.foo3,
 ExtensionsSpecExperimentalTests.foo,
 ExtensionsSpecExperimentalTests.bar]
-/
#guard_msgs in
#printSpecHelpers

namespace Impl

method fib_iterative' (n: Nat) return (res: Nat)
    ensures res = fib n
    do
    if n = 0 then
        return 0
    else if n = 1 then
        return 1
    else
        let mut a := 0
        let mut b := 1
        let mut i := 2
        while i <= n
            invariant i ≤ n + 1
            invariant a = fib (i - 2)
            invariant b = fib (i - 1)
            done_with i = n + 1
        do
            let next_fib := a + b
            a := b
            b := next_fib
            i := i + 1
        return b

#eval (fib_iterative' 2).run

end Impl

end ExtensionsSpecExperimentalTests
