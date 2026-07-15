import Velvet.Std
import Extensions.SpecDSL

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Comprehensive test of section Specs functionality

namespace ExtensionsSpecDSLTest1
section Specs

register_specdef_allow_recursion

def fib (n: Nat) : Nat :=
  if n < 2 then 1 else
  fib (n - 1) + fib (n - 2)
  termination_by n

def precondition (n: Nat) := True
def postcondition (n: Nat) (result : Nat) :=
  result = fib n

end Specs

section Impl
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

end ExtensionsSpecDSLTest1

namespace ExtensionsSpecDSLTest2

section Specs

def precondition (n : Nat) := n < 100
def postcondition (n : Nat) (result : Nat) := result > n ∧ result < n + 10

end Specs

end ExtensionsSpecDSLTest2

#print ExtensionsSpecDSLTest1.precondition
#check ExtensionsSpecDSLTest1.postcondition
#check ExtensionsSpecDSLTest2.precondition
#check ExtensionsSpecDSLTest2.postcondition
