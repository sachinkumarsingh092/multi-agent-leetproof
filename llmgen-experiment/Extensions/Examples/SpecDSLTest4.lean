import Velvet.Std
import Extensions.SpecDSL

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Test: Non-recursive functions defined in section Specs get loomAbstractionSimp attribute

namespace ExtensionsSpecDSLTest4

section Specs

def add (x y : Nat) : Nat := x + y
def multiply (x y : Nat) : Nat := x * y
def isEven (n : Nat) : Bool := n % 2 = 0
def increment (x : Nat) : Nat := x + 1

def precondition (x y : Nat) := True
def postcondition (x y : Nat) (result : Nat) := True

end Specs

namespace Impl

-- These compile fine since section Specs only adds loomAbstractionSimp,
-- not specHelper (the body check uses specHelpers from Extensions.SpecDSLExperimental).
method testValid (x : Nat) (y : Nat) return (res: Nat)
    ensures res = x + y + 1
    do
    let sum := x + y
    return sum + 1

end Impl

end ExtensionsSpecDSLTest4

-- Print function definitions to check attributes
#print ExtensionsSpecDSLTest4.add
#print ExtensionsSpecDSLTest4.multiply
#print ExtensionsSpecDSLTest4.isEven
#print ExtensionsSpecDSLTest4.increment
