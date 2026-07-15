import Mathlib.Tactic

namespace VerinaSpec


def only_once_precond (a : Array Int) (key : Int) : Prop :=
  True

def only_once_loop {T : Type} [DecidableEq T] (a : Array T) (key : T) (i keyCount : Nat) : Bool :=
  if i < a.size then
    match a[i]? with
    | some val =>
        let newCount := if val = key then keyCount + 1 else keyCount
        only_once_loop a key (i + 1) newCount
    | none => keyCount == 1
  else
    keyCount == 1

def count_occurrences {T : Type} [DecidableEq T] (a : Array T) (key : T) : Nat :=
  a.foldl (fun cnt x => if x = key then cnt + 1 else cnt) 0

def only_once_postcond (a : Array Int) (key : Int) (result: Bool) :=
  ((count_occurrences a key = 1) → result) ∧
  ((count_occurrences a key ≠ 1) → ¬ result)

end VerinaSpec

namespace LLMSpec

-- Helper definition: the key occurs exactly once iff its Array.count is 1.
def occursExactlyOnce (a : Array Int) (key : Int) : Prop :=
  a.count key = 1

def precondition (a : Array Int) (key : Int) : Prop :=
  True

def postcondition (a : Array Int) (key : Int) (result : Bool) : Prop :=
  (result = true ↔ occursExactlyOnce a key)

end LLMSpec

section Proof

theorem precondition_equiv (a : Array Int) (key : Int) :
  VerinaSpec.only_once_precond a key ↔ LLMSpec.precondition a key := by
  sorry

theorem postcondition_equiv (a : Array Int) (key : Int) (result: Bool) :
  LLMSpec.precondition a key →
  (VerinaSpec.only_once_postcond a key result ↔ LLMSpec.postcondition a key result) := by
  sorry

end Proof
