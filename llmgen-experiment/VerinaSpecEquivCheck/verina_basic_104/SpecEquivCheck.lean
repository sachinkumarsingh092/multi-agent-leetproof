import Mathlib.Tactic

namespace VerinaSpec

structure Map (K V : Type) [BEq K] [BEq V] where
  entries : List (K × V)
deriving Inhabited
instance  (K V : Type) [BEq K] [BEq V] : BEq (Map K V) where
  beq m1 m2 := List.length m1.entries = List.length m2.entries ∧ List.beq m1.entries m2.entries

def empty {K V : Type} [BEq K] [BEq V] : Map K V := ⟨[]⟩

def insert {K V : Type} [BEq K] [BEq V] (m : Map K V) (k : K) (v : V) : Map K V :=
  let entries := m.entries.filter (fun p => ¬(p.1 == k)) ++ [(k, v)]
  ⟨entries⟩

def update_map_precond (m1 : Map Int Int) (m2 : Map Int Int) : Prop :=
  True

def find? {K V : Type} [BEq K] [BEq V] (m : Map K V) (k : K) : Option V :=
  m.entries.find? (fun p => p.1 == k) |>.map (·.2)

def update_map_postcond (m1 : Map Int Int) (m2 : Map Int Int) (result: Map Int Int) : Prop :=
  List.Pairwise (fun a b => a.1 ≤ b.1) result.entries ∧
  m2.entries.all (fun x => find? result x.1 = some x.2) ∧
  m1.entries.all (fun x =>
    match find? m2 x.1 with
    | some _ => true
    | none => find? result x.1 = some x.2
  ) ∧
  result.entries.all (fun x =>
    match find? m1 x.1 with
    | some v => match find? m2 x.1 with
      | some v' => x.2 = v'
      | none => x.2 = v
    | none => find? m2 x.1 = some x.2
  )

end VerinaSpec

namespace LLMSpec

def precondition (m1 : Map Int Int) (m2 : Map Int Int) : Prop := by admit

def postcondition (m1 : Map Int Int) (m2 : Map Int Int) (result: Map Int Int) : Prop := by admit

end LLMSpec

section Proof

theorem precondition_equiv (m1 : Map Int Int) (m2 : Map Int Int) :
  VerinaSpec.update_map_precond m1 m2 ↔ LLMSpec.precondition m1 m2 := by
  admit

theorem postcondition_equiv (m1 : Map Int Int) (m2 : Map Int Int) (result: Map Int Int) :
  LLMSpec.precondition m1 m2 →
  (VerinaSpec.update_map_postcond m1 m2 result ↔ LLMSpec.postcondition m1 m2 result) := by
  admit

end Proof
