import Extensions.Testing
import Extensions.SMTHelper

import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic

/-!
Consolidated tactic entrypoint.

Provided by imported modules:
- `plausible'` (from `Extensions.Testing`)
- `smt'`, `auto'` (from `Extensions.SMTHelper`)
-/


@[simp,grind]
theorem empty_arr_sz : forall { α },  (#[]: Array α).size = 0 := by
  grind
  
@[simp,grind]
theorem empty_list_sz : forall { α },  ([]: List α).length = 0 := by
  grind
  
@[simp,grind]
theorem not_lt_empty_list {α} {t : Nat} :
  ¬ t < ([] : List α).length := by
  simp

@[simp,grind]
theorem not_lt_empty_array {α} {t : Nat} :
  ¬ t < (#[] : Array α).size := by
  simp

@[simp]
theorem forall_lt_empty_array {α} {P : Nat → Prop} :
    (∀ t, t < (#[] : Array α).size → P t) := by
  intro t h
  simp at h

@[simp]
theorem forall_lt_empty_list {α} {P : Nat → Prop} :
    (∀ t, t < ([] : List α).length → P t) := by
  intro t h
  simp at h
