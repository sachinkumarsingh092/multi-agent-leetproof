import CaseStudies.TestingUtil
import Plausible.Testable

/-!
# Velvet Plausible — Property-Based Testing with bounded quantifiers

This file extends the Loom library's `CaseStudies.TestingUtil` (which provides
`DecidableHeuristics` with `GuessingBounds`, `SyncAux`, etc.) with analogous
`Testable` quasi-instances for Plausible-based property testing.

It also provides the `plausible'` tactic which normalizes goals and
synthesizes auxiliary `Testable` instances via bound-guessing.
-/

namespace Loom.Testing

section TestableHeuristics

open Lean Meta Elab Tactic Plausible

/-!
## Copied private infrastructure from Loom's CaseStudies.TestingUtil

The following definitions are private in the Loom library and cannot be
accessed from downstream. We copy the generalized versions from loom-dev
(which support both Decidable and Testable via the `tcName` parameter).
-/

/-- Traverse `e` in a way like `Meta.transform`, with these differences:
- `step` takes an array of free variables, which represents the free
  variables introduced along the way by `forallE` and `lam`.
- `step` returns `Unit`.
- There is only `post` step.
- `forallE` and `lam` are not be handled in a cascading way. -/

elab "silentAesop" : tactic => do
  let saved ← getThe Core.State
  modifyThe Core.State fun st => { st with messages := {} }
  try
    evalTactic (← `(tactic| aesop))
  finally
    modifyThe Core.State fun st => { st with messages := saved.messages }

scoped macro "prove_subtype_by_guessing_simple_solver'" : tactic =>
  `(tactic| (intros ; try simp at * ; try (silentAesop <;> (solve | omega | grind))))

private partial def simpleBottomUpTraverse' {m} [Monad m] [MonadLiftT MetaM m] [MonadControlT MetaM m]
  (e : Expr) (step : Array Expr → Expr → m Unit)
  (skipConstInApp := false)
  : m Unit := go #[] e
where go (fvars : Array Expr) (e : Expr) : m Unit := do
  let goWhole? ← do
    match e with
    | .forallE nm d b bi  => do
      go fvars d
      withLocalDecl nm bi d fun x => do
        let fvars' := fvars.push x
        go fvars' (b.instantiate1 x)
      pure true
    | .lam nm d b bi      => do
      withLocalDecl nm bi d fun x => do
        go fvars d
        let fvars' := fvars.push x
        go fvars' (b.instantiate1 x)
      pure true
    | .app ..             =>
      e.withApp fun f args => do
        unless skipConstInApp && f.isConst do go fvars f
        for arg in args do go fvars arg
      pure true
    | .mdata _ b          => go fvars b ; pure false
    | _                   => pure false
  if goWhole? then step fvars e

private inductive TCSynthAuxTacticResult' where
  | notApplicable (ex : MessageData)
  | notTarget
  | doneWithoutAux (inst : Expr)
  | doneWithAux (inst : Expr)
  | auxFailed (ex : MessageData)
deriving Inhabited

private instance : ToMessageData TCSynthAuxTacticResult' where
  toMessageData
    | .notApplicable ex => m!"not applicable:\n{ex}"
    | .notTarget        => "not target"
    | .doneWithoutAux inst  => m!"done without aux:\n{inst}"
    | .doneWithAux inst => m!"done with aux:\n{inst}"
    | .auxFailed ex     => m!"aux failed:\n{ex}"

private abbrev TCSynthAuxTacticM' := StateT (Array Expr) TacticM

/-- Try synthesizing `target` with optional auxiliary instances. -/
private def trySynthWithoutAux' (target : Expr) (insts : Array Expr := #[]) : TacticM (Option Expr) := do
  if insts.isEmpty then
    try
      let inst ← synthInstance target
      let inst ← instantiateMVars inst
      return some inst
    catch _ =>
      return none
  else
    try
      let goriginal ← mkFreshExprMVar target
      let mut gres := goriginal.mvarId!
      let mut fvars' := #[]
      for inst in insts do
        let (fv, g') ← gres.let (← mkFreshUserName `inst) inst
        fvars' := fvars'.push fv
        gres := g'
      let inst ← gres.withContext do synthInstance target
      let inst ← gres.withContext do instantiateMVars inst
      let inst ← gres.withContext do zetaDeltaFVars inst fvars'
      return some inst
    catch _ =>
      return none

/-- Try synthesizing `target` using the local instances `insts` and
a quasi-instance constructed by `qinst`. -/
private def trySynthByAux' (fvars insts : Array Expr) (target : Expr)
  (qinst : MetaM Expr)
  (subtypeGoalTactic : TSyntax `tactic) : TacticM (Sum Expr MessageData) := do
  let (fvars', g) ← do
    let goriginal ← mkFreshExprMVar target
    let mut gres := goriginal.mvarId!
    let mut fvars' := #[]
    for inst in insts do
      let (fv, g') ← gres.let (← mkFreshUserName `inst) inst
      fvars' := fvars'.push fv
      gres := g'
    pure (fvars', gres)
  try
    let qinst ← g.withContext qinst
    let res ← g.apply (cfg := { allowSynthFailures := true }) qinst
    let (gdecpred?, g') ← match res with
      | [g1, g2]  =>
        let tmp ← g1.getType''
        if tmp.getAppFn'.isConstOf ``Subtype then pure (some g2, g1) else pure (some g1, g2)
      | [g']      => pure (none, g')
      | _         => throwError "applying {qinst} to {target} failed; expected 1 or 2 goals, got {res}"
    if let some gdecpred := gdecpred? then
      let goals ← evalTacticAt (← `(tactic| intros ; infer_instance )) gdecpred
      unless goals.isEmpty do throwError "failed to synthesize {gdecpred} by `intros ; infer_instance`"
    let goals ← evalTacticAt subtypeGoalTactic g'
    unless goals.isEmpty && (← g'.isAssigned) do throwError "failed to synthesize {g'} by `prove_subtype_by_guessing`"
    let inst ← instantiateMVars (Expr.mvar g)
    if inst.hasMVar then throwError "synthesized auxiliary instance {g} has metavariables"
    let inst ← mkLambdaFVars fvars inst (usedOnly := true)
    let inst ← g.withContext do zetaDeltaFVars inst fvars'
    return .inl inst
  catch ex =>
    return .inr ex.toMessageData

private def auxSynthesizeCore' (fvars : Array Expr) (e : Expr) (tcName : Name)
  (choices : List (MetaM Expr × TSyntax `tactic)) (addSimpleSynthToState : Bool := false) : TCSynthAuxTacticM' TCSynthAuxTacticResult' := do
  let dec ← mkAppM tcName #[e]

  -- Try simple synthesis first (without any auxiliary tactics)
  let insts : Array Expr ← get
  let instOpt ← trySynthWithoutAux' dec insts

  match instOpt with
  | some inst =>
    if addSimpleSynthToState then
      let inst ← mkLambdaFVars fvars inst (usedOnly := true)
      modify (fun s => s.push inst)
      return .doneWithAux inst
    else
      return .doneWithoutAux inst
  | none => pure ()

  -- If simple synthesis failed, try each choice with auxiliary tactics
  let mut results : Array TCSynthAuxTacticResult' := #[]
  for (qinst, tac) in choices do
    let res ← trySynthByAux' fvars insts dec qinst tac

    match res with
    | .inl inst =>
      modify (fun (s : Array Expr) => s.push inst)
      return .doneWithAux inst
    | .inr ex =>
      results := results.push (.auxFailed ex)

  -- If no choices were provided or all failed, return appropriate error
  if results.isEmpty then
    return .auxFailed m!"No synthesis strategies available for {e}"
  else
    return results[0]!

/-!
## Testable quasi-instances for bounded quantifiers

The following defines a bunch of _quasi-instances_ for deriving
`Testable` instances that start with bounded quantifiers. They are
"quasi" since they have some non-trivial premises that cannot be
handled by the usual instance synthesis procedure.
-/

section NatBounds

variable {p : Nat → Prop} [∀ i, Testable (p i)]

/-- Convert an unbounded universal quantifier to a bounded one for Testable.
If we can show that `(∀ i, i < n → p i) → ∀ i, p i`, then we can test
`∀ i, p i` by testing the bounded version. -/
def Testable.Nat.testableFromBallLT (n : Nat)
  (h : (∀ i, i < n → p i) → ∀ i, p i) :
  Testable (∀ i, p i) where
  run cfg _ := do
    if h_n_zero : n = 0 then
      -- Empty domain case: (∀ i, i < 0 → p i) is vacuously true
      return TestResult.success (PSum.inr (h (fun i hi => by
        rw [h_n_zero] at hi
        exact absurd hi (Nat.not_lt_zero i))))
    else
      -- Systematically test each value from 0 to n-1
      let rec checkAll (x : Nat) (hAllBefore : ∀ y, y < x → p y) :
          Gen (TestResult (∀ i, p i)) := do
        if h_ge : x ≥ n then
          -- We've tested all values [0, n) and all passed
          return TestResult.success (PSum.inr (h (fun i hi => by
            have hi_lt_x : i < x := Nat.lt_of_lt_of_le hi h_ge
            exact hAllBefore i hi_lt_x)))
        else
          have hlt : x < n := Nat.lt_of_not_ge h_ge
          -- Test p x
          let testResult ← @Testable.run (p x) (inferInstance) cfg false
          match testResult with
          | TestResult.success (PSum.inr hP) =>
            -- p x holds, continue to next value
            checkAll (x + 1) (fun y hy => by
              cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hy) with
              | inl h_lt => exact hAllBefore y h_lt
              | inr h_eq => rw [h_eq]; exact hP)
          | TestResult.success (PSum.inl _) =>
            -- Can't determine p x
            return TestResult.gaveUp cfg.numInst
          | TestResult.failure h_not_P _ _ =>
            -- Found a counterexample: p x is false but x < n
            return TestResult.failure
              (fun h_forall => h_not_P (h_forall x))
              [s!"Counterexample: x = {x}"]
              1
          | TestResult.gaveUp count =>
            return TestResult.gaveUp count
      checkAll 0 (fun _ hi => absurd hi (Nat.not_lt_zero _))

def Testable.Nat.testableFromBallLT' (h : { n : Nat // (∀ i, i < n → p i) → ∀ i, p i }) :
  Testable (∀ i, p i) := Testable.Nat.testableFromBallLT h.val h.property

def Testable.Nat.testableFromBallLE (n : Nat)
  (h : (∀ i, i ≤ n → p i) → ∀ i, p i) :
  Testable (∀ i, p i) where
  run cfg _ := do
    -- Systematically test each value from 0 to n (inclusive)
    let rec checkAll (x : Nat) (hAllBefore : ∀ y, y < x → p y) :
        Gen (TestResult (∀ i, p i)) := do
      if h_gt : x > n then
        -- We've tested all values [0, n] and all passed
        return TestResult.success (PSum.inr (h (fun i hi => by
          have hi_le_n : i ≤ n := hi
          have hi_lt_x : i < x := Nat.lt_of_le_of_lt hi_le_n h_gt
          exact hAllBefore i hi_lt_x)))
      else
        have hle : x ≤ n := Nat.le_of_not_gt h_gt
        -- Test p x
        let testResult ← @Testable.run (p x) (inferInstance) cfg false
        match testResult with
        | TestResult.success (PSum.inr hP) =>
          -- p x holds, continue to next value
          checkAll (x + 1) (fun y hy => by
            cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hy) with
            | inl h_lt => exact hAllBefore y h_lt
            | inr h_eq => rw [h_eq]; exact hP)
        | TestResult.success (PSum.inl _) =>
          -- Can't determine p x
          return TestResult.gaveUp cfg.numInst
        | TestResult.failure h_not_P _ _ =>
          -- Found a counterexample: p x is false but x ≤ n
          return TestResult.failure
            (fun h_forall => h_not_P (h_forall x))
            [s!"Counterexample: x = {x}"]
            1
        | TestResult.gaveUp count =>
          return TestResult.gaveUp count
    termination_by n + 1 - x
    checkAll 0 (fun _ hi => absurd hi (Nat.not_lt_zero _))

def Testable.Nat.testableFromBallLE' (h : { n : Nat // (∀ i, i ≤ n → p i) → ∀ i, p i }) :
  Testable (∀ i, p i) := Testable.Nat.testableFromBallLE h.val h.property

/-- Convert an unbounded existential quantifier to a bounded one for Testable. -/
def Testable.Nat.testableFromExistsLT (n : Nat)
  (h : (∃ i, p i) → (∃ i, i < n ∧ p i)) :
  Testable (∃ i, p i) where
  run cfg _ := do
    if h_n_zero : n = 0 then
      -- Empty domain case: ∃ i, i < 0 ∧ p i is vacuously false
      return TestResult.failure
        (fun h_exists =>
          let ⟨w, hw_lt, _⟩ := h h_exists
          by rw [h_n_zero] at hw_lt; exact Nat.not_lt_zero w hw_lt)
        ["empty domain: n = 0"]
        0
    else
      -- Systematically try each value from 0 to n-1
      let rec findWitness (x : Nat)
        (hAllBefore : ∀ y, y < x → ¬p y) : Gen (TestResult (∃ i, p i)) := do
        if h_ge : x ≥ n then
          -- We've tried all values [0, n) and none worked
          return TestResult.failure
            (fun h_exists => by
              let ⟨w, hw_lt, hw_p⟩ := h h_exists
              have hw_lt_x : w < x := Nat.lt_of_lt_of_le hw_lt h_ge
              have h_not_p_w := hAllBefore w hw_lt_x
              exact h_not_p_w hw_p)
            [s!"No witness found in [0, {n})"]
            n
        else
          have hlt : x < n := Nat.lt_of_not_ge h_ge
          -- Test p x
          let testResult ← @Testable.run (p x) (inferInstance) cfg false
          match testResult with
          | TestResult.success (PSum.inr hP) =>
            -- Found a witness!
            return TestResult.success (PSum.inr ⟨x, hP⟩)
          | TestResult.success (PSum.inl _) =>
            return TestResult.gaveUp cfg.numInst
          | TestResult.failure hNotPx _ _ =>
            -- p x is false, continue to next value
            findWitness (x + 1) (fun y hy => by
              cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hy) with
              | inl h_lt => exact hAllBefore y h_lt
              | inr h_eq => rw [h_eq]; exact hNotPx)
          | TestResult.gaveUp count =>
            return TestResult.gaveUp count
      termination_by n - x
      findWitness 0 (fun _ hi => absurd hi (Nat.not_lt_zero _))

def Testable.Nat.testableFromExistsLT' (h : { n : Nat // (∃ i, p i) → (∃ i, i < n ∧ p i) }) :
  Testable (∃ i, p i) := Testable.Nat.testableFromExistsLT h.val h.property

def Testable.Nat.testableFromExistsLE (n : Nat)
  (h : (∃ i, p i) → (∃ i, i ≤ n ∧ p i)) :
  Testable (∃ i, p i) where
  run cfg _ := do
    -- Systematically try each value from 0 to n (inclusive)
    let rec findWitness (x : Nat)
      (hAllBefore : ∀ y, y < x → ¬p y) : Gen (TestResult (∃ i, p i)) := do
      if h_gt : x > n then
        -- We've tried all values [0, n] and none worked
        return TestResult.failure
          (fun h_exists => by
            let ⟨w, hw_le, hw_p⟩ := h h_exists
            have hw_lt_x : w < x := Nat.lt_of_le_of_lt hw_le h_gt
            have h_not_p_w := hAllBefore w hw_lt_x
            exact h_not_p_w hw_p)
          [s!"No witness found in [0, {n}]"]
          (n + 1)
      else
        have hle : x ≤ n := Nat.le_of_not_gt h_gt
        -- Test p x
        let testResult ← @Testable.run (p x) (inferInstance) cfg false
        match testResult with
        | TestResult.success (PSum.inr hP) =>
          -- Found a witness!
          return TestResult.success (PSum.inr ⟨x, hP⟩)
        | TestResult.success (PSum.inl _) =>
          return TestResult.gaveUp cfg.numInst
        | TestResult.failure hNotPx _ _ =>
          -- p x is false, continue to next value
          findWitness (x + 1) (fun y hy => by
            cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hy) with
            | inl h_lt => exact hAllBefore y h_lt
            | inr h_eq => rw [h_eq]; exact hNotPx)
        | TestResult.gaveUp count =>
          return TestResult.gaveUp count
    termination_by n + 1 - x
    findWitness 0 (fun _ hi => absurd hi (Nat.not_lt_zero _))

def Testable.Nat.testableFromExistsLE' (h : { n : Nat // (∃ i, p i) → (∃ i, i ≤ n ∧ p i) }) :
  Testable (∃ i, p i) := Testable.Nat.testableFromExistsLE h.val h.property

end NatBounds

section IntBounds

variable {p : Int → Prop} [∀ i, Testable (p i)]

def Testable.Int.testableFromBallLELE (lo hi : Int)
  (h : (∀ i, lo ≤ i → i ≤ hi → p i) → ∀ i, p i) :
  Testable (∀ i, p i) where
  run cfg _ := do
    if h_empty : hi < lo then
      -- Empty domain case: (∀ i, lo ≤ i → i ≤ hi → p i) is vacuously true
      return TestResult.success (PSum.inr (h (fun i hi_lo hi_hi => by
        omega)))
    else
      -- Systematically test each value from lo to hi (inclusive)
      let rec checkAll (x : Int) (hAllBefore : ∀ y, lo ≤ y → y < x → p y) :
          Gen (TestResult (∀ i, p i)) := do
        if h_gt : x > hi then
          -- We've tested all values [lo, hi] and all passed
          return TestResult.success (PSum.inr (h (fun i hi_lo hi_hi => by
            have hi_lt_x : i < x := Int.lt_of_le_of_lt hi_hi h_gt
            exact hAllBefore i hi_lo hi_lt_x)))
        else
          have hle : x ≤ hi := Int.le_of_not_gt h_gt
          -- Test p x (we know lo ≤ x from the starting point and induction)
          let testResult ← @Testable.run (p x) (inferInstance) cfg false
          match testResult with
          | TestResult.success (PSum.inr hP) =>
            -- p x holds, continue to next value
            checkAll (x + 1) (fun y hy_lo hy_lt => by
              if h_eq : y = x then
                rw [h_eq]; exact hP
              else
                have hy_lt_x : y < x := by omega
                exact hAllBefore y hy_lo hy_lt_x)
          | TestResult.success (PSum.inl _) =>
            return TestResult.gaveUp cfg.numInst
          | TestResult.failure h_not_P _ _ =>
            -- Found a counterexample
            return TestResult.failure
              (fun h_forall => h_not_P (h_forall x))
              [s!"Counterexample: x = {x}"]
              1
          | TestResult.gaveUp count =>
            return TestResult.gaveUp count
      termination_by (hi + 1 - x).toNat
      decreasing_by
        simp_wf
        omega
      checkAll lo (fun y hy_lo hy_lt => absurd hy_lt (Int.not_lt.mpr hy_lo))

def Testable.Int.testableFromBallLELE' (h : { lohi : Int × Int // (∀ i, lohi.1 ≤ i → i ≤ lohi.2 → p i) → ∀ i, p i }) :
  Testable (∀ i, p i) :=
  let ⟨(lo, hi), h_prop⟩ := h
  Testable.Int.testableFromBallLELE lo hi h_prop

/-- Testable instance for existential with Int bounds using systematic search. -/
def Testable.Int.testableFromExistsLELE (lo hi : Int)
  (h : (∃ i, p i) → (∃ i, lo ≤ i ∧ i ≤ hi ∧ p i)) :
  Testable (∃ i, p i) where
  run cfg _ := do
    if h_empty : hi < lo then
      -- Empty domain case: ∃ i, lo ≤ i ∧ i ≤ hi ∧ p i is vacuously false
      return TestResult.failure
        (fun h_exists =>
          let ⟨w, hw_lo, hw_hi, _⟩ := h h_exists
          by omega)
        [s!"empty domain: hi ({hi}) < lo ({lo})"]
        0
    else
      -- Systematically try each value from lo to hi
      let rec findWitness (x : Int) (hx_ge : lo ≤ x)
        (hAllBefore : ∀ y, lo ≤ y → y < x → ¬p y) : Gen (TestResult (∃ i, p i)) := do
        if h_gt : x > hi then
          -- We've tried all values [lo, hi] and none worked
          return TestResult.failure
            (fun h_exists => by
              let ⟨w, hw_lo, hw_hi, hw_p⟩ := h h_exists
              have hw_lt_x : w < x := by omega
              have h_not_p_w := hAllBefore w hw_lo hw_lt_x
              exact h_not_p_w hw_p)
            [s!"No witness found in [{lo}, {hi}]"]
            ((hi - lo + 1).toNat)
        else
          have hle : x ≤ hi := Int.le_of_not_gt h_gt
          -- Test p x
          let testResult ← @Testable.run (p x) (inferInstance) cfg false
          match testResult with
          | TestResult.success (PSum.inr hP) =>
            -- Found a witness!
            return TestResult.success (PSum.inr ⟨x, hP⟩)
          | TestResult.success (PSum.inl _) =>
            return TestResult.gaveUp cfg.numInst
          | TestResult.failure hNotPx _ _ =>
            -- p x is false, continue to next value
            findWitness (x + 1) (by omega) (fun y hy_lo hy_lt => by
              by_cases h_eq : y = x
              · rw [h_eq]; exact hNotPx
              · have hy_lt_x : y < x := by omega
                exact hAllBefore y hy_lo hy_lt_x)
          | TestResult.gaveUp count =>
            return TestResult.gaveUp count
      termination_by (hi + 1 - x).toNat
      decreasing_by simp_wf; omega
      findWitness lo (Int.le_refl lo) (fun y hy_lo hy_lt => absurd hy_lt (Int.not_lt.mpr hy_lo))

def Testable.Int.testableFromExistsLELE' (h : { lohi : Int × Int // (∃ i, p i) → (∃ i, lohi.1 ≤ i ∧ i ≤ lohi.2 ∧ p i) }) :
  Testable (∃ i, p i) :=
  let ⟨(lo, hi), h_prop⟩ := h
  Testable.Int.testableFromExistsLELE lo hi h_prop

end IntBounds

section TCSynthTestableAuxTactic

/-!
Similar to the Decidable version, we implement auxiliary instance synthesis
for Testable instances with bounded quantifiers.
-/

/-- Perform auxiliary instance synthesis for a proposition `e`
of the form `NamedBinder var (∀ x, p x)`. -/
private def auxTestSynthesizeForall (fvars : Array Expr) (e : Expr) : TCSynthAuxTacticM' TCSynthAuxTacticResult' := do
  -- Check if e is of the form: NamedBinder var (∀ ...)
  let e := e.consumeMData
  unless e.isAppOf `Plausible.NamedBinder do
    return .notApplicable m!"not a NamedBinder"

  let some body := e.getAppArgs[1]? | return .notApplicable m!"NamedBinder has no body"
  let Expr.forallE _nm _d _b _bi := body | return .notApplicable m!"NamedBinder body is not a ∀"

  auxSynthesizeCore' fvars e ``Testable [] (addSimpleSynthToState := true)

/-- Perform auxiliary instance synthesis for a proposition `e`
of the form `∃ i, p i`. -/
private def auxTestSynthesizeExists (fvars : Array Expr) (e : Expr) : TCSynthAuxTacticM' TCSynthAuxTacticResult' := do
  let e := e.consumeMData
  let_expr Exists d p := e | return .notApplicable m!"not an ∃"
  let generalSolver ← `(tactic| prove_subtype_by_guessing_simple_solver' )
  let handlers : List (Expr × List (MetaM Expr × TSyntax `tactic)) :=
    [ (mkConst ``Nat,
        [(mkAppOptM ``Testable.Nat.testableFromExistsLT' #[.some p],
          ← `(tactic| prove_subtype_by_guessing_nat_lt $generalSolver )),
         (mkAppOptM ``Testable.Nat.testableFromExistsLE' #[.some p],
          ← `(tactic| prove_subtype_by_guessing_nat_le $generalSolver ))]),
      (mkConst ``Int,
        [(mkAppOptM ``Testable.Int.testableFromExistsLELE' #[.some p],
          ← `(tactic| prove_subtype_by_guessing_int_lele $generalSolver ))]) ]
  let some (_, choices) ← handlers.findM? fun a => isDefEq d a.1
    | return .notTarget
  auxSynthesizeCore' fvars e ``Testable choices (addSimpleSynthToState := true)

/-- Synthesize auxiliary `Testable` instances by traversing `e`
in a bottom-up manner. Returns the array of synthesized instances. -/
partial def auxTestSynth (e : Expr) : TacticM (Array Expr) := do
  let mnd := simpleBottomUpTraverse' (m := StateT (Array Expr) TacticM) e
    (skipConstInApp := true)
    fun fvars e => do
      unless ← Meta.isProp e do return
      let r ← auxTestSynthesizeForall fvars e
      unless r matches .notApplicable _ do
        trace[Loom.debug] m!"[auxTestSynthesizeForall] result for {e}: {r}"
      let r ← auxTestSynthesizeExists fvars e
      unless r matches .notApplicable _ do
        trace[Loom.debug] m!"[auxTestSynthesizeExists] result for {e}: {r}"
  let (_, insts) ← mnd.run #[]
  trace[Loom.debug] m!"[auxTestSynth] synthesized {insts.size} instances"
  return insts

elab "infer_aux_testable_instance" : tactic => do
  withMainContext do
    evalTactic (← `(tactic| dsimp -$(mkIdent `failIfUnchanged) only [$(mkIdent `loomAbstractionSimp):ident] ))
  let tgt ← getMainTarget
  let insts ← auxTestSynth tgt
  -- Add instances using mv.let
  for inst in insts do
    let mv ← getMainGoal
    let (_, mv') ← mv.let (← mkFreshUserName `inst) inst
    replaceMainGoal [mv']

end TCSynthTestableAuxTactic

end TestableHeuristics

section CustomPlausible

open Lean Meta Elab Tactic
open Parser.Tactic
open Plausible Decorations

syntax (name := plausibleSyntax) "plausible'" (config)? : tactic

partial def addDecorationsLoom (e : Expr) : MetaM Expr :=
  Meta.transform e fun expr => do
    if not (← Meta.inferType expr).isProp then
      if expr.isLambda then return .continue
      return .done expr
    else if let Expr.forallE name type body data := expr then
      let newType ← addDecorationsLoom type
      let newBody ← Meta.withLocalDecl name data type fun fvar => do
        return (← addDecorationsLoom (body.instantiate1 fvar)).abstract #[fvar]
      let rest := Expr.forallE name newType newBody data
      return .done <| (← Meta.mkAppM `Plausible.NamedBinder #[mkStrLit name.toString, rest])
    else
      return .continue

/-- Try to normalize `tgt` and synthesize a `Testable` instance.
    Returns `none` (without throwing) if synthesis fails for any reason. -/
def tryLoomMkTestable (tgt : Expr) : TacticM (Option (Expr × Expr)) := do
  let mvar ← mkFreshExprMVar tgt
  let savedGoals ← getGoals
  setGoals [mvar.mvarId!]
  let result ← try
    evalTactic (← `(tactic| dsimp -$(mkIdent `failIfUnchanged) only [$(mkIdent `loomAbstractionSimp):ident] ))
    evalTactic (← `(tactic| try simp only [imp_iff_not_or, iff_iff_and_or_not_and_not, forall_imp_iff_exists_imp, not_and, not_or, not_forall, not_exists, not_not]))
    evalTactic (← `(tactic| try simp only [Array.getElem!_eq_getD]))
    let g ← getMainGoal
    g.withContext do
      let tgtNorm ← g.getType
      trace[Loom.debug] m!"Normalized goal: {tgtNorm}"
      let tgt' ← addDecorationsLoom tgtNorm
      trace[Loom.debug] m!"Add decorations: {tgt'}"
      let auxInsts ← auxTestSynth tgt'
      let target ← mkAppM ``Testable #[tgt']
      let inst? ← trySynthWithoutAux' target auxInsts
      match inst? with
      | none => pure none
      | some inst =>
          trace[Loom.debug] "Using instance:\n  {inst}"
          pure (some (tgt', inst))
  catch _ => pure none
  try admitGoal mvar.mvarId! catch _ => pure ()
  setGoals savedGoals
  return result

/-- Normalize a proposition and synthesize a `Testable` instance.
    Creates a synthetic goal, runs tactic normalizations (dsimp + simp) to simplify
    `tgt`, adds Plausible decorations, then synthesizes a `Testable` instance.
    Returns `(decoratedTgt, instance)`.
    Throws a descriptive error if synthesis fails. -/
def loomMkTestable (tgt : Expr) : TacticM (Expr × Expr) := do
  match ← tryLoomMkTestable tgt with
  | some r => return r
  | none =>
    throwError "\
        Failed to synthesize a `testable` instance for `{tgt}`.\
        \nWhat to do:\
        \n1. make sure that the types you are using have `Plausible.SampleableExt` instances\
        \n (you can use `#sample my_type` if you are unsure);\
        \n2. make sure that the relations and predicates that your proposition use are decidable;\
        \n3. make sure that instances of `Plausible.Testable` exist that, when combined,\
        \n  apply to your proposition.\
        \n\
        \nUse `set_option trace.Meta.synthInstance true` to understand what instances are missing.\
        \n\
        \nTry this:\
        \nset_option trace.Meta.synthInstance true\
        \n#synth Plausible.Testable ({tgt})"

/-- Try to synthesize a `Decidable` instance for `tgt` using Loom's decidability tactics:
      `repeat' refine @instDecidableAnd _ _ ?_ ?_`
      `all_goals (try (infer_aux_decidable_instance ; infer_instance))`
    Returns `none` (without throwing) if synthesis fails. -/
def tryLoomMkDecidable (tgt : Expr) : TacticM (Option Expr) := do
  let target ← mkAppM ``Decidable #[tgt]
  let mvar ← mkFreshExprMVar target
  let savedGoals ← getGoals
  setGoals [mvar.mvarId!]
  let result ← try
    evalTactic (← `(tactic| repeat' refine @instDecidableAnd _ _ ?_ ?_))
    evalTactic (← `(tactic| all_goals (try (infer_aux_decidable_instance ; infer_instance))))
    let remaining ← getGoals
    if !remaining.isEmpty then pure none
    else
      let inst ← instantiateMVars mvar
      pure (if inst.hasMVar then none else some inst)
  catch _ => pure none
  try admitGoal mvar.mvarId! catch _ => pure ()
  setGoals savedGoals
  return result

/-- Synthesize a `Decidable` instance for `tgt` using Loom's decidability tactics.
    Throws if synthesis fails. -/
def loomMkDecidable (tgt : Expr) : TacticM Expr := do
  match ← tryLoomMkDecidable tgt with
  | some inst => return inst
  | none => throwError "Failed to synthesize a `Decidable` instance for `{tgt}`."

/-- Test a Prop-typed expression `tgt` under the current MetaM local context.
    Normalizes and synthesizes a `Testable` instance via `loomMkTestable`, then
    runs the plausible check.  Does NOT touch the caller's goal state. -/
def loomTestExpr (tgt : Expr) (cfg : Plausible.Configuration) : TacticM Unit := do
  let cfg := { cfg with
    traceDiscarded := cfg.traceDiscarded || (← isTracingEnabledFor `plausible.discarded),
    traceSuccesses := cfg.traceSuccesses || (← isTracingEnabledFor `plausible.success),
    traceShrink := cfg.traceShrink || (← isTracingEnabledFor `plausible.shrink.steps),
    traceShrinkCandidates := cfg.traceShrinkCandidates
      || (← isTracingEnabledFor `plausible.shrink.candidates) }
  let (tgt', inst) ← loomMkTestable tgt
  let e ← mkAppOptM ``Testable.check #[tgt, toExpr cfg, tgt', inst]
  trace[plausible.decoration] "[testable decoration]\n  {tgt'}"
  let code ← unsafe evalExpr (CoreM PUnit) (mkApp (mkConst ``CoreM) (mkConst ``PUnit [1])) e
  _ ← code

elab_rules : tactic | `(tactic| plausible' $[$cfg]?) => withMainContext do
  let cfg ← elabConfig (mkOptionalNode cfg)
  -- Convert the tactic goal (with its local context) into a closed Prop expression
  let (_, g) ← (← getMainGoal).revert ((← getLocalHyps).map (Expr.fvarId!))
  let tgt ← g.getType
  trace[Loom.debug] m!"Original goal: {tgt}"
  g.withContext do
  loomTestExpr tgt cfg
  admitGoal g

end CustomPlausible

section MutationTesting

open Plausible

/-- Types that support mutation-based testing.
    `mutate x` generates a "nearby" variant of `x`, used to build
    a corpus-guided fuzzing loop on top of `plausible'`. -/
class Mutatable (α : Type u) where
  mutate : α → Gen α

namespace Mutatable

instance : Mutatable Bool where
  mutate _ := Gen.chooseAny Bool

instance : Mutatable Int where
  mutate x := do
    -- op: 0 = add/sub small delta, 1 = negate, 2 = multiply by 2–5, 3 = divide by 2–5
    let op ← Gen.choose Nat 0 3 (by omega)
    if op.val == 0 then
      let delta ← Gen.choose Nat 0 20 (by omega)
      let neg ← Gen.chooseAny Bool
      return if neg then x - (delta : Int) else x + (delta : Int)
    else if op.val == 1 then
      return -x
    else if op.val == 2 then
      let factor ← Gen.choose Nat 2 5 (by omega)
      return x * (factor : Int)
    else
      let factor ← Gen.choose Nat 2 5 (by omega)
      return x / (factor : Int)

instance : Mutatable Nat where
  mutate x := do
    -- op: 0 = add/sub small delta, 1 = multiply by 2–5, 2 = divide by 2–5
    let op ← Gen.choose Nat 0 2 (by omega)
    if op.val == 0 then
      let delta ← Gen.choose Nat 0 10 (by omega)
      let sub ← Gen.chooseAny Bool
      return if sub then x - delta else x + delta
    else if op.val == 1 then
      let factor ← Gen.choose Nat 2 5 (by omega)
      return x * factor
    else
      let factor ← Gen.choose Nat 2 5 (by omega)
      return x / factor

instance [Mutatable α] [Mutatable β] : Mutatable (α × β) where
  mutate pair := do
    let flipA ← Gen.chooseAny Bool
    if flipA then
      return (← mutate pair.1, pair.2)
    else
      return (pair.1, ← mutate pair.2)

/-- Homogeneous pair: additionally supports swapping the two components. -/
instance (priority := 2000) [Mutatable α] : Mutatable (α × α) where
  mutate pair := do
    -- op: 0 = mutate fst, 1 = mutate snd, 2 = swap
    let op ← Gen.choose Nat 0 2 (by omega)
    if op.val == 0 then
      return (← mutate pair.1, pair.2)
    else if op.val == 1 then
      return (pair.1, ← mutate pair.2)
    else
      return (pair.2, pair.1)

instance [Mutatable α] [Inhabited α] : Mutatable (List α) where
  mutate xs := do
    if xs.isEmpty then return xs
    let op ← Gen.choose Nat 0 4 (by omega)
    if op.val == 0 then
      -- Mutate a random element
      let i ← Gen.choose Nat 0 (xs.length - 1) (by omega)
      let x' ← mutate xs[i.val]!
      return xs.set i.val x'
    else if op.val == 1 then
      -- Drop a random element
      let i ← Gen.choose Nat 0 (xs.length - 1) (by omega)
      return xs.eraseIdx i.val
    else if op.val == 2 then
      -- Duplicate a random element
      let i ← Gen.choose Nat 0 (xs.length - 1) (by omega)
      return xs.insertIdx i.val xs[i.val]!
    else if op.val == 3 then
      -- Swap two random elements
      let i ← Gen.choose Nat 0 (xs.length - 1) (by omega)
      let j ← Gen.choose Nat 0 (xs.length - 1) (by omega)
      return (xs.set i.val xs[j.val]!).set j.val xs[i.val]!
    else
      -- Append a mutated copy of a random element
      let i ← Gen.choose Nat 0 (xs.length - 1) (by omega)
      let x' ← mutate xs[i.val]!
      return xs ++ [x']

instance [Mutatable α] [Inhabited α] : Mutatable (Array α) where
  mutate arr := do
    if arr.isEmpty then return arr
    let op ← Gen.choose Nat 0 4 (by omega)
    if op.val == 0 then
      -- Mutate a random element
      let i ← Gen.choose Nat 0 (arr.size - 1) (by omega)
      let x' ← mutate arr[i.val]!
      return arr.set! i.val x'
    else if op.val == 1 then
      -- Drop a random element
      let i ← Gen.choose Nat 0 (arr.size - 1) (by omega)
      return arr.eraseIdx! i.val
    else if op.val == 2 then
      -- Duplicate a random element
      let i ← Gen.choose Nat 0 (arr.size - 1) (by omega)
      return arr.insertIdx i.val arr[i.val]!
    else if op.val == 3 then
      -- Swap two random elements
      let i ← Gen.choose Nat 0 (arr.size - 1) (by omega)
      let j ← Gen.choose Nat 0 (arr.size - 1) (by omega)
      return (arr.set! i.val arr[j.val]!).set! j.val arr[i.val]!
    else
      -- Append a mutated copy of a random element
      let i ← Gen.choose Nat 0 (arr.size - 1) (by omega)
      let x' ← mutate arr[i.val]!
      return arr.push x'

instance : Mutatable Char where
  mutate c := do
    let delta ← Gen.choose Nat 0 5 (by omega)
    let neg ← Gen.chooseAny Bool
    let newNat := if neg then c.val.toNat - delta else c.val.toNat + delta
    return Char.ofNat newNat

instance : Mutatable String where
  mutate s := do
    let chars' ← Mutatable.mutate s.toList
    return String.mk chars'

end Mutatable

-- ─────────────────────────────────────────────────────────────────────────────
-- Layer 2: Corpus-based mutation test loop
-- ─────────────────────────────────────────────────────────────────────────────

/-- The outcome of one iteration in the mutation test loop. -/
inductive IterResult where
  /-- A counterexample was found; carry the variable bindings and shrink count. -/
  | counterexample (msgs : List String) (shrinks : Nat) : IterResult
  /-- The guard did not hold (e.g. `result = expected`).
      These values are added to the corpus as useful seeds. -/
  | discarded : IterResult
  /-- The proposition held non-trivially (guard held, conclusion held). -/
  | passed : IterResult

/-- Configuration for mutation-based testing. -/
structure LoomMutConfig where
  /-- Underlying Plausible configuration (numInst, maxSize, …). -/
  inner : Plausible.Configuration := {}
  /-- Out of `mutOutOf` random choices, `mutProb` many trigger a corpus
      mutation; the rest do a fresh sample. Default: 1/2 = 50 %. -/
  mutProb  : Nat := 1
  mutOutOf : Nat := 2
  /-- Maximum number of values stored in the corpus. -/
  maxCorpusSize : Nat := 50
  /-- Selection weight given to each user-supplied seed relative to
      corpus entries discovered during fuzzing (weight 1 each).
      Higher values mean seeds are picked more often. Default: 3. -/
  seedWeight : Nat := 15
  /-- When true, print each tested value to stderr.
      Enable via `set_option trace.Loom.mut true`. -/
  traceValues : Bool := false

/-- Run a single `Testable` check at size `sz` and classify the outcome.
    Used as the building block for `testOne` in `loomMutLoop`. -/
def loomMutRunInner (p : Prop) (inst : Testable p)
    (cfg : Plausible.Configuration) (sz : Nat) : IO IterResult := do
  let result ← Gen.run (inst.run cfg false) sz
  return match result with
  | .failure _ msgs n => .counterexample msgs n
  | .success (.inl _) => .discarded
  | .success (.inr _) => .passed
  | .gaveUp _         => .discarded

/-- Core mutation test loop.

Maintains a corpus of "interesting" values and alternates between fresh
sampling (`genFresh`) and corpus-guided mutation (`mutate`).

Convention for `testOne`:
* `.discarded` — the guard failed (the value is added to the corpus as a seed).
* `.passed`    — the property held non-trivially; no corpus update.
* `.counterexample` — a counterexample was found; the loop throws an `IO.Error`.

Returns `()` when no counterexample is found after all iterations. -/
def loomMutLoop (α : Type) [Inhabited α] [ToString α]
    (genFresh : Gen α)
    (mutate   : α → Gen α)
    (testOne  : α → IO IterResult)
    (initialSeeds : Array α)
    (cfg      : LoomMutConfig) : IO (Array String) := do
  -- Corpus stores (value, weight).
  -- User-supplied seeds start at seedWeight; everything else starts at 1.
  let initCorpus : Array (α × Nat) := initialSeeds.map (·, cfg.seedWeight)
  let corpus   : IO.Ref (Array (α × Nat)) ← IO.mkRef initCorpus
  let traceLog : IO.Ref (Array String)    ← IO.mkRef #[]
  for iter in List.range cfg.inner.numInst do
    let sz := iter * cfg.inner.maxSize / (Nat.max cfg.inner.numInst 1)
    let curCorpus ← corpus.get
    -- Produce the next test value together with the weight it would receive
    -- if it ends up being added to the corpus.
    let pair : α × Nat ← do
      if curCorpus.isEmpty then
        pure (← Gen.run genFresh sz, 1)
      else do
        let coin ← Gen.run (Gen.choose Nat 0 (cfg.mutOutOf - 1) (by omega)) sz
        if coin.val < cfg.mutProb then
          -- Weighted selection proportional to each entry's weight.
          let totalWeight := curCorpus.foldl (fun acc (_, w) => acc + w) 0
          if totalWeight == 0 then
            pure (← Gen.run genFresh sz, 1)
          else
            let pick ← Gen.run (Gen.choose Nat 0 (totalWeight - 1) (by omega)) sz
            -- Walk the corpus to find the entry whose cumulative-weight range
            -- contains `pick`.
            let mut remaining := pick.val
            let mut chosen    := curCorpus[0]!
            for entry in curCorpus do
              if remaining < entry.2 then
                chosen := entry
                break
              remaining := remaining - entry.2
            let (parent, parentWeight) := chosen
            let v ← Gen.run (mutate parent) sz
            -- Child weight decays by 20 % per generation, floored at 1.
            pure (v, Nat.max 1 (parentWeight * 4 / 5))
        else
          -- Fresh sample: fixed weight 1.
          pure (← Gen.run genFresh sz, 1)
    let x          := pair.1
    let childWeight := pair.2
    let iterResult ← testOne x
    if cfg.traceValues then
      let tag := match iterResult with
        | .counterexample _ _ => "COUNTEREXAMPLE"
        | .discarded           => "discarded"
        | .passed              => "passed"
      traceLog.modify (·.push s!"iter {iter}: {x}  [{tag}]")
    match iterResult with
    | .counterexample msgs n =>
      let header := "Found a counter-example!"
      let counterExample := s!"counter example = {x}"
      let body   := msgs.foldl (fun acc m => acc ++ "\n  " ++ m) ""
      throw (IO.userError s!"{header}\n{counterExample}{body}\n(shrinks: {n})")
    | .discarded =>
      -- Guard-failing values are potential seeds (e.g. equal to `expected`)
      if curCorpus.size < cfg.maxCorpusSize then
        corpus.modify (·.push (x, childWeight))
    | .passed => pure ()
  return ← traceLog.get

end MutationTesting

-- ─────────────────────────────────────────────────────────────────────────────
-- Layer 3: plausible'_mut tactic
-- ─────────────────────────────────────────────────────────────────────────────

section MutationTestingTactic

open Lean Meta Elab Tactic
open Parser.Tactic
open Plausible Decorations

initialize registerTraceClass `Loom.mut

/-- `ToExpr` for `LoomMutConfig` so it can be passed through `unsafe evalExpr`. -/
private instance : ToExpr LoomMutConfig where
  toTypeExpr := mkConst ``LoomMutConfig
  toExpr cfg :=
    mkAppN (mkConst ``LoomMutConfig.mk)
      #[toExpr cfg.inner, toExpr cfg.mutProb, toExpr cfg.mutOutOf, toExpr cfg.maxCorpusSize, toExpr cfg.seedWeight, toExpr cfg.traceValues]

/-- Extract `(αType, body)` from `∀ _ : αType, body`, skipping `NamedBinder` wrappers. -/
private def extractOuterForall (e : Expr) : Option (Expr × Expr) :=
  match e with
  | Expr.forallE _ αType body _ => some (αType, body)
  | Expr.app (.app (.const ``NamedBinder _) _) inner => extractOuterForall inner
  | _ => none

/-- Like `plausible'` but maintains a corpus of interesting values and
    alternates between fresh sampling and corpus-guided mutation.

    Optional `seeds` pre-populate the corpus; useful when a known valid answer
    is available (e.g. the expected answer in a uniqueness test).

    ```lean
    plausible'_mut (seeds := [expected]) (config := { numInst := 100 })
    ``` -/
syntax (name := mutPlausibleSyntax) "plausible'_mut"
    ("(" "seeds" ":=" term ")")?
    (config)? : tactic

elab_rules : tactic | `(tactic| plausible'_mut $[( seeds := $seedsTerm )]? $[$cfg]?) => withMainContext do
  let plausibleCfg ← elabConfig (mkOptionalNode cfg)
  -- Revert all local hypotheses so the goal is a closed Prop
  let (_, g) ← (← getMainGoal).revert ((← getLocalHyps).map Expr.fvarId!)
  let tgt ← g.getType
  trace[Loom.debug] m!"plausible'_mut: tgt = {tgt}"
  g.withContext do
  -- Extract the outermost ∀ x : α
  let some (αType, body) := extractOuterForall tgt
    | throwError "plausible'_mut: goal must start with `∀ x : α, …`, got:\n  {tgt}"
  -- Synthesize instances for α.
  -- SampleableExt has two universe parameters (Sort u, Type v); use
  -- mkConstWithFreshMVarLevels so synthInstance can solve both levels.
  let sampleableInst ← synthInstance
    (mkApp (← mkConstWithFreshMVarLevels ``SampleableExt) αType)
  let mutableInst   ← synthInstance
    (mkApp (← mkConstWithFreshMVarLevels ``Mutatable) αType)
  let inhabitedInst ← synthInstance
    (mkApp (← mkConstWithFreshMVarLevels ``Inhabited) αType)
  let toStringInst  ← synthInstance
    (mkApp (← mkConstWithFreshMVarLevels ``ToString) αType)
  -- genFresh : Gen α  (= SampleableExt.interpSample α)
  -- mkAppOptM lets the AppBuilder unify the universe level from αType : Type 0.
  let genFreshExpr ← mkAppOptM ``SampleableExt.interpSample #[some αType, some sampleableInst]
  -- mutate : α → Gen α
  let mutateExpr ← mkAppOptM ``Mutatable.mutate #[some αType, some mutableInst]
  -- testOne : α → IO IterResult
  -- For each (x : α), normalise `body x` and build a Testable check action.
  let innerCfgExpr := toExpr plausibleCfg
  let szExpr       := mkNatLit plausibleCfg.maxSize
  let testOneExpr ← withLocalDecl `x BinderInfo.default αType fun xFVar => do
    let bodyX := body.instantiate1 xFVar
    let (bodyXNorm, instXExpr) ← loomMkTestable bodyX
    let runExpr ← mkAppM ``loomMutRunInner #[bodyXNorm, instXExpr, innerCfgExpr, szExpr]
    mkLambdaFVars #[xFVar] runExpr
  -- initialSeeds : Array α
  let seedsExpr ← match seedsTerm with
    | none     => mkAppOptM ``Array.empty #[some αType]
    | some stx =>
        let arrType ← mkAppM ``Array #[αType]
        Lean.Elab.Term.TermElabM.run' <| Lean.Elab.Term.elabTerm stx (some arrType)
  -- Build and execute the mutation loop
  let traceVals ← isTracingEnabledFor `Loom.mut
  let loomMutCfg : LoomMutConfig := { inner := plausibleCfg, traceValues := traceVals }
  let loopExpr ← mkAppOptM ``loomMutLoop #[
    some αType, some inhabitedInst, some toStringInst,
    some genFreshExpr, some mutateExpr,
    some testOneExpr, some seedsExpr,
    some (toExpr loomMutCfg)
  ]
  if !plausibleCfg.quiet then
    Lean.logInfo s!"plausible'_mut: running {plausibleCfg.numInst} iterations \
      (mutProb {loomMutCfg.mutProb}/{loomMutCfg.mutOutOf}, \
      corpus cap {loomMutCfg.maxCorpusSize}) …"
  let ioLogType ← mkAppM ``IO #[← mkAppM ``Array #[mkConst ``String]]
  let code ← unsafe evalExpr (IO (Array String)) ioLogType loopExpr
  let traceMsgs ← liftM code
  if traceVals && !traceMsgs.isEmpty then
    let combined := traceMsgs.foldl (fun acc s => acc ++ "\n" ++ s) "plausible'_mut trace:"
    Lean.logInfo combined
  if !plausibleCfg.quiet then
    Lean.logInfo "plausible'_mut: unable to find a counter-example"
  admitGoal g

end MutationTestingTactic

end Loom.Testing
