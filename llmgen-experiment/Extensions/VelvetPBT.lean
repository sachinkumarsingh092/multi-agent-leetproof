import Velvet.Std
import CaseStudies.TestingUtil
import Extensions.SpecDSL
import Extensions.Testing

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Extract elements from the Expr representation of a List α
open Lean in
partial def listExprElems (e : Expr) : Array Expr :=
  match e.getAppFn, e.getAppArgs with
  | .const `List.cons _, #[_, hd, tl] => #[hd] ++ listExprElems tl
  | _, _                               => #[]

-- Strip the WithName p name wrapper, returning the underlying proposition
open Lean in
def unwrapWithName (e : Expr) : Expr :=
  if e.isAppOfArity `WithName 2 then e.getAppArgs[0]! else e

-- Recursively split a Prop expression along And (∧) applications into a flat list.
-- WithName wrappers are stripped first. If the expression is not syntactically an And,
-- whnf reduction is attempted to handle definitions that unfold to conjunctions
-- (e.g. `def post x y := P1 x y ∧ P2 x y`). A non-And expression returns a singleton.
open Lean Meta Elab Term in
private partial def splitAndConjuncts (e : Expr) : TermElabM (List Expr) := do
  let e' := unwrapWithName e
  if e'.isAppOfArity ``And 2 then
    let args := e'.getAppArgs
    return (← splitAndConjuncts args[0]!) ++ (← splitAndConjuncts args[1]!)
  else
    let e'' ← whnf e'
    if e''.isAppOfArity ``And 2 then
      let args := e''.getAppArgs
      return (← splitAndConjuncts args[0]!) ++ (← splitAndConjuncts args[1]!)
    else
      return [e']

-- VelvetTestM adds a StdGen state layer on top of VelvetM, so that
-- runtime plausible tests can consume randomness from the StateT state.
-- MonadLift VelvetM VelvetTestM is provided automatically by StateT.
abbrev VelvetTestM α := ExceptT String (StateT StdGen VelvetM) α

-- Runtime helper: check a single proposition using its Testable instance.
-- Reads StdGen from the StateT state, runs the Plausible test suite, updates
-- the state with the new generator, and diverges (via DivM.div) on failure.
--
-- Gen α = RandT (ReaderT (ULift Nat) (Except GenError)) α
--       = StateT (ULift StdGen) (ReaderT (ULift Nat) (Except GenError)) α
-- We use `StateT.run` explicitly because `Gen.run` is a different function
-- (it takes `Nat` and returns `IO α`).
private def velvetCheckProp
    (p : Prop) (inst : Plausible.Testable p) (size : Nat) (errorMsg : String)
    : VelvetTestM PUnit := do
  let s ← get
  -- StateT.run : Gen (TestResult p) → ULift StdGen
  --           → ReaderT (ULift Nat) (Except GenError) (TestResult p × ULift StdGen)
  -- ReaderT.run : ... → ULift Nat → Except GenError (TestResult p × ULift StdGen)
  match (StateT.run (inst.run {} false) (ULift.up s)).run ⟨size⟩ with
  | .ok (r, ⟨s'⟩) =>
    set s'
    match r with
    | .success _ | .gaveUp _ => pure ()
    | .failure _ _ _ =>
        throw errorMsg
  | .error _ => pure ()

-- Runtime check for a decidable proposition: fails immediately if ¬p.
-- Unlike velvetCheckProp, no random testing is done—the result is exact.
private def velvetDecideCheck (p : Prop) [Decidable p] (errorMsg : String) : VelvetTestM PUnit :=
  if decide p then pure () else throw errorMsg

-- No-op check: used as a fallback when neither Decidable nor Testable can be synthesized.
private def velvetSkipCheck : VelvetTestM PUnit := pure ()

-- Postcondition check wrappers returning Gen Bool (true = pass).
-- velvetPostDecidable uses `decide` for an exact check.
-- velvetPostTestable runs Plausible random testing and maps to Bool.
private def velvetPostDecidable (p : Prop) [Decidable p] : Plausible.Gen Bool :=
  pure (decide p)

private def velvetPostTestable (p : Prop) [Plausible.Testable p] : Plausible.Gen Bool :=
  Functor.map (fun r => !r.isFailure) (Plausible.Testable.runSuite p)

-- Run a Gen α with a specific seed and size, without touching stdGenRef.
-- Mirrors how Gen.run works but uses runRandWith instead of runRand.
private def runGenWith (seed : Nat) (x : Plausible.Gen α) (size : Nat) : IO α :=
  letI : MonadLift (ReaderT (ULift Nat) (Except Plausible.GenError)) IO :=
    ⟨fun m => match ReaderT.run m ⟨size⟩ with
              | .ok a  => pure a
              | .error e => throw (Plausible.Gen.genFailure e)⟩
  Plausible.runRandWith seed x

-- Runtime check for the decreasing (termination) measure.
-- Returns the new prevMeas, or diverges (DivM.div) if measure did not strictly decrease.
--   (none,   _)      → pure prev        no measure annotation, skip
--   (some c, none)   → pure (some c)    first iteration: record
--   (some c, some p) → c < p: pure (some c); else: diverge
private def velvetCheckDecreasingM
    (curr prev : Option Nat) (errorMsg : String) : VelvetTestM (Option Nat) := do
  match curr, prev with
  | none,   _       => pure prev
  | some c, none    => pure (some c)
  | some c, some p  =>
    if c < p then pure (some c)
    else do
      throw errorMsg

-- Wrap a ForInStep to carry Option Nat (the measure) alongside the accumulator.
-- Used to thread prevMeas through loop iterations without changing VelvetTestM.
--   yield: carry yieldMeas (the new measure from this iteration's check)
--   done:  carry doneMeas  (typically prevMeas — loop exited, no new check)
private def velvetWrapForInStep {β : Type u}
    (step : ForInStep β)
    (yieldMeas doneMeas : Option Nat) : ForInStep (β × Option Nat) :=
  match step with
  | .yield v => .yield (v, yieldMeas)
  | .done  v => .done  (v, doneMeas)

-- Lift a VelvetM α program to VelvetTestM α using monadLift.
-- The program may be a multi-argument function (fun x y => ... : VelvetM α),
-- so we recurse through the outer lambdas and apply monadLift to the body.
open Lean Meta Elab in
private partial def liftVelvetMBody (e : Expr) : TermElabM Expr := do
  match e with
  | .lam n t b bi =>
    withLocalDecl n bi t fun fv => do
      mkLambdaFVars #[fv] (← liftVelvetMBody (b.instantiate1 fv))
  | body =>
    mkAppOptM ``MonadLiftT.monadLift
      #[none, some (mkConst ``VelvetTestM), none, none, some body]

-- Check if an expression contains a decreasingGadget application.
-- Used to decide whether to extend the ForIn accumulator with Option Nat.
open Lean in
private partial def containsDecreasingGadget : Expr → Bool
  | e@(.app f a) =>
    e.isAppOf `decreasingGadget || containsDecreasingGadget f || containsDecreasingGadget a
  | .lam _ _ b _    => containsDecreasingGadget b
  | .letE _ _ v b _ => containsDecreasingGadget v || containsDecreasingGadget b
  | .mdata _ e      => containsDecreasingGadget e
  | _               => false

-- Extract the measure argument from the first decreasingGadget in a bind chain.
-- bind (decreasingGadget meas) cont → some meas; otherwise none.
open Lean in
private def findDecreasingMeas (e : Expr) : Option Expr :=
  let e' := e.consumeMData
  let fn   := e'.getAppFn
  let args := e'.getAppArgs
  if fn.isConstOf ``Bind.bind && args.size >= 6 then
    let action := args[4]!
    if action.isAppOf `decreasingGadget then some action.appArg!
    else none
  else none

-- Traverse a VelvetTestM expression (produced by liftVelvetMBody) and
-- replace each `monadLift (... gadget ...)` pattern with the appropriate
-- VelvetTestM action.
--
-- The key structural cases:
--   monadLift body       → recurse into body (a VelvetM expr)
--   fun / let            → recurse through binders
--   bind gadget cont     → replace gadget, recurse into cont
--   bind action cont     → rebuild as VelvetTestM bind (recurse both)
--   anything else        → monadLift it (leaf VelvetM expr)
-- Run a TacticM action from TermElabM by supplying a fresh context/state.
-- loomMkTestable manages its own synthetic goal internally, so empty goals is fine.
open Lean Elab Tactic in
private def runAsTacticM {α} (x : TacticM α) : TermElabM α := do
  let ctx : Context := { elaborator := .anonymous }
  let st  : State  := { goals := [] }
  let (result, _) ← x.run ctx |>.run st
  return result

open Lean Meta Elab Term in
private partial def replaceGadgetsInLifted (e : Expr) : TermElabM Expr := do
  -- If e is monadLift applied to a VelvetM body, go inside
  if e.isAppOf ``MonadLiftT.monadLift then
    let args := e.getAppArgs
    -- monadLift has 5 args: m n inst α body; body is last
    if args.size >= 5 then
      return ← distributeMonadLift args[4]!
    else
      return e
  -- Otherwise recurse structurally
  else match e with
  | .lam n t b bi =>
    withLocalDecl n bi t fun fv => do
      mkLambdaFVars #[fv] (← replaceGadgetsInLifted (b.instantiate1 fv))
  | .letE n t v b _ =>
    withLetDecl n t v fun fv => do
      mkLetFVars #[fv] (← replaceGadgetsInLifted (b.instantiate1 fv))
  | .mdata md inner => return .mdata md (← replaceGadgetsInLifted inner)
  | .app f a =>
    return .app (← replaceGadgetsInLifted f) (← replaceGadgetsInLifted a)
  | other => return other

-- Distribute monadLift through a VelvetM expression, replacing gadgets.
-- Returns a VelvetTestM expression.
where distributeMonadLift (e : Expr) (prevMeasCtx : Option Expr := none) : TermElabM Expr := do
  match e with
  -- Binders: recurse into body, propagating prevMeasCtx so it reaches decreasingGadget
  | .lam n t b bi =>
    withLocalDecl n bi t fun fv => do
      mkLambdaFVars #[fv] (← distributeMonadLift (b.instantiate1 fv) prevMeasCtx)
  | .letE n t v b _ =>
    withLetDecl n t v fun fv => do
      mkLetFVars #[fv] (← distributeMonadLift (b.instantiate1 fv) prevMeasCtx)
  | .mdata md inner => return .mdata md (← distributeMonadLift inner prevMeasCtx)
  | _ =>
    let fn   := e.getAppFn
    let args := e.getAppArgs
    -- Bind: check if action is a gadget
    if fn.isConstOf ``Bind.bind && args.size >= 6 then
      let action := args[4]!
      let cont   := args[5]!
      if action.isAppOf `invariantGadget then
        -- Extract individual propositions from the invariant list (keep raw for name extraction)
        let rawElems := listExprElems action.appArg!
        let cont' ← distributeMonadLift cont prevMeasCtx
        let punitTy   := Lean.mkConst ``PUnit [.succ .zero]
        let punitUnit := Lean.mkConst ``PUnit.unit [.succ .zero]
        -- Build check chain right-to-left.
        -- Accumulator type: PUnit → VelvetTestM outerAlpha  (same shape as cont').
        -- Starting value: cont' itself.
        -- Each step wraps the current acc with one more check.
        let chain ← rawElems.foldrM (fun raw acc => do
          let p := unwrapWithName raw
          -- Extract name string from WithName wrapper if present.
          -- WithName args: [0]=prop [1]=Lean.Name; Lean.Name.str args: [0]=parent [1]=StrLit
          -- whnf reduces Name.mkStr to Name.str (mkStr is a def, not a ctor)
          let invName : String ← do
            if raw.isAppOfArity `WithName 2 then
              let nameExpr ← whnf (raw.getAppArgs[1]!)
              let nfn   := nameExpr.getAppFn
              let nargs := nameExpr.getAppArgs
              if nfn.isConstOf ``Lean.Name.str && nargs.size == 2 then
                match nargs[1]! with
                | .lit (.strVal s) => pure s
                | _ => pure ""
              else pure ""
            else pure ""
          -- Format: "invariant_test" → invariant "test" doesn't hold
          --         "invariant_1"    → invariant "1" doesn't hold
          --         ""               → invariant doesn't hold
          let errMsg : String :=
            match invName.splitOn "_" with
            | pfx :: rest@(_ :: _) =>
              s!"{pfx} \"{"_".intercalate rest}\" doesn't hold"
            | _ => "invariant doesn't hold"
          -- Try decidable first (exact), fall back to testable (random). Skip on both failure.
          let check? ← runAsTacticM do
            match ← Loom.Testing.tryLoomMkDecidable p with
            | some decInst =>
              let e ← mkAppOptM ``velvetDecideCheck #[some p, some decInst, some (toExpr errMsg)]
              pure (some e)
            | none =>
              match ← Loom.Testing.tryLoomMkTestable p with
              | some (p', inst) =>
                let e ← mkAppOptM ``velvetCheckProp
                  #[some p', some inst, some (toExpr (100 : Nat)), some (toExpr errMsg)]
                pure (some e)
              | none => pure none
          match check? with
          | some check =>
            let bound ← mkAppM ``Bind.bind #[check, acc]
            return Lean.mkLambda `_ .default punitTy bound
          | none =>
            logWarning m!"velvet_plausible_test: skipping invariant check — could not synthesize Decidable or Testable for:\n  {p}"
            return acc  -- synthesis failed: skip this invariant
        ) cont'
        -- Apply chain to PUnit.unit and beta-reduce to get VelvetTestM outerAlpha
        return Lean.Expr.headBeta (mkApp chain punitUnit)
      else if action.isAppOf `onDoneGadget then
        -- onDoneGadget carries the loop-exit condition (e.g. ¬(x' > 0)).
        -- It appears just before `ite cond yield done`.
        -- We strip the gadget but inject a runtime check into the done branch.
        let rawDone := action.appArg!
        let prop := unwrapWithName rawDone
        let contBody := Expr.headBeta (.app cont (.const `PUnit.unit [.succ .zero]))
        -- Process cont() with none: strips decreasingGadget, exposes the ite
        -- so that the done check can be injected into the done branch correctly.
        let body ← distributeMonadLift contBody
        -- Extract done name from WithName wrapper (same logic as invariants)
        let doneErrMsg : String ← do
          if rawDone.isAppOfArity `WithName 2 then
            let nameExpr ← whnf (rawDone.getAppArgs[1]!)
            let nfn   := nameExpr.getAppFn
            let nargs := nameExpr.getAppArgs
            if nfn.isConstOf ``Lean.Name.str && nargs.size == 2 then
              match nargs[1]! with
              | .lit (.strVal s) =>
                let errMsg : String :=
                  match s.splitOn "_" with
                  | pfx :: rest@(_ :: _) =>
                    s!"{pfx} \"{"_".intercalate rest}\" doesn't hold"
                  | _ => s!"'{s}' doesn't hold"
                pure errMsg
              | _ => pure "exit condition doesn't hold"
            else pure "exit condition doesn't hold"
          else pure "exit condition doesn't hold"
        -- Try decidable first (exact), fall back to testable (random).
        let check? ← runAsTacticM do
          match ← Loom.Testing.tryLoomMkDecidable prop with
          | some decInst =>
            let e ← mkAppOptM ``velvetDecideCheck #[some prop, some decInst, some (toExpr doneErrMsg)]
            pure (some e)
          | none =>
            match ← Loom.Testing.tryLoomMkTestable prop with
            | some (p', inst) =>
              let e ← mkAppOptM ``velvetCheckProp
                #[some p', some inst, some (toExpr (100 : Nat)), some (toExpr doneErrMsg)]
              pure (some e)
            | none => pure none
        if check?.isNone then
          logWarning m!"velvet_plausible_test: skipping done-condition check — could not synthesize Decidable or Testable for:\n  {prop}"
        let bodyWithCheck ←
          match check? with
          | some check =>
            -- If the body is an ite (yield vs done), inject check into the done branch
            let bodyCore := body.consumeMData
            let bodyFn   := bodyCore.getAppFn
            let bodyArgs := bodyCore.getAppArgs
            if bodyFn.isConstOf ``ite && bodyArgs.size >= 5 then
              let doneBranch := bodyArgs[4]!
              let punitTy   := Lean.mkConst ``PUnit [.succ .zero]
              let discardLam := Lean.mkLambda `_ .default punitTy doneBranch
              let newDone ← mkAppM ``Bind.bind #[check, discardLam]
              pure (mkAppN bodyFn (bodyArgs.set! 4 newDone))
            else
              -- Fallback: prepend the check before the whole body
              let punitTy   := Lean.mkConst ``PUnit [.succ .zero]
              let discardLam := Lean.mkLambda `_ .default punitTy body
              mkAppM ``Bind.bind #[check, discardLam]
          | none => pure body  -- synthesis failed: silently strip the gadget
        -- If prevMeasCtx is set and there's a decreasingGadget in cont, wrap bodyWithCheck
        -- with the measure check so it runs each loop iteration.
        match prevMeasCtx, findDecreasingMeas contBody with
        | some prevMeasExpr, some meas =>
          -- Use Functor.map to avoid Pure.pure whose monad can't be inferred without ctx.
          let optNatTy ← mkAppM ``Option #[mkConst ``Nat]
          let bodyTy ← inferType bodyWithCheck
          let forInStepβTy := bodyTy.appArg!
          withLocalDecl `newMeas .default optNatTy fun newMeasFV => do
            withLocalDecl `step .default forInStepβTy fun stepFV => do
              let wrapApp ← mkAppM ``velvetWrapForInStep #[stepFV, newMeasFV, newMeasFV]
              let wrapFn  ← mkLambdaFVars #[stepFV] wrapApp
              let mapped  ← mkAppM ``Functor.map #[wrapFn, bodyWithCheck]
              let newMeasLam ← mkLambdaFVars #[newMeasFV] mapped
              let checkExpr  ← mkAppM ``velvetCheckDecreasingM #[meas, prevMeasExpr, toExpr "Decreasing check failed"]
              mkAppM ``Bind.bind #[checkExpr, newMeasLam]
        | _, _ => return bodyWithCheck
      else if action.isAppOf `decreasingGadget then
        let punit := Expr.const `PUnit.unit [.succ .zero]
        match prevMeasCtx with
        | none =>
          -- Not inside an extended loop body; strip as before.
          distributeMonadLift (Expr.headBeta (.app cont punit))
        | some prevMeasExpr =>
          -- Inside an extended loop body: check the measure and wrap ForInStep results.
          -- meas : Option Nat (the current iteration's decreasing measure)
          let meas := action.appArg!
          -- Process cont() with no prevMeasCtx: produces VelvetTestM (ForInStep β)
          let processedCont ← distributeMonadLift (Expr.headBeta (.app cont punit))
          let contTy ← inferType processedCont
          let forInStepβTy := contTy.appArg!      -- ForInStep β
          let optNatTy ← mkAppM ``Option #[mkConst ``Nat]
          -- Build:
          --   bind (velvetCheckDecreasingM meas prevMeas) fun newMeas =>
          --     bind processedCont fun step =>
          --       pure (velvetWrapForInStep step newMeas prevMeas)
          withLocalDecl `newMeas .default optNatTy fun newMeasFV => do
            let stepLam ←
              withLocalDecl `step .default forInStepβTy fun stepFV => do
                let wrapApp ← mkAppM ``velvetWrapForInStep
                                #[stepFV, newMeasFV, prevMeasExpr]
                let pureWrap ← mkAppM ``Pure.pure #[wrapApp]
                mkLambdaFVars #[stepFV] pureWrap   -- fun step => pure (wrap step)
            let bindStep   ← mkAppM ``Bind.bind #[processedCont, stepLam]
            let newMeasLam ← mkLambdaFVars #[newMeasFV] bindStep
            let checkExpr  ← mkAppM ``velvetCheckDecreasingM #[meas, prevMeasExpr, toExpr "Decreasing check failed"]
            mkAppM ``Bind.bind #[checkExpr, newMeasLam]
      else
        let action' ← distributeMonadLift action
        let cont'   ← distributeMonadLift cont prevMeasCtx
        mkAppM ``Bind.bind #[action', cont']
    -- ForIn: recurse into the loop body lambda, rebuild in VelvetTestM
    -- @ForIn.forIn args: [m, ρ, α, β, ForIn inst, Monad inst, container, init, body] (9 total)
    else if fn.isConstOf ``ForIn.forIn && args.size >= 9 then
      let container := args[6]!
      let initState := args[7]!
      let loopBody  := args[8]!
      -- If the loop body contains a decreasingGadget, extend the accumulator
      -- from β to β × Option Nat so prevMeas threads through loop iterations.
      if !containsDecreasingGadget loopBody then
        let loopBody' ← distributeMonadLift loopBody
        mkAppM ``ForIn.forIn #[container, initState, loopBody']
      else
        match loopBody with
        | .lam n1 t1 body1 bi1 =>
          withLocalDecl n1 bi1 t1 fun elemFV => do
            let inner := body1.instantiate1 elemFV
            match inner with
            | .lam _ t2 body2 bi2 => do
              -- t2 is β (original accumulator type). Extend to β × Option Nat.
              let β        := t2
              let optNatTy ← mkAppM ``Option #[mkConst ``Nat]
              let pairTy   ← mkAppM ``Prod #[β, optNatTy]
              let noneVal  ← mkAppOptM ``Option.none #[some (mkConst ``Nat)]
              withLocalDecl `accPair bi2 pairTy fun accPairFV => do
                -- Destructure: acc = accPair.1, prevMeas = accPair.2
                let accValExpr   ← mkAppM ``Prod.fst #[accPairFV]
                let prevMeasExpr ← mkAppM ``Prod.snd #[accPairFV]
                -- Substitute acc with accPair.1, then process with prevMeas as prevMeasCtx
                let body2'     := body2.instantiate1 accValExpr
                let resultBody ← distributeMonadLift body2' (some prevMeasExpr)
                let innerLam   ← mkLambdaFVars #[accPairFV] resultBody
                let loopBody'  ← mkLambdaFVars #[elemFV] innerLam
                -- Initial state: (initState, none)
                let initState' ← mkAppM ``Prod.mk #[initState, noneVal]
                let forInResult ← mkAppM ``ForIn.forIn #[container, initState', loopBody']
                -- Extract original accumulator via Functor.map Prod.fst
                -- (avoids Pure.pure whose monad can't be inferred without context)
                let pairTy' ← inferType initState'
                withLocalDecl `p .default pairTy' fun pFV => do
                  let fstApp ← mkAppM ``Prod.fst #[pFV]
                  let fstFn  ← mkLambdaFVars #[pFV] fstApp
                  mkAppM ``Functor.map #[fstFn, forInResult]
            | _ => do
              let loopBody' ← distributeMonadLift loopBody
              mkAppM ``ForIn.forIn #[container, initState, loopBody']
        | _ =>
          let loopBody' ← distributeMonadLift loopBody
          mkAppM ``ForIn.forIn #[container, initState, loopBody']
    -- Ite: recurse into both branches, rebuild
    -- @ite args: [α, c, Decidable, then, else]
    else if fn.isConstOf ``ite && args.size >= 5 then
      let cond       := args[1]!
      let decInst    := args[2]!
      let thenBranch := args[3]!
      let elseBranch := args[4]!
      let thenBranch' ← distributeMonadLift thenBranch prevMeasCtx
      let elseBranch' ← distributeMonadLift elseBranch prevMeasCtx
      mkAppOptM ``ite #[none, some cond, some decInst, some thenBranch', some elseBranch']
    -- Leaf VelvetM expression: wrap with monadLift
    else
      mkAppOptM ``MonadLiftT.monadLift
        #[none, some (mkConst ``VelvetTestM), none, none, some e]

open Lean Meta Elab in
elab "#lift_to_velvet_test" n:ident : command => do
  let name ← Elab.Command.liftCoreM (Lean.resolveGlobalConstNoOverload n)
  let info ← Elab.Command.liftCoreM (Lean.getConstInfo name)
  let some val := info.value? | throwError "'{name}' has no definition body"
  let lifted  ← Elab.Command.liftTermElabM (liftVelvetMBody val)
  let result  ← Elab.Command.liftTermElabM (replaceGadgetsInLifted lifted)
  Lean.logInfo m!"{result}"

-- Extract the binder type from a bracketedBinder TSyntax.
-- Handles explicit binders of the form (id : tp).
open Lean in
private def binderType? (b : TSyntax `Lean.Parser.Term.bracketedBinder) : Option (TSyntax `term) :=
  match b with
  | `(bracketedBinder| ($_ : $tp:term)) => some tp
  | `(bracketedBinder| {$_ : $tp:term}) => some tp
  | `(bracketedBinder| [$_ : $tp:term]) => some tp
  | _ => none

-- Build and register the <name>VelvetTest definition:
-- lifts the VelvetM program into VelvetTestM with inline Testable checks.
open Lean Meta Elab in
private def mkVelvetTestDef (name : Name) : TermElabM Name := do
  let vtestName := name.appendAfter "VelvetTest"
  let info ← getConstInfo name
  let some origVal := info.value? | throwError "'{name}' has no definition body"
  let lifted   ← liftVelvetMBody origVal
  let vtestExpr ← replaceGadgetsInLifted lifted
  -- Resolve pending metavariables from instance synthesis
  let vtestExpr ← instantiateMVars vtestExpr
  let vtestType ← instantiateMVars (← inferType vtestExpr)
  let decl := Declaration.defnDecl {
    name        := vtestName
    levelParams := info.levelParams
    type        := vtestType
    value       := vtestExpr
    hints       := .regular (Lean.getMaxHeight (← getEnv) vtestExpr + 1)
    safety      := .safe
  }
  addAndCompile decl
  return vtestName

/-- Configuration for `velvet_plausible_test`. -/
structure VelvetTestConfig where
  /-- Maximum number of tests to run. Used when `maxMs` is `none`. -/
  maxTests : Nat := 100
  /-- Time limit in milliseconds. If set, tests run until this many ms have elapsed
  (ignoring `maxTests`). -/
  maxMs : Option Nat := none
  /-- Size parameter passed to the random generator, controls the magnitude of
  generated values (analogous to Plausible's `size`). -/
  size : Nat := 30
  deriving Inhabited

syntax "velvet_plausible_test" ident : command
syntax "velvet_plausible_test" ident "(" "config" ":=" term ")" : command

open Lean Meta Elab Command in
private def runVelvetPlausibleTest
    (nameRaw : TSyntax `ident) (cfg : VelvetTestConfig) : CommandElabM Unit := do
  let (ctx, name) ← obtainVelvetTestingCtx nameRaw

  -- Step 1: Build and register the VelvetTestM program
  let vtestName ← Command.liftTermElabM (mkVelvetTestDef name)

  -- Step 2: Synthesize Decidable for the precondition
  elabDefiningDecidableInstancesForVelvetSpec nameRaw true none none

  -- Step 3: Extract parameter types from binderIdents for interpSample calls
  let paramTypes : Array (TSyntax `term) ← ctx.binderIdents.mapM fun b =>
    match binderType? b with
    | some tp => pure tp
    | none    => throwError "unexpected binder form: {b}"

  -- Step 3.5: Synthesize Testable for each postcondition conjunct independently.
  -- Elaborate ctx.post, split into individual conjuncts by decomposing ∧, and
  -- synthesize Decidable/Testable for each one separately. The final check
  -- function sequences all per-conjunct checks so a failing conjunct is reported
  -- immediately even if other conjuncts could not get an instance synthesized.
  let postCheckName := name.appendAfter "VelvetPostCheck"
  Command.liftTermElabM do
    let paramTypeExprs ← paramTypes.mapM fun tp => Term.elabType tp
    let retTypeExpr ← Term.elabType ctx.retType
    let rec mkWithLocals (i : Nat) (fvs : Array Expr) : TermElabM Expr := do
      if i < paramTypeExprs.size then
        withLocalDecl (ctx.ids[i]!.getId) .default paramTypeExprs[i]! fun fv =>
          mkWithLocals (i + 1) (fvs.push fv)
      else
        withLocalDecl ctx.retId.getId .default retTypeExpr fun retFV => do
          let allFVs := fvs.push retFV
          let postExpr ← Term.elabTerm ctx.post (some (mkSort .zero))
          -- Split the postcondition conjunction into individual conjuncts.
          -- andListWithName builds the conjunction right-to-left (last ensures = outermost
          -- left conjunct), so we reverse to restore write order: ensures clause 1 = (1 of N).
          let conjuncts := (← splitAndConjuncts postExpr).reverse
          let n := conjuncts.length
          let punitTy := Lean.mkConst ``PUnit [.succ .zero]
          -- Build a check expression for each conjunct independently.
          let checks ← ((List.range n).zip conjuncts).mapM fun (i, conjunct) => do
            let conjunctStr : String := toString (← Lean.PrettyPrinter.ppExpr conjunct)
            let errMsg : String :=
              if n = 1 then s!"postcondition doesn't hold\n  {conjunctStr}"
              else s!"postcondition ({i + 1} of {n}) doesn't hold\n  {conjunctStr}"
            match ← runAsTacticM (Loom.Testing.tryLoomMkDecidable conjunct) with
            | some decInst =>
              mkAppOptM ``velvetDecideCheck
                #[some conjunct, some decInst, some (toExpr errMsg)]
            | none =>
              match ← runAsTacticM (Loom.Testing.tryLoomMkTestable conjunct) with
              | some (p', inst) =>
                mkAppOptM ``velvetCheckProp
                  #[some p', some inst, some (toExpr (100 : Nat)), some (toExpr errMsg)]
              | none =>
                logWarning m!"velvet_plausible_test: skipping postcondition conjunct ({i + 1} of {n}) — could not synthesize Decidable or Testable for:\n  {conjunct}"
                mkAppM ``velvetSkipCheck #[]
          -- Sequence all checks: check0 >>= fun _ => check1 >>= fun _ => ...
          let checkExpr ← match checks with
            | [] => mkAppM ``velvetSkipCheck #[]
            | c :: cs =>
              cs.foldlM (fun acc check => do
                let discardLam := Lean.mkLambda `_ .default punitTy check
                mkAppM ``Bind.bind #[acc, discardLam]
              ) c
          mkLambdaFVars allFVs checkExpr
    let checkFnExpr ← mkWithLocals 0 #[]
    let checkFnType ← instantiateMVars (← inferType checkFnExpr)
    let checkFnExpr ← instantiateMVars checkFnExpr
    let decl := Declaration.defnDecl {
      name        := postCheckName
      levelParams := []
      type        := checkFnType
      value       := checkFnExpr
      hints       := .regular (Lean.getMaxHeight (← getEnv) checkFnExpr + 1)
      safety      := .safe
    }
    addAndCompile decl

  -- Step 4: Build precondition check term: @decide _ (namePreDecidable id1 id2 ...)
  let ids := ctx.ids
  let preInstName := name.appendAfter "PreDecidable"
  let preCheckTerm : TSyntax `term ←
    try
      let _ ← resolveGlobalConstNoOverloadCore preInstName
      `(term| @decide _ ($(Syntax.mkApp (mkIdent preInstName) ids)))
    catch _ =>
      `(term| decide ($(ctx.pre)))

  -- Step 5: Build the core Gen Bool body (inputs already bound by the time this runs).
  --   • skip if precondition not satisfied (return true = pass)
  --   • sample a Nat seed for the VelvetTestM StdGen
  --   • run the VelvetTestM program; invariant violations → DivM.div
  --   • on DivM.res, check the postcondition with Testable.runSuite
  -- DivM.res carries (retVal × StdGen); bind ctx.ret and discard the new StdGen.
  let vtestIdent := mkIdent vtestName
  let ret  := ctx.ret
  -- Build the postcondition check call: {name}VelvetPostCheck id0 id1 ... retId
  let postCheckCall := Syntax.mkApp (mkIdent postCheckName) (ids.push ctx.retId)
  -- Build a term that at runtime evaluates to "id0 = <val>, id1 = <val>, ..."
  -- All ids are in scope inside genBodyTerm (bound by the >>= chain in genTerm).
  let inputStrTerm : TSyntax `term ← do
    let pieces ← ids.mapM fun (id : Ident) =>
      let namePart := Syntax.mkStrLit (id.getId.toString ++ " = ")
      `(term| ($namePart ++ toString $id))
    match pieces.toList with
    | [] => `(term| ("" : String))
    | first :: rest =>
      rest.foldlM (fun acc p => `(term| ($acc ++ (", " : String) ++ $p))) first

  -- genBodyTerm returns Gen (Option String):
  --   none         = pass
  --   some errMsg  = fail with reason (includes input values)
  let genBodyTerm ← `(term| do
      unless $preCheckTerm do return (none : Option String)
      let velvetInputStr : String := $inputStrTerm
      let velvetSeedN ← Plausible.SampleableExt.interpSample Nat
      let velvetStdGen := mkStdGen velvetSeedN
      match NonDetT.run (($(Syntax.mkApp vtestIdent ids)).run velvetStdGen) with
      | DivM.div => pure (some ("program diverged\n  " ++ velvetInputStr))
      | DivM.res (.error velvetErrMsg, _) => pure (some (velvetErrMsg ++ "\n  " ++ velvetInputStr))
      | DivM.res (.ok $ret, velvetFinalState) =>
          match NonDetT.run (($postCheckCall:term).run velvetFinalState) with
          | DivM.div => pure (some ("postcondition check diverged\n  " ++ velvetInputStr))
          | DivM.res (.error velvetPostMsg, _) => pure (some (velvetPostMsg ++ "\n  " ++ velvetInputStr))
          | DivM.res (.ok _, _) => pure none)

  -- Step 6: Wrap each parameter sample via >>= so we never need doSeqItem splicing.
  --   Result: interpSample T0 >>= fun id0 => interpSample T1 >>= fun id1 => genBodyTerm
  let genTerm ← (ids.zip paramTypes).foldrM (fun (id, tp) acc =>
    `(term| Plausible.SampleableExt.interpSample $tp >>= fun $id => $acc))
    genBodyTerm

  -- Step 7: Build the IO Unit runner and evaluate it with #eval.
  --   If cfg.maxMs is set, loop until the time limit; otherwise run cfg.maxTests iterations.
  let sizeLit := Syntax.mkNatLit cfg.size
  let ioTerm ← match cfg.maxMs with
    | none =>
      let nLit  := Syntax.mkNatLit cfg.maxTests
      let passMsg := Syntax.mkStrLit s!"[velvet_plausible_test] PASS: {cfg.maxTests} tests passed"
      `(term| do
          let mut velvetAllPassed := true
          for i in List.range $nLit do
            let velvetResult ← runGenWith i ($genTerm) $sizeLit
            if let some velvetErrMsg := velvetResult then
              IO.println s!"[velvet_plausible_test] FAIL: {velvetErrMsg}"
              velvetAllPassed := false
              break
          if velvetAllPassed then
            IO.println $passMsg)
    | some ms =>
      let msLit := Syntax.mkNatLit ms
      `(term| do
          let mut velvetAllPassed := true
          let velvetStartMs ← (IO.monoMsNow : IO Nat)
          let mut velvetI := 0
          repeat
            let velvetNowMs ← (IO.monoMsNow : IO Nat)
            if velvetNowMs - velvetStartMs ≥ $msLit then break
            let velvetResult ← runGenWith velvetI ($genTerm) $sizeLit
            velvetI := velvetI + 1
            if let some velvetErrMsg := velvetResult then
              IO.println s!"[velvet_plausible_test] FAIL: {velvetErrMsg}"
              velvetAllPassed := false
              break
          if velvetAllPassed then
            IO.println s!"[velvet_plausible_test] PASS: {velvetI} tests passed")
  let evalCmd ← `(command| #eval $ioTerm)
  elabCommand evalCmd

open Lean Meta Elab Command in
elab_rules : command
  | `(command| velvet_plausible_test $nameRaw:ident) =>
    runVelvetPlausibleTest nameRaw {}
  | `(command| velvet_plausible_test $nameRaw:ident (config := $cfgTerm:term)) => do
    let cfg ← Command.liftTermElabM
      (unsafe Lean.Elab.Term.evalTerm VelvetTestConfig (mkConst ``VelvetTestConfig) cfgTerm)
    runVelvetPlausibleTest nameRaw cfg
