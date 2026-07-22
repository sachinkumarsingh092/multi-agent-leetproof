import Lean

open Lean Elab Command Meta

namespace Extensions

abbrev Names := Array Name

initialize disallowedSymbols : SimpleScopedEnvExtension Name Names ←
  registerSimpleScopedEnvExtension {
    initial := #[]
    addEntry := fun s a => s.push a
  }

private def getDisallowedSymbols [Monad m] [MonadEnv m] : m Names :=
  return disallowedSymbols.getState (← getEnv)

private def modifyDisallowedSymbols [Monad m] [MonadEnv m] (f : Names → Names) : m Unit :=
  Lean.modifyEnv (disallowedSymbols.modifyState · f)

syntax (name := disallowedSymbol) "disallowedSymbol" : attr

initialize registerBuiltinAttribute {
  name := `disallowedSymbol
  descr := "Marks a declaration as disallowed in checked declarations"
  add := fun declName _ _ => do
    modifyDisallowedSymbols (·.push declName)
}

private def resolveIdentOrKeep (id : Ident) : CommandElabM Name := do
  try
    resolveGlobalConstNoOverloadCore id.getId
  catch _ =>
    pure id.getId

private def resolveIdentOrThrow (id : Ident) : CommandElabM Name := do
  try
    resolveGlobalConstNoOverloadCore id.getId
  catch _ =>
    throwErrorAt id "Could not resolve `{id.getId}`"

private def resolveManyOrThrow (ids : Array Ident) : CommandElabM (Array Name) :=
  ids.mapM resolveIdentOrThrow

elab "register_disallowed_symbol " id:ident : command => do
  let nm ← resolveIdentOrKeep id
  modifyDisallowedSymbols (·.push nm)

elab "#print_disallowed_symbols" : command => do
  logInfo m!"Disallowed symbols: {← getDisallowedSymbols}"

/-- Names of wrappers whose arguments are ignored while scanning.
    Used only by the Velvet-method checker. -/
private def gadgetWrapperNames : Array Name := #[
  `invariantGadget,
  `onDoneGadget,
  `assertGadget,
  `decreasingGadget
]

private def isIgnoredWrapperApp (ignoredWrappers : NameSet) (e : Expr) : Bool :=
  match e.getAppFn with
  | .const n _ => ignoredWrappers.contains n
  | _ => false

private partial def findForbiddenConsts
  (e : Expr)
  (forbidden : NameSet)
  (ignored : NameSet)
  (ignoredWrappers : NameSet)
  (acc : NameSet := {}) : NameSet :=
  if isIgnoredWrapperApp ignoredWrappers e then
    acc
  else
    match e with
    | .const n _ =>
      if ignored.contains n then acc
      else if forbidden.contains n then acc.insert n
      else acc
    | .app f arg =>
      findForbiddenConsts arg forbidden ignored ignoredWrappers
        (findForbiddenConsts f forbidden ignored ignoredWrappers acc)
    | .lam _ ty body _ =>
      findForbiddenConsts body forbidden ignored ignoredWrappers
        (findForbiddenConsts ty forbidden ignored ignoredWrappers acc)
    | .forallE _ ty body _ =>
      findForbiddenConsts body forbidden ignored ignoredWrappers
        (findForbiddenConsts ty forbidden ignored ignoredWrappers acc)
    | .letE _ ty val body _ =>
      findForbiddenConsts body forbidden ignored ignoredWrappers
        (findForbiddenConsts val forbidden ignored ignoredWrappers
          (findForbiddenConsts ty forbidden ignored ignoredWrappers acc))
    | .mdata _ e' => findForbiddenConsts e' forbidden ignored ignoredWrappers acc
    | .proj _ _ e' => findForbiddenConsts e' forbidden ignored ignoredWrappers acc
    | _ => acc

private partial def forallCodomain (e : Expr) : Expr :=
  match e.consumeMData with
  | .forallE _ _ body _ => forallCodomain body
  | e' => e'

private def isVelvetMethodConst (ci : ConstantInfo) : Bool :=
  let codom := forallCodomain ci.type
  match codom.getAppFn.consumeMData with
  | .const n _ => n == `VelvetM || n.toString.endsWith "VelvetM"
  | _ => false

private def ensureNoDisallowedSymbols
  (declName : Name)
  (symbols : Array Name)
  (ignored : Array Name)
  (requireVelvetMethod : Bool) : CommandElabM Unit := do
  let env ← getEnv
  let some ci := env.find? declName
    | throwError "Unknown declaration `{declName}`"

  if requireVelvetMethod && !isVelvetMethodConst ci then
    throwError "Declaration `{declName}` is not a Velvet method"

  let some body := ci.value?
    | throwError "Declaration `{declName}` has no body"

  let forbiddenSet := symbols.foldl (fun s n => s.insert n) ({} : NameSet)
  let ignoredSet := ignored.foldl (fun s n => s.insert n) ({} : NameSet)
  let ignoredWrapperSet :=
    if requireVelvetMethod
    then gadgetWrapperNames.foldl (fun s n => s.insert n) ({} : NameSet)
    else ({} : NameSet)

  let found := findForbiddenConsts body forbiddenSet ignoredSet ignoredWrapperSet
  unless found.isEmpty do
    let names := found.toList.map (·.toString)
    throwError "Disallowed symbols used in `{declName}`: {", ".intercalate names}"

private def runDisallowedCheck
  (decl : Ident)
  (symbols? : Option (Array Ident))
  (ignores? : Option (Array Ident))
  (requireVelvetMethod : Bool) : CommandElabM Unit := do
  let declName ← resolveIdentOrThrow decl
  let symbols ← match symbols? with
    | some ids => resolveManyOrThrow ids
    | none => getDisallowedSymbols
  let localIgnores ← match ignores? with
    | some ids => resolveManyOrThrow ids
    | none => pure #[]
  ensureNoDisallowedSymbols declName symbols localIgnores requireVelvetMethod

syntax "#ensure_no_disallowed_symbols " ident : command
syntax "#ensure_no_disallowed_symbols " ident " using " "[" ident,* "]" : command
syntax "#ensure_no_disallowed_symbols " ident " ignoring " "[" ident,* "]" : command
syntax "#ensure_no_disallowed_symbols " ident " using " "[" ident,* "]" " ignoring " "[" ident,* "]" : command

syntax "#ensure_no_disallowed_symbols_in_method " ident : command
syntax "#ensure_no_disallowed_symbols_in_method " ident " using " "[" ident,* "]" : command
syntax "#ensure_no_disallowed_symbols_in_method " ident " ignoring " "[" ident,* "]" : command
syntax "#ensure_no_disallowed_symbols_in_method " ident " using " "[" ident,* "]" " ignoring " "[" ident,* "]" : command

elab_rules : command
  | `(command| #ensure_no_disallowed_symbols $decl:ident) =>
    runDisallowedCheck decl none none false
  | `(command| #ensure_no_disallowed_symbols $decl:ident using [$ids:ident,*]) =>
    runDisallowedCheck decl (some ids.getElems) none false
  | `(command| #ensure_no_disallowed_symbols $decl:ident ignoring [$ign:ident,*]) =>
    runDisallowedCheck decl none (some ign.getElems) false
  | `(command| #ensure_no_disallowed_symbols $decl:ident using [$ids:ident,*] ignoring [$ign:ident,*]) =>
    runDisallowedCheck decl (some ids.getElems) (some ign.getElems) false

  | `(command| #ensure_no_disallowed_symbols_in_method $decl:ident) =>
    runDisallowedCheck decl none none true
  | `(command| #ensure_no_disallowed_symbols_in_method $decl:ident using [$ids:ident,*]) =>
    runDisallowedCheck decl (some ids.getElems) none true
  | `(command| #ensure_no_disallowed_symbols_in_method $decl:ident ignoring [$ign:ident,*]) =>
    runDisallowedCheck decl none (some ign.getElems) true
  | `(command| #ensure_no_disallowed_symbols_in_method $decl:ident using [$ids:ident,*] ignoring [$ign:ident,*]) =>
    runDisallowedCheck decl (some ids.getElems) (some ign.getElems) true

end Extensions
