import Lean
import Lean.Parser.Command

import Velvet.Std
import Extensions.Attributes

import Loom.MonadAlgebras.WP.Gen

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

open Lean Elab Command Parser Meta


-- `spec` is like `def` but automatically adds `@[loomAbstractionSimp, specHelper, grind]` attribute
elab "spec " name:declId sig:optDeclSig val:declVal : command => do
  let valRaw := val.raw
  if valRaw.isOfKind ``Command.declValSimple then
    let stx ← `(command|
      @[loomAbstractionSimp, specHelper, grind]
      def $name $sig $val:declVal
    )
    elabCommand stx
  else
    throwErrorAt val "Unsupported syntax, only allowed syntax is with ':=' "

elab "#printSpecHelpers" : command => do
  let st := specHelpers.getState (← getEnv)
  logInfo m!"Spec Helpers: {st}"
