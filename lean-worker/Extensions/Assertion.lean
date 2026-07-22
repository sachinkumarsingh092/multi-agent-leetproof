import Lean

open Lean Elab Command Meta Term in
/-- Run `#eval term` and capture the output message as a string. -/
private def evalAndCapture (t : Syntax) : CommandElabM (String × String) := do
  let termStr := t.reprint.getD "<term>"
  -- Save current messages, run #eval, capture output, restore messages
  let initMsgs ← modifyGet fun st => (st.messages, { st with messages := {} })
  try
    let t' : TSyntax `term := ⟨t⟩
    let evalCmd ← `(command| #eval $t')
    elabCommand evalCmd
    let msgs := (← get).messages
    let output := msgs.toList.filterMap fun msg =>
      if msg.severity == .information then some msg.data else none
    let outputStr ← output.mapM fun md => md.toString
    return (termStr, "\n".intercalate outputStr)
  finally
    modify fun st => { st with messages := initMsgs }

open Lean Elab Command Meta Term in

/--
`#assert_same_evaluation #[term1, term2, ...]` evaluates all terms (via `#eval`) and
asserts they produce identical output. Useful for testing Velvet methods against expected values.

```
#assert_same_evaluation #[1 + 1, 2]
#assert_same_evaluation #[(decodeStr' input).run, expected]
```
-/
elab "#assert_same_evaluation " arr:term : command => do
  let `(#[$ts,*]) := arr
    | throwError "Expected array literal #[term1, term2, ...]"
  let terms := ts.getElems
  if terms.size < 2 then
    throwError "Need at least 2 terms to compare"
  let results ← terms.mapM evalAndCapture
  let (firstTerm, firstResult) := results[0]!
  for i in [1:results.size] do
    let (iTerm, iResult) := results[i]!
    if iResult != firstResult then
      throwError "Evaluations differ!\n\nTerm 1: {firstTerm}\n=> {firstResult}\n\nTerm {i+1}: {iTerm}\n=> {iResult}"
