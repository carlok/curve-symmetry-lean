import CurveSymmetry
import Lean.Util.CollectAxioms

/-! Local/CI dependency audit, not an independent checker or Palomar dry run.
Inspect every declaration in the project's namespace, including private names.
The accompanying source audit checks that library namespaces stay in this scope. -/

open Lean in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    if (`CurveSymmetry).isPrefixOf (privateToUserName name) then
      let axioms ← collectAxioms name
      for axiomName in axioms do
        unless allowed.contains axiomName do
          throwError "Forbidden axiom {axiomName} in {name}"
      checked := checked + 1
  if checked == 0 then
    throwError "Empty audit: the proof library was not loaded"
  logInfo m!"Axiom audit passed: {checked} declarations; allowlist propext, Classical.choice, Quot.sound"
