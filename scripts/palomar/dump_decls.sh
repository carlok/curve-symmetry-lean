#!/bin/sh
# Pre-check only, NOT the Palomar Comparator: print the elaborated types of the
# compared theorems and the types and values of the Challenge definitions from a
# given module (Challenge or Solution), and the axioms of each theorem.
# Usage: LEAN_PATH=... sh dump_decls.sh <Module>
set -eu
mod=$1
tmp=$(mktemp -d)
cat > "$tmp/Dump.lean" <<LEAN
import $mod
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let thms := [\`SharpSymmetryBounds.sharp_bounds, \`SharpSymmetryBounds.rotation_bound_sharp,
    \`SharpSymmetryBounds.full_bound_sharp, \`SharpSymmetryBounds.equality_classification,
    \`SharpSymmetryBounds.family_attains_bound]
  let defs := [\`SharpSymmetryBounds.realCurve, \`SharpSymmetryBounds.symmetries,
    \`SharpSymmetryBounds.directSymmetries, \`SharpSymmetryBounds.extremalCurve]
  for n in thms ++ defs do
    let some ci := env.find? n | throwError "missing {n}"
    IO.println s!"TYPE {n} := {ci.type.dbgToString}"
  for n in defs do
    let some ci := env.find? n | throwError "missing {n}"
    match ci.value? with
    | some v => IO.println s!"VALUE {n} := {v.dbgToString}"
    | none => throwError "no value {n}"
LEAN
elan run leanprover/lean4:v4.34.0 lean "$tmp/Dump.lean"
rm -rf "$tmp"
