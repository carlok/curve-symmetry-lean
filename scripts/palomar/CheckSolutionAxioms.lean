import Solution
import Lean.Util.CollectAxioms

/-! Pre-check (not Comparator): the five compared Solution theorems depend only on
`propext`, `Classical.choice` and `Quot.sound`. -/

open Lean in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let thms := [`SharpSymmetryBounds.sharp_bounds, `SharpSymmetryBounds.rotation_bound_sharp,
    `SharpSymmetryBounds.full_bound_sharp, `SharpSymmetryBounds.equality_classification,
    `SharpSymmetryBounds.family_attains_bound]
  for n in thms do
    for ax in ← collectAxioms n do
      unless allowed.contains ax do
        throwError "Forbidden axiom {ax} in {n}"
  logInfo m!"Solution axiom pre-check passed for {thms.length} theorems"
