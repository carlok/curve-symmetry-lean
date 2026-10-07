/-
Phase 5, solution check: for every node, read the built `Sol_*.olean` and
`Thm_*.olean` (no environment is built, so the many `solution` constants do not
clash) and require the elaborated type of `solution` to equal the type of the
statement stub, binder names and binder info included, with the same universe
parameters.

Usage: lake env lean --run p2m/check_solutions.lean <pairs file>
Each line of the pairs file: <Sol olean> <Thm olean> <full theorem name>.
-/
import Lean
open Lean

/-- The first binder where two alpha-equivalent types differ in binder info, or in
binder name once hygiene (macro scopes, which carry the module name) is erased. -/
partial def binderDiff : Expr → Expr → Option String
  | .forallE n₁ t₁ b₁ i₁, .forallE n₂ t₂ b₂ i₂ | .lam n₁ t₁ b₁ i₁, .lam n₂ t₂ b₂ i₂ =>
    if n₁.eraseMacroScopes != n₂.eraseMacroScopes || i₁ != i₂ then
      some s!"{n₁} ({repr i₁}) vs {n₂} ({repr i₂})"
    else (binderDiff t₁ t₂).orElse fun _ => binderDiff b₁ b₂
  | .letE n₁ t₁ v₁ b₁ _, .letE n₂ t₂ v₂ b₂ _ =>
    if n₁.eraseMacroScopes != n₂.eraseMacroScopes then some s!"let {n₁} vs {n₂}" else
    ((binderDiff t₁ t₂).orElse fun _ => binderDiff v₁ v₂).orElse fun _ => binderDiff b₁ b₂
  | .app f₁ a₁, .app f₂ a₂ => (binderDiff f₁ f₂).orElse fun _ => binderDiff a₁ a₂
  | .mdata _ e₁, .mdata _ e₂ | .proj _ _ e₁, .proj _ _ e₂ => binderDiff e₁ e₂
  | _, _ => none

unsafe def main (args : List String) : IO UInt32 := do
  let some (listFile : String) := args[0]?
    | do IO.eprintln "usage: lake env lean --run check_solutions.lean <pairs file>"
         return 2
  let mut strict : Nat := 0
  let mut hyg : Nat := 0
  let mut bad : Nat := 0
  for l in (← IO.FS.lines ⟨listFile⟩) do
    match l.splitOn " " with
    | [sol, thm, nm] =>
      let (sd, sr) ← readModuleData ⟨sol⟩
      let (td, tr) ← readModuleData ⟨thm⟩
      match sd.constants.find? (·.name == `solution), td.constants.find? (·.name == nm.toName) with
      | some sc, some tc =>
        if sc.levelParams != tc.levelParams then
          bad := bad + 1
          IO.println s!"DIFFER  {nm}: universe parameters {sc.levelParams} vs {tc.levelParams}"
        else if sc.type.equal tc.type then
          strict := strict + 1
        else if sc.type == tc.type && (binderDiff sc.type tc.type).isNone then
          hyg := hyg + 1
        else
          bad := bad + 1
          IO.println s!"DIFFER  {nm} (alpha-equivalent: {sc.type == tc.type}; first binder difference: {binderDiff sc.type tc.type})"
      | _, _ =>
        bad := bad + 1
        IO.println s!"MISSING {nm}"
      sr.free
      tr.free
    | _ => IO.println s!"BAD LINE {l}"
  IO.println s!"solution type identical to the statement: {strict}; identical up to hygienic binder names: {hyg}; differing or missing: {bad}"
  return (if bad == 0 then 0 else 1)
