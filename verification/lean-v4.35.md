# Move to Lean 4.35.0 (2026-10-16)

From Lean 4.34.0 with Mathlib `5ed2965` (tag `v4.34.0`) to Lean 4.35.0 with Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679` (tag `v4.35.0`), 651 Mathlib commits later.
The eight inherited pins come from Mathlib's own manifest at that tag. Both lock files
(the root and `palomar/theorem1/`) and `scripts/palomar/dump_decls.sh` follow.

## What changed

Five modules, 18 lines, all forced by the new versions:

- `HomogeneousDifferential`, `PolynomialDifferential`: the unused-tactic linter now
  rejects the branches of `first | rfl | (ext v; simp …)` that never run; only the
  branch that closes the goals is kept.
- `QuadraticRing`: `SetLike.exists_of_lt` is deprecated in favour of
  `IsConcreteLE.exists_of_lt`.
- `PlaceUniformizers` (five statements), `InfinityDifferentials` (one statement): a
  singleton set `{f a (b)}` written across lines now parses as the start of a
  `{… | …}` set-builder. The element is put in parentheses, `{(f a (b))}`. This
  changes the spelling, not the elaborated statement.

No declaration was added, removed or renamed. None of the 30 modules shared with the
public Theorem 1 repository `carlok/sharp-symmetry-bounds-lean` changed. The
registered Palomar entry is a fixed record and is not affected. The Prove2Me copy
of the library stays on the platform's Lean 4.33.1 and Mathlib `0df444a`.

## Checks

- Full clean `lean/check.sh` against a new reuse installation at the v4.35.0 pins,
  warnings as errors: exit 0.
- Namespace axiom audit: 2,058 declarations, the same as before; only `propext`,
  `Classical.choice`, `Quot.sound`.
- `scripts/check_sources.py --reuse`: 109 modules, 9 exact dependency revisions.
- Package tests: 10 passing.
- CI on `main` at `a2c13b7`: Linux build `38872333753`, Palomar Theorem 1 entry
  build `38872333805`, negative controls `38872333742`, all green.
