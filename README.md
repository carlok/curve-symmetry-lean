# Sharp symmetry bounds for real algebraic curves

Read [the four-page paper](sharp_symmetry_bounds.pdf), or its [TeX source](sharp_symmetry_bounds.tex).

This is an autonomous working note. It does not use Díaz's conjecture, the transcendental-number framework, or any result whose proof is left in `p20_astra.tex`.

For an infinite geometrically irreducible real plane curve of degree `d >= 2`, other than a circle, the paper proves:

- At most `max(d, 2d-4)` rotations, with equality examples in every degree.
- At most `2d` Euclidean symmetries, also sharp in every degree.
- A classification of the curves attaining the rotation bound when `d >= 5`, including their exact ambient Möbius groups and equivalences. The extremal family has no anti-Möbius self-equivalence.

The elementary coefficient method is credited to Lebmeir–Richter-Gebert and Lebmeir. The proposed contribution is the sharp bounds and the equality-case classification, not that method. An explicit irreducible quintic contradicts the degree restriction in Lemma 9 of **arXiv:1801.09962v1**. Access to the accepted/journal version failed, so the paper deliberately makes no claim about that version.

The note also replaces the auxiliary `4d` symmetry bound in the checked Pach–de Zeeuw manuscript by `2d`. This improves a constant, not the exponent in their distinct-distance result.

## Status

Proofs have been reconstructed, checked against exceptional cases, and tested with exact symbolic arithmetic. The literature search found the underlying method, but not the sharp-bound/equality-classification package stated here. **That is not a certificate of novelty.** No external expert review has occurred. The relevant versions and remaining checks are recorded in [CHECKS.md](CHECKS.md).

A [Lean port](lean/README.md) verifies every clause of Theorem 1, starting from real Cartesian polynomials and actual Euclidean isometry groups. For Theorem 2, the global Jacobian locus and the four-form completeness theorem are now checked: arbitrary Möbius or anti-Möbius spherical containment forces the stated forms, without assuming preservation of the singular pair. Local tangent-cone calculations and exact coefficient tests are also checked. **The Zariski-closure identification, full sphere-group classification, parameter-filter application, and genus assertions remain incomplete. No Palomar dry run has occurred.** Local development reuses installed Lean/Mathlib without copying libraries; private Linux CI independently rebuilds from the pinned dependencies.

The paper is unchanged during the formalization sprints. This is an independent
Apache-2.0 project; its remote is the verified private repository
`carlok/curve-symmetry-lean`. See [SPRINTS.md](SPRINTS.md) for completion gates
and [migration evidence](verification/MIGRATION.md). No public release or
Palomar submission is authorized by the current work.

## Reproduce

The root is a Lake project pinned to Lean 4.32.0 and an exact Mathlib revision.
On this Mac, reuse the installed dependency tree without downloading libraries:

```sh
rtk proxy sh lean/check.sh /Users/carlo/Documents/varie/hacks/lean4/diaz-modulus-lean
```

For a clean machine, with Elan installed:

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true verification/Audit.lean
python3 scripts/check_sources.py
```

The Linux workflow builds from a fresh private checkout, uses upstream Mathlib
cache artifacts, and checks all project-namespace axiom dependencies. It is
**not** the sandboxed Comparator/NanoDa dry run. The claim-by-claim boundary is
in [COVERAGE.md](COVERAGE.md); the kernel does not check that editorial ledger.

From this folder:

```sh
uv run verify.py
latexmk -pdf -interaction=nonstopmode -halt-on-error sharp_symmetry_bounds.tex
chktex -q sharp_symmetry_bounds.tex
```

The script declares and pins SymPy 1.14.0. Its 2,082 checks use exact arithmetic and include support tests through degree 40; they supplement the general proofs rather than replace them. `uv` needs network access on the first run unless the dependency is cached.
