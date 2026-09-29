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

A [Lean port](lean/README.md) verifies every clause of Theorem 1, starting from real Cartesian polynomials and actual Euclidean isometry groups, and every clause of Theorem 2 for actual ambient transformations: arbitrary Möbius or anti-Möbius spherical containment forces the stated forms, the full ambient group is dihedral of order `4m`, the Euclidean group is the `2m` rotations, and the parameter-equivalence criteria hold. Lemma 4 is proved: irreducibility, the singular pair and its ordinary `m`-fold points (in standard charts), and genus `m` read as the genus of the function field (dimension of its holomorphic differentials). The Lean route to the genus is an explicit basis, not Riemann–Hurwitz. **Remark 5's genus comparison with `Re(z⁴)=1` (three versus two) is not yet formalized.** Readings and scope limits are in [COVERAGE.md](COVERAGE.md). Local development reuses installed Lean/Mathlib without copying libraries; private Linux CI independently rebuilds from the pinned dependencies.

Theorem 1 alone is also published in the separate public repository [`carlok/sharp-symmetry-bounds-lean`](https://github.com/carlok/sharp-symmetry-bounds-lean) and registered with Palomar as [`PALOMAR-2026-09-18-000007`](https://palomar-registry.org/entry?id=PALOMAR-2026-09-18-000007&version=1), after mechanical verification and an automated editorial review. That is neither a human review nor a novelty certificate, and it covers nothing else in this repository.

The paper is unchanged during the formalization sprints. This is an independent
Apache-2.0 project; its remote is the verified private repository
`carlok/curve-symmetry-lean`. See [SPRINTS.md](SPRINTS.md) for completion gates
and [migration evidence](verification/MIGRATION.md). This repository stays
private. No arXiv preprint is planned; any release or further Palomar entry
needs the user's explicit go.

## Reproduce

The root is a Lake project pinned to Lean 4.34.0 and an exact Mathlib revision.
On this Mac, reuse the installed dependency tree without downloading libraries:

```sh
rtk proxy sh lean/check.sh /Users/carlo/Documents/varie/hacks/lean4/mathlib-v4.34.0-reuse
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
