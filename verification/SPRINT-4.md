# Sprint 4 gate — 2026-09-30

Sprint 4 covered the genus and the remaining paper claims. The gate, as
SPRINTS.md states it: the entire mathematical port is hole-free, and a
numerical branch-count identity does not count as a geometric-genus theorem.

## Rows audited against the TeX

Every row with sprint 4 in [COVERAGE.md](../COVERAGE.md), read against
`sharp_symmetry_bounds.tex` and the Lean statement it cites.

| Row | TeX | Lean | Reading | Verdict |
|---|---|---|---|---|
| S03 | Lemma 3 proof: no glide reflection; opposite symmetries have index two | `opposite_symmetry_no_glide`, `oppositeDirectEquiv` | as printed | matches |
| S04 | Lemma 3 (`lem:sign`): `f∘T = ε(T)f`, `ε = ±1`, `ε = 1` for reflections | `paper_isometry_sign` | as printed; `ε = 1` for every orientation-reversing symmetry, which is at least as strong | matches |
| S07 | equation (5) (`eq:radial`): `N > d` forces `N = 2m`, `ε = −1`, `P = X^m A(XY) + Y^m Ā(XY)`, `1 ≤ deg A ≤ ⌊(d−m)/2⌋`, `m ≤ d − 2` | `paper_high_order_radial_form` | as printed | matches |
| S10 | equation (`eq:quintic`): the Cartesian expansion equals `Re(z³(|z|² + i))`, `f(e^{πi/3}z) = −f(z)`, exactly six rotations | `quinticValue_eq`, `quintic_sixtyDegree_negates`, `sixtyDegree_isometry_order`, `quintic_isometry_count` | as printed; the full isometry group has six elements, so there are six rotations and no reflection | matches |
| G06 | Lemma 4 (`lem:geometry`): `(0,0)`, `(∞,∞)` ordinary `m`-fold points | `family_ordinary_multiple_points` | standard-chart multiplicity; chart-transition invariance not claimed | matches at the reading |
| G07 | Lemma 4: "its normalization" | `family_functionField_double_cover` and G07b | the function-field double cover (user-approved 2026-09-15) | matches at the reading |
| G08 | Lemma 4 proof: `2m+2` simple branch points, the roots of the two coprime factors and `0, ∞` | `family_branch_points` | branch points counted by fibres; ramification indices, hence "simple", not formalized | matches at the reading |
| G09 | Lemma 4: "its normalization has genus `m`", by Riemann–Hurwitz | `family_genus`, `paper_family_genus` | genus of the function field, the dimension of its holomorphic differentials; proved with an explicit basis | matches at the reading; route differs |
| G10 | Lemma 4 proof: for `r > 0`, `2m` angles on the circle of radius `r` | `family_metric_circle_card` | as printed, for every nonreal `α` | matches |
| R01 | Remark 5: `Re(z⁴) = 1` attains the rotation bound and is not in the `m = 2` family, genus three against two | `paper_degree_four_genus` | same genus reading as G09; no direct or opposite similarity, for every nonreal parameter | matches at the reading |

## No substitute invariant

- R01 goes through genus, as printed (user decisions 2026-09-15 and
  2026-09-28): genus exactly three against two. The non-similarity is not
  derived from some other invariant.
- G09 and R01 compute a genus: the dimension of the holomorphic differentials
  of the function field, defined without a chosen model (R01a). They do not
  use a numerical branch count. G08's count is a separate row.
- Route difference: the paper proves Lemma 4's genus by Riemann–Hurwitz. Lean
  proves it with an explicit basis `tⁱ·dt/w`, `i < m`. The Riemann–Hurwitz
  degree identity as a divisor statement is not pursued (user decision
  2026-09-28).

## Coverage after the gate

Every principal, supporting and geometry row of COVERAGE.md is proved, some at
a recorded reading (G01, G05–G09, G11, R01). R01–R03 are proved. R04 and R05 are
scope restrictions, not theorems. No row is open.

## Verification

- Proof commit `b8c207e` (R01e-3): full clean `lean/check.sh` against the
  v4.34.0 reuse installation passed; the namespace audit passed 2,058
  declarations with only `propext`, `Classical.choice` and `Quot.sound`;
  109 modules, nine exact dependency pins, six package tests. Private Linux run
  `36617682447` and Palomar Theorem 1 entry build `36617682484` passed.
- The gate commit changes documentation only. Its full clean `lean/check.sh`
  was rerun on the same Lean sources before the commit.
- Tag: `sprint-4-complete` (annotated) on the gate commit, once its Linux run
  passes. Pushing the tag is the user's decision.

No human review, registry acceptance beyond Theorem 1, or novelty
certification is implied.
