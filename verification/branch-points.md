# Branch points of the double cover (G08) — 2026-09-16

The introducing commit is the checkpoint for this package. It follows G07b-3
(`24404dd`, private Linux run 35093882792).

## Recorded choice (user decision, 2026-09-16)

The project is already large, so the simplest honest notion is used. A point of
the `t`-line is a branch point of the degree-two cover when fewer than two places
of the function field lie over it (the classical fibre-count definition for a
finite cover). A place lies over a finite `c` when `t − c` belongs to it and is
not a unit; it lies over `∞` when it does not contain `t`. Ramification indices
are not defined, so the paper's word "simple" (index two) is not separately
formalized. For a degree-two cover it follows from the fundamental identity
`Σ e·f = 2`, which is also not formalized.

## Results (FamilyBranchPoints)

- `quadPlace_poly_inv_mem_iff`: in the point place `(c, d)`, `1/p(t)` is integral
  iff `p(c) ≠ 0`.
- `familyPlacesOver`, `IsFamilyBranchPoint`: the definitions above, over
  `OnePoint ℂ`.
- `mem_familyPlacesOver_coe`: places over a finite `c` are exactly the point
  places `(c, d)`, `d² = h_α(c)`.
- `familyPlacesOver_infty`: the only place over `∞` is `familyInfinityPlace`.
- `familyPlacesOver_coe_ncard`: one place over `c` if `h_α(c) = 0`, two otherwise.
- `familyH_roots_card`: `h_α` has exactly `2m+1` distinct roots (separable of
  degree `2m+1` over an algebraically closed field).
- `family_branch_points`: the branch points are exactly `∞` and the roots of
  `h_α`; there are `2m+2` of them; `∞` and `0` are branch points; every other
  point has two places over it.

## Scope boundary

No ramification index, differential, Riemann–Hurwitz formula or genus. G09 and
R01 remain and are deferred by user decision in favour of preparing the
Theorem 1 Palomar entry.

## Checks

- New module and aggregate compiled incrementally with warnings as errors.
- Namespace axiom audit: 1,440 declarations; only propext, Classical.choice,
  Quot.sound.
- Preflight: 88 modules, nine exact pins. Six package tests and
  `git diff --check` passed.
- Paper TeX/PDF hashes unchanged from ONBOARDING.md.

This snapshot requires its own CI result. No clean local rebuild,
independent checker, Palomar dry run or human review is claimed.
