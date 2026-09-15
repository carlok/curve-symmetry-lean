# Integral closure of ℂ[t] in the double cover (G07b-1) — 2026-09-15

The introducing commit is the checkpoint for this package. It follows G07a
(`cac8e03`, private Linux run 34940883130).

## Results

QuadraticIntegralClosure works with `QuadField h = ℂ(t)[W]/(W² − h)` for any
`h ∈ ℂ[t]`. No irreducibility instance is used, which avoids the field/ring
instance diamond of `AdjoinRoot`; nontriviality follows from degree two.

- `quad_exists_eq`: every element is `a + b·w` with `a, b ∈ ℂ(t)`
  (reduction modulo the monic quadratic).
- `quadConj`, `quadConj_apply`: the `ℂ(t)`-algebra conjugation `w ↦ −w`.
- `quad_ratFunc_integral`: an element of `ℂ(t)` integral over `ℂ[t]` inside
  `L` is a polynomial, since `ℂ[t]` is integrally closed.
- `ratFunc_polynomial_of_sq_mul`: if `b² h` is polynomial and `h` is
  squarefree then `b` is polynomial. The reduced denominator `q` satisfies
  `q² ∣ h`, so it is a monic unit, i.e. `1`.
- `quad_isIntegral_iff`: for squarefree `h`, `x` is integral over `ℂ[t]` iff
  `x = a + b·w` with `a, b ∈ ℂ[t]`. Trace `2a` and norm `a² − b²h` of an
  integral element are integral elements of `ℂ(t)`, hence polynomials.
- `family_isIntegral_iff`: the family case, using `familyH_squarefree_of`.
  The field is `AdjoinRoot (familyQuadraticRat m α)` definitionally
  (`quadRat_familyH`), which G07a identified with the function field of `V_α`.

## Scope boundary

This describes the integral closure as a set of elements; it does not yet
package it as a Dedekind domain, construct its maximal ideals, or classify
places. G07b-2 (places over finite `t`), G07b-3 (place over infinity and the
full classification), G08, G09 and R01 remain.

## Checks

- New module and aggregate compiled incrementally with warnings as errors.
- Namespace axiom audit: 1,308 declarations; only propext, Classical.choice,
  Quot.sound.
- Preflight: 82 modules, nine exact pins. Six package tests and
  `git diff --check` passed.
- Paper TeX/PDF hashes unchanged from ONBOARDING.md.

This snapshot requires its own CI result. No clean local rebuild,
independent checker, Palomar dry run or human review is claimed.
