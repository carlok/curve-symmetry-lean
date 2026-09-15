# Dedekind integral closure and points of the double cover (G07b-2a/2b) — 2026-09-15

The introducing commit is the checkpoint for these two packages. It follows
G07b-1 (`9327385`, private Linux run 34943343401).

## G07b-2a: QuadraticDedekind

With `W² − h` irreducible over `ℂ(t)` (as a `Fact`), `L = QuadField h` is
finite over `ℂ(t)` (power basis) and separable (characteristic zero).

- `quad_integralClosure_isDedekindDomain`: the integral closure of `ℂ[t]` in
  `L` is a Dedekind domain (`integralClosure.isDedekindDomain`).
- `quad_integralClosure_isFractionRing`: its fraction field is `L`.
- `quad_mem_integralClosure_iff`: its elements are `a + b·w`, `a, b ∈ ℂ[t]`,
  for squarefree `h` (G07b-1).
- `family_integralClosure_dedekind`: the family case.

## G07b-2b: QuadraticRing

`QuadRing h = ℂ[t][W]/(W² − h)`, the affine coordinate ring of the double cover.

- `quadRingMap`: the `ℂ[t]`-algebra map to `L`, `W ↦ w`.
- `quad_coeff_eq_zero`: `1, w` are independent over `ℂ(t)` for `h ≠ 0`
  (conjugation and `w² = h`).
- `quadRingMap_injective` and `quadRingMap_range`: for squarefree `h` the map
  is injective and its image is exactly the set of elements integral over
  `ℂ[t]`.
- `quadEval c d hd`: evaluation `t ↦ c`, `W ↦ d` for `d² = h(c)`; surjective
  onto `ℂ`, so its kernel is maximal.
- `exists_X_sub_C_mem`: every maximal ideal of `ℂ[t]` contains some `t − c`
  (a nonzero element factors over the algebraically closed field).
- `quadRing_isMaximal_iff`: every maximal ideal `𝔪` of `QuadRing h` is such a
  kernel. The contraction to `ℂ[t]` is maximal (integral extension), so it
  contains `t − c`. In the residue field, `w̄² = h(c)` forces `w̄ = ±d₀`, and
  the quotient map agrees with `ℂ ∘ quadEval` on generators.
- `quadEval_ker_injective`: distinct points give distinct maximal ideals.
- `family_quadRing_points`: all of this for `h_α`.

## Scope boundary

These are statements about the affine ring over the finite `t`-line. They do
not yet relate valuation rings (places) of `L` to these maximal ideals
(G07b-2c), and do not treat `t = ∞` (G07b-3). No differential, ramification
index or genus is defined.

## Checks

- Both new modules and aggregate compiled incrementally with warnings as errors.
- Namespace axiom audit: 1,343 declarations; only propext, Classical.choice,
  Quot.sound.
- Preflight: 84 modules, nine exact pins. Six package tests and
  `git diff --check` passed.
- Paper TeX/PDF hashes unchanged from ONBOARDING.md.

This snapshot requires its own CI result. No clean local rebuild,
independent checker, Palomar dry run or human review is claimed.
