# Places over the finite t-line (G07b-2c) — 2026-09-15

The introducing commit is the checkpoint for this package. It follows
G07b-2a/2b (`6e43f53`, private Linux run 34944104779).

A place of `L = ℂ(t)[W]/(W² − h)` is taken to be a valuation subring `O ≠ L`.
Places "over the finite `t`-line" are those containing `ℂ[t]`. A valuation
subring containing `ℂ[t]` automatically contains the constants `ℂ`.

## Generic part: DedekindPlaces

For a Dedekind domain `A` with fraction field `K`:

- `primeValuationSubring K P hP`: the localization `A_P` inside `K` for a
  nonzero prime `P`. It is a valuation subring because `A_P` is a DVR
  (`IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain`).
- `placeCenter K O hO`: the contraction to `A` of the maximal ideal of a
  valuation subring `O ⊇ A`.
- `placeCenter_ne_bot`: the center is nonzero when `O ≠ K`.
- `eq_primeValuationSubring_of_le`: a valuation subring `O ≠ K` containing
  `A_P` equals `A_P`. Its overrings correspond to primes of the DVR `A_P`
  (`ValuationSubring.ofPrime_idealOfLE`), which are `⊥` or maximal.
- `eq_primeValuationSubring_placeCenter`: every `O ≠ K` containing `A` equals
  `A_P` at its center.
- `placeCenter_primeValuationSubring`, `primeValuationSubring_ne_top`,
  `primeValuationSubring_injective`: the center of `A_P` is `P`, `A_P ≠ K`, and
  distinct primes give distinct valuation subrings.

## Family part: QuadraticPlaces

- `QuadRing h` receives the algebra structure `quadRingMap`. For squarefree
  `h` with `W² − h` irreducible it is an integral closure of `ℂ[t]` in `L`,
  hence a Dedekind domain with fraction field `L`.
- `quadRing_mem_of_polynomial_mem`: a valuation subring containing `ℂ[t]`
  contains `ℂ[t][w]`, since `w² = h(t)` and `x² ∈ O` forces `x ∈ O`.
- `quadPlace h c d hd`: the place at the point `(c, d)`, `d² = h(c)`.
- `quad_finite_place_classification`: each point place is a place containing
  `ℂ[t]`; every such place is a point place; distinct points give distinct
  places (via `quadRing_isMaximal_iff` and `quadEval_ker_injective`).
- `quad_points_over`: two points over `t = c` if `h(c) ≠ 0`, one if `h(c) = 0`.
- `family_finite_place_classification`: the family case for `h_α`.

## Scope boundary

Places not containing `t` (over `t = ∞`) are G07b-3. No ramification index,
order of a differential or genus is defined here. The identification of these
places with the points of the normalization is the approved fidelity reading
recorded in COVERAGE.

## Checks

- Both new modules and aggregate compiled incrementally with warnings as errors.
- Namespace axiom audit: 1,383 declarations; only propext, Classical.choice,
  Quot.sound.
- Preflight: 86 modules, nine exact pins. Six package tests and
  `git diff --check` passed.
- Paper TeX/PDF hashes unchanged from ONBOARDING.md.

This snapshot requires its own CI result. No clean local rebuild,
independent checker, Palomar dry run or human review is claimed.
