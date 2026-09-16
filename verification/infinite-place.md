# The place over t = ∞ and the full place classification (G07b-3) — 2026-09-16

The introducing commit is the checkpoint for this package. It follows
G07b-2c (`e209f92`, private Linux run 34945242761).

## Idea

With `s = 1/t` and `w' = w·s^(m+1)`, `w² = h_α(t)` becomes
`w'² = h_{conj α}(s)`, because
`h_α(1/s) = h_{conj α}(s)·s^(−(2m+2))` (`familyH_inv_identity`). So the chart at
infinity is the same family with the conjugate parameter, and the finite-place
classification (G07b-2c) applies to it.

## Results (QuadraticInfinity)

- `ratInv`: the `ℂ`-algebra map `ℂ(t) → ℂ(t)`, `t ↦ 1/t` (from transcendence of
  `1/t`); `ratInv_surjective`.
- `familyInfinityMap`, `familyInfinityMap_surjective`, `familyInfinityEquiv`:
  the ring isomorphism `ℂ(t)[W]/(W² − h_α) ≃ ℂ(s)[W]/(W² − h_{conj α})`, with
  `t ↦ 1/s` (`familyInfinityMap_t`), constants fixed (`familyInfinityMap_polyC`)
  and `w ↦ w'·s^(−(m+1))`.
- `familyInfinityPlace`: the pullback of the point place `(0, 0)` of the
  conjugate family.
- `quadPlace_X_inv_mem_iff`: in the point place `(c, d)`, `1/s` is integral iff
  `c ≠ 0` (center computation).
- `familyInfinityPlace_ne_top`, `familyInfinityPlace_const`,
  `familyInfinityPlace_t_notMem`: it is a place containing the constants, not `t`.
- `place_eq_quadPlace_of_t_mem`: a place containing the constants and `t` is a
  point place.
- `place_eq_infinity_of_t_notMem`: a place containing the constants but not `t`
  is `familyInfinityPlace`. It transfers the place to the conjugate chart,
  where it contains `ℂ[s]` with `s` noninvertible, forcing the point `(0, 0)`.
- `family_place_classification`: every valuation subring `O ≠ L` containing the
  constants is a point place `(c, d)`, `d² = h_α(c)`, or the unique place at
  infinity.

With G07a, G07b-1, G07b-2a/b/c this completes the description of the
places (points of the normalization, under the approved function-field
reading) of the function field of `V_α`.

## Scope boundary

No ramification index, differential or genus is defined. The count of distinct
roots of `h_α` and the ramification of each place over `ℂ(t)` (G08), and genus
(G09), remain.

## Checks

- New module and aggregate compiled incrementally with warnings as errors.
- Namespace axiom audit: 1,420 declarations; only propext, Classical.choice,
  Quot.sound.
- Preflight: 87 modules, nine exact pins. Six package tests and
  `git diff --check` passed.
- Paper TeX/PDF hashes unchanged from ONBOARDING.md.

This snapshot requires its own CI result. No clean local rebuild,
independent checker, Palomar dry run or human review is claimed.
