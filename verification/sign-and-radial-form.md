# Lemma 3 sign and equation (5) — 2026-09-15

The introducing commit is the checkpoint for these two bounded Sprint 4
packages. It succeeds `2cff8af`, which passed private Linux runs 34937614030
and 34937613937.

## Lemma 3 sign (S03, S04): IsometrySign

- `opposite_symmetry_no_glide`: for irreducible `P` of degree at least two with
  nonempty real locus, an opposite symmetry `z ↦ a conj(z) + b` satisfies
  `a conj(b) + b = 0`, because its square is that translation.
- `opposite_symmetry_fixed_point`: it fixes `b/2`, so it is a reflection in a
  line, not a glide reflection.
- `isometry_sign_of_realLocus`: for every element `T` of the actual isometry
  group of the real locus, `P(Tz, conj Tz) = ε P(z, conj z)` for all `z`, with
  `ε = ±1`, and `ε = 1` whenever `T` has opposite form. A direct map with
  `a = 1` is the identity by translation exclusion. Otherwise its fixed point
  is moved to the origin with `shift`, and `rotation_sign_of_realLocus` or
  `reflection_fixes_equation` supplies the sign.
- `paper_isometry_sign`: the same for a geometrically irreducible real
  Cartesian `f`, stated as `f(Re Tz, Im Tz) = ε f(Re z, Im z)` with real `ε`.

The identity is between polynomial functions on the real plane. It does not
define a sign homomorphism; the paper does not claim one.

## Equation (5) (S07): RadialAntiForm

- `weightPolynomial P m` and `oppositeWeightPolynomial P m` collect the
  coefficients of `X^(k+m) Y^k` and `X^k Y^(k+m)` as one-variable polynomials.
- `anti_radial_form`: if `rotate ζ P = -P`, `ζ` is a primitive `2m`th root and
  `deg P < 2m`, then `P = X^m A(XY) + Y^m B(XY)` with both natural degrees at
  most `(deg P - m)/2` (floor division).
- `irreducible_anti_radial_form`: with conjugate-symmetric coefficients,
  `B = conj A`; for irreducible `P` and `m ≥ 2`, `A` is nonconstant and
  `m + 2 ≤ deg P`.
- `complexifyReal_conjugate_coeff`: complexified real Cartesian equations have
  conjugate-symmetric coefficients.
- `paper_high_order_radial_form`: a geometrically irreducible non-circle real
  Cartesian curve of degree at least two, with infinite zero set and a rotation
  `z ↦ ζz` of primitive order `N > d`, has `N = 2m`, sign `-1`, and equation (5)
  with `1 ≤ deg A ≤ ⌊(d-m)/2⌋` and `m + 2 ≤ d`.

## Checks

- Both new modules and aggregate compiled incrementally with warnings as errors.
- Namespace axiom audit: 1,223 declarations; only propext, Classical.choice,
  Quot.sound.
- Preflight: 80 modules, nine exact pins. Six package tests and
  `git diff --check` passed.
- Paper TeX/PDF hashes unchanged from ONBOARDING.md.

This snapshot requires its own CI result. No clean local rebuild, independent
checker, Palomar dry run or human review is claimed. Sprint 4 still needs
G07–G09 (normalization, ramification, genus) and R01.
