# Packages 4 and 5 complete — 2026-09-14

The introducing commit is the completion snapshot.

## Package 4

FamilyEuclidean adds:

- family_affine_self_filter: any nondegenerate affine self-inclusion has
  zero translation and coefficient satisfying a^(2m)=1.
- family_isometry_iff_rotation: actual Mathlib Euclidean isometries preserve
  the curve iff they are one of these centered root rotations.
- family_isometry_card: the full actual isometry group has exactly 2m elements.

Assumptions: m>=2, nonreal alpha, norm alpha=1. This includes the quartic case.
The previous no-opposite result and actual-isometry classification are used;
no preservation of the origin is assumed.

## Package 5

FamilyAlgebraic proves algebraicity over Q of the two normal-form coefficients,
then constructs an algebraic-entry invertible matrix with the same action at
every sphere point. The endpoint familyAmbientGroup_algebraic_representative
applies directly to the independently defined actual ambient group.
It additionally assumes IsAlgebraic Q alpha.

The conclusion is existence of an algebraic representative, not algebraicity
of arbitrary representatives: scalar rescaling can introduce transcendental
entries without changing a projective transformation. No anti-Möbius
symmetries need separate representatives, by the earlier exclusion theorem.

## Checks

Both changed proof modules and the aggregate compiled incrementally with
warnings as errors, using installed Lean 4.32.0 and the pinned Mathlib.
The entire namespace audit passed for 1,096 declarations with only propext,
Classical.choice, Quot.sound. Preflight: 73 modules, nine exact pins.
All six package tests and the whitespace check passed.

TeX and PDF hashes remain unchanged:

```text
3aff1c6edf6f189de6fa56c690631c266364a3b129408eb0fd5a200ceb186925 sharp_symmetry_bounds.tex
8b1f71e7a4f5dbce7fce3de383b675411e3fbba21bea4939609991f47a10ffd1 sharp_symmetry_bounds.pdf
```

Preceding commit f8021b8 passed Linux run 34848974599; its second run was
still in progress when checked. This completion snapshot needs its own CI.
No clean local rebuild, independent replay, or Palomar dry run is claimed.
Package 6 (parameter-family consequence) remains; Sprints 4–7 remain.
