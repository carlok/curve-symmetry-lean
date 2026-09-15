# Tangent directions and explicit quintic — 2026-09-15

The introducing commit is the checkpoint for these two bounded packages.

## Projective tangent directions

BinaryTangentDirections defines directions by the homogeneous binary-form
zero locus on Mathlib Projectivization. binaryTangentDirections_mk proves
independence from nonzero representative scaling. The finite chart is exactly
z^m=-b/a; infinity is excluded when a is nonzero. A root-of-unity bijection
proves exactly m directions for m>0 and nonzero a,b.
family_diagonal_tangent_direction_counts specializes to the two displayed
cones, alpha X^m + conjugate(alpha)Y^m and X^m+Y^m.

This is not a normalization or multiplicity theorem. G06 stays partial
pending its geometric ordinary-point/multiplicity interface.

## Printed quintic

QuinticExample proves the Cartesian expression as an identity of functions
on C, identifies its zero set with the m=3, alpha=i family, and verifies
negation under multiplication by exp(pi*i/3). The coefficient is a primitive
sixth root; sixtyDegree_isometry_order separately proves exact order six of
the actual Euclidean isometry. The full isometry count is six by the existing
family theorem. This closes the outstanding explicit calculations in S10.

## Checks and limits

Both modules and aggregate compiled incrementally with warnings as errors.
Namespace audit: 1,149 declarations; only propext, Classical.choice, Quot.sound.
Preflight: 77 modules, nine pins. Six package tests and whitespace checks passed.
Installed dependencies were reused without source modification. Paper TeX/PDF
hashes are unchanged from ONBOARDING.md.

Previous 8688b5e passed private Linux runs 34880827187 and 34880827101.
This new snapshot requires its own CI result. No clean local rebuild,
independent checker, Palomar dry run, or human review is claimed.
Sprint 4 remains incomplete, notably G06–G09, R01, S04 and S07.
