# Parameter arc and centered-circle sections — 2026-09-14

The introducing commit is this completion snapshot.

## Package 6 and Sprint 3 exit audit

FamilyParameterArc proves unit modulus and positive imaginary part for
exp(i theta), 0<theta<pi; injectivity follows from strict monotonicity of cos
on [0,pi]. Positive imaginary parts exclude conjugate equality.
family_arc_equivalence_iff then uses the checked ambient equivalence criteria:
either holomorphic or antiholomorphic spherical equivalence exists iff the
angles are equal. This closes R02 for every m>=2.

The Sprint 3 ledger now has proved entries T2.1–T2.7, G13, R02, R03.
These use actual Euclidean/sphere maps; zero, infinity, and m=2 are included
where claimed. The nonreal and normalized parameter restrictions remain.
Sprint 3 is complete. This does NOT close the separate genus/normalization
or remaining supporting-exposition obligations assigned to Sprint 4.

## First Sprint 4 package: G10

FamilyCircleSections proves that points of equal nonzero modulus on the
family have ratio whose 2m-th power is one. Conversely every root rotation
preserves both family and modulus. familyCircleRootEquiv gives an explicit
bijection from the roots of unity to the circle section, using any section
point; existence was already proved by family_point_of_norm.

family_metric_circle_card counts the actual intersection with Metric.sphere
0 r. It gives exactly 2m points for m>0, nonreal alpha, r>0, with no norm-one
hypothesis on alpha. The free orbit description also gives the angular
spacing interpretation without choosing an argument branch.

## Verification

Both modules and aggregate compiled incrementally with warnings as errors.
Whole namespace audit: 1,125 declarations, only propext, Classical.choice,
Quot.sound. Preflight: 75 modules, nine exact pins. Six package tests and
whitespace checks passed. Installed Lean 4.32.0/Mathlib were reused unchanged.
TeX/PDF hashes remain those recorded in ONBOARDING.md.

The preceding 54f2f1a passed Linux runs 34849856938 and 34849856066.
Those runs do not verify this new commit; its Linux CI must be checked
separately. No clean local rebuild, NanoDa replay, or Palomar dry run is claimed.

Next: an explicitly scoped remaining Sprint 4 obligation, such as G06's
ordinary-multiple-point interface. G07–G09 and R01 remain substantial.
