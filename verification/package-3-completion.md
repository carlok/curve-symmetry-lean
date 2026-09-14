# Package 3 completion — 2026-09-14

This report belongs to the commit introducing it. The exact commit can be
recovered with `git log -1 --format=%H -- verification/package-3-completion.md`.

## Mathematical scope

`lean/FamilyDihedral.lean` proves:

- The four composition laws of actual sphere dilations and inversions,
  including their behavior at zero and infinity.
- A cyclic-root parametrization and a faithful dihedral sphere action.
- Surjectivity onto `familyAmbientGroup`, which was independently defined
  as the Möbius permutation image intersected with the curve set stabilizer.
- `familyAmbientGroup_dihedral`: an isomorphism with
  `DihedralGroup (2*m)`.
- `familyAmbientGroup_card`: cardinality exactly `4*m`.
- `familyAmbientGroup_generators`: generators of orders `2*m` and `2`,
  the relation `s*r*s = r⁻¹`, and exhaustion by `r^i` and `s*r^i`
  for `0 <= i < 2*m`.

The public conclusions assume exactly `m >= 2`, nonreal complex parameter
`alpha`, and `norm alpha = 1`. The base inversion coefficient is obtained
from algebraic closedness, not added as a hypothesis to those conclusions.
The previous no-anti-Möbius theorem excludes the other parity, so this is
the full ambient group claimed in T2.5. The case m=2 is included.

## Verification

Lean 4.32.0; Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`.
New module and aggregate compiled incrementally with warnings as errors and
installed dependencies reused. The complete namespace audit passed for 1,075
declarations using only `propext`, `Classical.choice`, and `Quot.sound`.
Source preflight passed (71 modules, nine exact pins), all six package tests
passed, and the source diff passed whitespace checks.

The preceding commit 30bcfb0 passed private Linux runs 34823034995 and
34823034336. This completion commit requires its own CI result; those earlier
runs do not certify the new module. No clean local rebuild, NanoDa replay,
Palomar dry run, or independent human review is claimed here.

TeX and PDF hashes are unchanged:

```text
3aff1c6edf6f189de6fa56c690631c266364a3b129408eb0fd5a200ceb186925 sharp_symmetry_bounds.tex
8b1f71e7a4f5dbce7fce3de383b675411e3fbba21bea4939609991f47a10ffd1 sharp_symmetry_bounds.pdf
```

Package 3 is complete; Sprint 3 and Palomar readiness are not. Next is package
4: the full Euclidean-group identification, including the low-degree case.
