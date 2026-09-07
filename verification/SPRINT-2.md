# Sprint 2 checkpoints — incomplete

These are ordinary Lean build and axiom-audit results, not a Palomar dry run.
The chart compatibility of the global differential condition, its singular-pair
classification, and the resulting arbitrary Möbius completeness theorem remain
open.

| Source revision | Private Linux run | Result |
|---|---|---|
| `15906b4a810bcfecb9ec1d6843020b2b05095a60` | [34048432572](https://github.com/carlok/curve-symmetry-lean/actions/runs/34048432572) | Success |
| `20d30663821b13484d4a6ca89cde4ea3520d32ed` | [34049153247](https://github.com/carlok/curve-symmetry-lean/actions/runs/34049153247) | Success |
| `26c1f1fbc153f330f3a8ff2624ccc79bd63f948f` | [34085192057](https://github.com/carlok/curve-symmetry-lean/actions/runs/34085192057) | Success |

The first checkpoint added the actual spherical closure, standard projective
action, bihomogeneous family, conditional pair-stabilizer classification, and
divisibility of arbitrary Möbius pullbacks. The second established the separate
degree bounds and nonzero scalar pullback identity. Their complete local audits
covered 611 and 631 declarations respectively, with only `propext`,
`Classical.choice`, and `Quot.sound`.

The global-transport checkpoint adds homogeneous identities at every boundary
point, equivalence of the constructed complex zero loci in both orientations,
and the consequence that one-sided spherical containment is exact equivalence.
Its full local build on 2026-09-07 passed warnings-as-errors for all 40 files and
audited 651 declarations with the same allowlist. Its private Linux run passed
as recorded above.

The next checkpoint adds `HomogeneousDifferential.lean`: vanishing of the
function and its differential, using `HasFDerivAt` rather than a totalized
derivative; invariance under invertible coordinates and nonzero scalar
multiplication; independence from projective representatives; and transport
under both orientations of actual spherical inclusion. The complete local
41-file build passed warnings-as-errors on 2026-09-07; all 672 declarations
passed the permitted-axiom audit. All six package tests and `git diff --check`
passed. Linux verification of this checkpoint is pending its commit and push.
The paper source and PDF retain their migration-checkpoint SHA256 hashes.

The Linux runner reported an action-runtime deprecation warning for the pinned
checkout action; this did not invalidate the successful Lean build. No
Comparator, independent checker, proof sandbox, or editorial review has yet
been run. The TeX has not been changed.
