# Sprint 2 checkpoints — incomplete

These are ordinary Lean build and axiom-audit results, not a Palomar dry run.
The intrinsic singularity interface, its transport, and the resulting arbitrary
Möbius completeness theorem remain open.

| Source revision | Private Linux run | Result |
|---|---|---|
| `15906b4a810bcfecb9ec1d6843020b2b05095a60` | [34048432572](https://github.com/carlok/curve-symmetry-lean/actions/runs/34048432572) | Success |
| `20d30663821b13484d4a6ca89cde4ea3520d32ed` | [34049153247](https://github.com/carlok/curve-symmetry-lean/actions/runs/34049153247) | Success |

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
audited 651 declarations with the same allowlist. Linux evidence for this
checkpoint is to be recorded after committing and running CI.

The Linux runner reported an action-runtime deprecation warning for the pinned
checkout action; this did not invalidate the successful Lean build. No
Comparator, independent checker, proof sandbox, or editorial review has yet
been run. The TeX has not been changed.
