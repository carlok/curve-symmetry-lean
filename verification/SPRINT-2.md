# Sprint 2 checkpoints — incomplete

These are ordinary Lean build and axiom-audit results, not a Palomar dry run.
The chart compatibility, exact global Jacobian locus, and arbitrary Möbius
completeness are now proved. G01's Zariski-closure identification remains open;
the complete ambient symmetry group, parameter filters on sphere actions, and
genus belong to the later, still incomplete sprints.

| Source revision | Private Linux run | Result |
|---|---|---|
| `15906b4a810bcfecb9ec1d6843020b2b05095a60` | [34048432572](https://github.com/carlok/curve-symmetry-lean/actions/runs/34048432572) | Success |
| `20d30663821b13484d4a6ca89cde4ea3520d32ed` | [34049153247](https://github.com/carlok/curve-symmetry-lean/actions/runs/34049153247) | Success |
| `26c1f1fbc153f330f3a8ff2624ccc79bd63f948f` | [34085192057](https://github.com/carlok/curve-symmetry-lean/actions/runs/34085192057) | Success |
| `35573d31255a8d4b202679c19239a9b10ce10b95` | [34086041192](https://github.com/carlok/curve-symmetry-lean/actions/runs/34086041192) | Success |

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
passed. Linux verification passed at the revision recorded above.
The paper source and PDF retain their migration-checkpoint SHA256 hashes.

The completeness checkpoint adds three modules:

- `PolynomialDifferential`: formal partial derivatives give the true
  differential; the earlier Jacobian predicate has precisely this meaning.
- `HomogeneousCharts`: dehomogenization preserves critical zeros in both
  directions, proved using local nonzero denominators and the product rule.
- `FamilyGlobalSingularities`: the global Jacobian locus is exactly the two
  diagonal points; its transport derives pair preservation and then the two
  holomorphic and two antiholomorphic map forms on every sphere point.

The new endpoints require `m ≥ 2` and nonreal parameters. They need neither
unit-modulus normalization nor an assumed matrix shape. Their selected axiom
reports pass. The complete 44-file build passed warnings-as-errors on
2026-09-07; all 722 declarations passed the permitted-axiom audit. All six
package tests and `git diff --check` pass. Linux verification of this checkpoint
will follow its scoped commit. The TeX and PDF hashes remain unchanged.

The Linux runner reported an action-runtime deprecation warning for the pinned
checkout action; this did not invalidate the successful Lean build. No
Comparator, independent checker, proof sandbox, or editorial review has yet
been run. The TeX has not been changed.
