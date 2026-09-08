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
| `b1869904449847c603ffb774ed17721b711b38cb` | [34156010492](https://github.com/carlok/curve-symmetry-lean/actions/runs/34156010492) | Success |

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
package tests and `git diff --check` pass. Linux verification passed at the
revision recorded above. The TeX and PDF hashes remain unchanged.

The affine-closure checkpoint adds `AffineClosure.lean`, using Mathlib's
`MvPolynomial.vanishingIdeal`, `PrimeSpectrum`, and its existing Zariski
topology. It proves the exact principal vanishing ideal, its complex-point
zero locus, and the actual affine spectral closure. All selected endpoints
pass the permitted-axiom audit. The full 45-file build passed warnings-as-errors
on 2026-09-08; all 732 declarations passed the axiom allowlist. The six package
tests and `git diff --check` pass; TeX and PDF hashes remain unchanged. Private
Linux verification will follow this checkpoint's commit. Projective
boundary closure is explicitly still open; no topology or closure definition
has been chosen to make that missing assertion tautological.

The short boundary checkpoint adds `ProjectiveBoundary.lean`: the complement
of the standard affine chart on the constructed curve consists exactly of
`(∞,0)`, `(0,∞)`, and `(∞,∞)`. The new module and aggregate compile with
warnings-as-errors; the full imported namespace audit passes for 738
declarations. The source/dependency preflight passes for 46 files and all nine
pins. This was an incremental local build, not a fresh rebuild of every file.
The boundary decomposition itself does not discharge any closure-membership
assertion. The private Linux build of this checkpoint passed at
`308f03641a258d5e21e25b5b39c54605f6aa2057`
([run 34187407886](https://github.com/carlok/curve-symmetry-lean/actions/runs/34187407886)).
The preceding affine-only run was cancelled when superseded; the successful
boundary snapshot includes that module too.

The mixed-corner checkpoint adds `MixedCornerClosure.lean`. Deleting an
irreducible divisor not dividing a hypersurface equation preserves its Zariski
closure, proved component by component using generic points. Mathlib's
Nullstellensatz and Jacobson-space theorem then give the same closure using
actual complex evaluation points. Applied to the mixed chart, this places its
origin in the closure of points with nonzero first coordinate, for every
`m > 0` and arbitrary complex coefficients. This is not yet projective gluing.

On 2026-09-08 the new module and aggregate passed warnings-as-errors, and the
full imported namespace audit passed for 749 declarations with only `propext`,
`Classical.choice`, and `Quot.sound`. This was an incremental local build using
existing dependencies, not a fresh full rebuild. Source preflight passed for
47 files and nine exact dependency pins; all six package tests and
`git diff --check` passed. Linux verification of this new checkpoint is pending.
Next: the reciprocal chart at `(∞,∞)` with both axes deleted. G01 stays partial;
neither the TeX nor the Palomar contract has been changed.

The Linux runner reported an action-runtime deprecation warning for the pinned
checkout action; this did not invalidate the successful Lean build. No
Comparator, independent checker, proof sandbox, or editorial review has yet
been run. The TeX has not been changed.
