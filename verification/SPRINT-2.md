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

The reciprocal-corner checkpoint adds `ReciprocalCornerClosure.lean` and
generalizes the previous deleted-axis lemma to a divisor containing no
irreducible component of the equation. Neither coordinate divides the
reciprocal equation: evaluation at `(0,1)` and `(1,0)` gives `1`. Primality of
irreducible factors therefore permits deleting the product of both coordinates.
The complex-point density theorem places `(0,0)` of the reciprocal chart in
the Zariski closure of its complex points with both coordinates nonzero.
This holds for every `m > 0` and every complex parameter, without smoothness
or irreducibility assumptions on the curve. Projective gluing is not claimed.

The changed mixed module, new reciprocal module, and aggregate passed
warnings-as-errors on 2026-09-08. The full imported namespace audit passed for
755 declarations with the three permitted axioms. This was an incremental
local build, not a full rebuild. Preflight passed for 48 files and nine exact
dependency pins; six package tests and `git diff --check` passed. The TeX and
PDF retain their migration hashes. Linux CI for the preceding mixed checkpoint
was still running when checked; no new Linux success is asserted here.
Next bounded target: the other mixed corner's explicit factor-exchange chart.
G01 remains partial and all later sprint gates remain unchanged.

The other-mixed-corner checkpoint adds `OtherMixedCornerClosure.lean`.
`other_mixed_zero_iff` proves the chart-equation equivalence with its nonzero
denominator condition. `other_mixed_affine_points_image` proves that original
affine points with `Y ≠ 0`, mapped by `(X,Y) ↦ (1/Y,X)`, are exactly the
punctured second mixed chart. The two closure endpoints use this explicit
image identity, so their source sets are original affine curve points.
The chart origin representing `(0,∞)` belongs to their affine spectral closure
for every `m > 0` and every complex parameter. Global projective gluing is
still not claimed.

The new module and aggregate passed warnings-as-errors on 2026-09-08; the full
imported namespace audit passed for 759 declarations with the three permitted
axioms. This was an incremental local build. Preflight passed for 49 files
and nine dependency pins; all six package tests and `git diff --check` passed.
TeX and PDF hashes are unchanged. The preceding reciprocal checkpoint
`e19539989f7fbfc9d1be4da6a5c8bc7d4a69d29f` passed private Linux CI
([run 34224646788](https://github.com/carlok/curve-symmetry-lean/actions/runs/34224646788));
the superseded mixed-only run was cancelled. CI of the present checkpoint
is pending. Next: the analogous original-affine-point image identities for
the first mixed and reciprocal charts. Projective topology/gluing and G01
remain open; ordinary CI is not a Palomar dry run.

The original-point chart checkpoint adds `AffineChartImages.lean`. It proves
exact image identities for `(X,Y) ↦ (1/X,Y)` on `X ≠ 0` and
`(X,Y) ↦ (1/X,1/Y)` off both axes. The inverse constructions and nonzero
denominator conditions are explicit. Combining these identities with the
existing density theorems gives the full affine spectral closure of original
curve points in each chart, for every `m > 0` and every complex parameter.
Together with the preceding second mixed chart, all three boundary charts
now have original-affine-point closure descriptions. This does not construct
the global projective Zariski topology or prove chart gluing.

The preceding checkpoint `c1c7d08bee8d3d2a07857836c6e547a2ec37f5d9` passed
private Linux CI
([run 34276610791](https://github.com/carlok/curve-symmetry-lean/actions/runs/34276610791)).
On 2026-09-10 the new module and aggregate passed warnings-as-errors, and the
full imported namespace audit passed for 767 declarations with only the three
permitted axioms. This was an incremental local build using existing compiled
dependencies, not a fresh full rebuild. Preflight passed for 50 files and nine
exact dependency pins; six package tests and `git diff --check` passed. TeX
and PDF migration hashes are unchanged. This checkpoint's Linux CI is pending.
Next bounded target: common projective chart maps and their affine-overlap
identities. G01 and the later sprint gates remain incomplete.

The Linux runner reported an action-runtime deprecation warning for the pinned
checkout action; this did not invalidate the successful Lean build. No
Comparator, independent checker, proof sandbox, or editorial review has yet
been run. The TeX has not been changed.
