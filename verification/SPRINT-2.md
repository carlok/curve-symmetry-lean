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

The projective-chart-map checkpoint adds `ProjectiveChartMaps.lean`. Its maps
use the standard classes `[z:1]` and `[1:z]` in Mathlib's projectivization.
The identity `[1:z] = [1/z:1]` is proved with `z ≠ 0`; it yields the three
affine-overlap formulas in precisely the coordinate orders of the preceding
chart closure statements. Four membership equivalences identify the pulled-back
projective curve with the checked chart equations. The three chart origins
are exactly `(∞,0)`, `(0,∞)`, and `(∞,∞)`. No topology is installed by these
definitions, and no continuity, open embedding, or gluing is asserted.

On 2026-09-10 the new module and aggregate passed warnings-as-errors, and the
full imported namespace audit passed for 789 declarations with only the three
permitted axioms. This was an incremental local build. Preflight passed for
51 files and nine exact dependency pins; six package tests and
`git diff --check` passed. The TeX and PDF migration hashes are unchanged.
The preceding `7daaeab` private Linux run was still in progress when checked;
no Linux success for either that snapshot or this new checkpoint is claimed.

Next bounded target: chart injectivity and coverage of the product of
projective lines. G01 remains incomplete.

The chart-cover checkpoint extends `ProjectiveChartMaps.lean` without adding
a module. Both projective-line chart maps and all four product chart maps are
injective. `projectiveLine_chart_cover` and `projectiveChart_cover` give actual
coordinate witnesses for every point. The second mixed chart retains its
ordered coordinates `(1/Y,X)`. These are set-theoretic statements only; the
cover is not declared open, and no embedding or gluing theorem is assumed.

On 2026-09-10 the changed module and aggregate passed warnings-as-errors;
the full imported namespace audit passed for 797 declarations with the three
permitted axioms. This was an incremental local build. Preflight passed for
51 files and nine dependency pins; six package tests and `git diff --check`
passed. No TeX/PDF changes were made. The preceding `ac1ed5c` Linux run was
still in progress when checked; this checkpoint's Linux verification is
pending. Next: exact chart ranges as coordinate-divisor complements. G01
remains incomplete, as do all later unfinished sprint gates.

The exact-range checkpoint extends `ProjectiveChartMaps.lean`. The affine
line chart omits precisely infinity and the reciprocal line chart omits
precisely zero. Accordingly the four product charts omit, respectively,
the coordinate divisors `(∞,∞)`, `(0,∞)`, `(∞,0)`, and `(0,0)`, where each
entry specifies the excluded value in that factor, not a single excluded
point. Both inclusions of each range description are proved with coordinate
witnesses. These statements do not yet prove the ranges open in a projective
Zariski topology.

On 2026-09-10 the changed module and aggregate passed warnings-as-errors;
all 804 imported namespace declarations passed the three-axiom allowlist.
This was an incremental local build. Preflight passed for 51 files and nine
pins, six package tests passed, and `git diff --check` passed. TeX/PDF were
not edited. The preceding `bd13e8f51b6e1f251b1718e8e85c5364498dcc19` checkpoint
passed private Linux CI
([run 34436170752](https://github.com/carlok/curve-symmetry-lean/actions/runs/34436170752));
the new checkpoint's Linux result is pending. Next: the affine Zariski topology
on complex evaluation points and coordinate-divisor open subsets, before
transition continuity and projective gluing. G01 remains incomplete.

The affine-topology checkpoint adds `AffineZariskiTopology.lean`. The topology
on complex coordinate points is induced by evaluation into Mathlib's prime
spectrum, with an instance local to the module's theorem section. Evaluation
is proved injective and a topological embedding. Polynomial nonvanishing sets
are open, polynomial zero sets closed, and both coordinate-deletion domains
are open. Most importantly, `affineZariski_closure` identifies closure with
the common zeros of the full vanishing ideal. The earlier real-diagonal
spectral density theorem is transferred to actual complex coordinate points.
No ambient Euclidean instance is changed and no projective topology is yet
constructed. Next: continuity of inversion transitions on their nonzero domains.

The preceding `c900075b57488244db527fd31003980e9c5a4180` checkpoint passed
private Linux CI
([run 34437842010](https://github.com/carlok/curve-symmetry-lean/actions/runs/34437842010)).
On 2026-09-10 the new module and aggregate passed warnings-as-errors, and all
815 imported namespace declarations passed the three-axiom allowlist. This
was an incremental local build with existing dependencies. Preflight passed
for 52 files and nine pins, six package tests and `git diff --check` passed,
and the TeX/PDF migration hashes remain unchanged. This checkpoint's private
Linux CI result is pending; these checks are not a Palomar dry run.
G01 and the later sprint gates remain incomplete.

The polynomial-map checkpoint resumes after rollback `1398e34`, without
restoring `InversionDenominators` or `InversionContinuity`. It adds
`PolynomialZariskiMaps.lean`: evaluating after a polynomial coordinate map
equals polynomial substitution, and inverse images of Zariski closed sets
are closed. The local Zariski topology instance remains explicit.
On 2026-09-12 the new module and aggregate compiled with warnings-as-errors;
820 namespace declarations passed the three-axiom audit. This was an
incremental local build. Preflight passed for 53 files and nine pins; six
tests and `git diff --check` passed. Baseline `1398e34951f77a8a54d29fbfdbbb1950608b5a21`
passed private Linux CI
([run 34494270359](https://github.com/carlok/curve-symmetry-lean/actions/runs/34494270359)).
New checkpoint CI is pending; no Palomar dry run is claimed.

The coordinate-exchange checkpoint adds `CoordinateExchange.lean`, building
on `1f49d05`. Coordinate swap is a Zariski homeomorphism of the plane and of
the open subset where both coordinates are nonzero. It commutes with factor
exchange in the affine and reciprocal projective charts; the second mixed
chart already accounts for the reversed coordinate order. This does not
restore the reverted inversion results or establish projective open embeddings.

On 2026-09-12 the new module and aggregate passed warnings-as-errors; 837
namespace declarations passed the three-axiom audit. Incremental local builds
only; preflight passed for 54 files and nine pins, all six tests passed, and
`git diff --check` passed. Original TeX/PDF hashes are unchanged. The existing
user-saved `ONBOARDING.md` is updated and included with this checkpoint.
Both new checkpoints' private Linux results are pending. Next: resolve the
rollback decision before proceeding with inverse-coordinate transitions;
global projective topology/gluing and G01 remain incomplete.

The approved inversion-restoration checkpoint reinstates the proof files
from `128b416` and `ee55b46` without reverting the later polynomial-map or
coordinate-exchange work. The user explicitly approved this restoration after
being asked. These are restored results, not new mathematical discoveries:
polynomial denominator clearing and a Zariski homeomorphism for inversion of
either coordinate on its nonzero domain. The old rollback warning is superseded
in `ONBOARDING.md`; no further restoration decision is outstanding.

On 2026-09-12 both restored modules were freshly compiled with warnings-as-errors,
followed by the aggregate and full namespace audit. All 857 declarations passed
the three-axiom allowlist. This was an incremental local build with existing
dependencies, not a fresh full rebuild. Preflight passed for 56 files and nine
pins; six tests and `git diff --check` passed. TeX/PDF migration hashes are
unchanged. Previous `55b9733` Linux run 34701500285 was in progress when checked;
no Linux success is asserted for it or this checkpoint. Next: simultaneous
inversion on the two-coordinate nonzero domain and the reciprocal-chart
interface. Projective topology/gluing, G01, and the later gates remain open.

The simultaneous-inversion/gluing checkpoint adds two modules:

- `SimultaneousInversion`: restrict both individual inversions to the torus,
  compose them into an involutive Zariski homeomorphism, and identify its exact
  vector formula, reciprocal-chart transition, and curve-equation equivalence.
- `ProjectiveClosureGluing`: prove that any set closed in all four affine
  charts and containing the affine curve contains the whole projective family.
  All four chart-density results are used. The family itself is chartwise
  closed. For any ambient topology satisfying chart continuity and closedness
  of the family, its affine complex-point closure is consequently the entire
  family. This ambient theorem is explicitly conditional, not a discharge of
  the standard projective topology interface.

On 2026-09-12 both modules and the aggregate passed warnings-as-errors; all
879 namespace declarations passed the three-axiom audit. This was an incremental
local build. Preflight passed for 58 files and nine pins; six tests and
`git diff --check` passed. TeX/PDF migration hashes are unchanged. The preceding
`3164274` Linux run 34701698303 was in progress when checked; new checkpoint
CI is pending. `ONBOARDING.md` documents the exact conditional boundary.

A targeted installed-source search found the projective-spectrum topology,
but no ready-made Zariski topology on the current product of Projectivization
point types. Supplying and justifying that standard topology, with the required
chart continuity/closedness (and ordinary chart compatibility), remains the
next obligation. No special topology has been chosen to force the conclusion;
G01, the rest of the full port, and the Palomar dry run remain incomplete.

The Linux runner reported an action-runtime deprecation warning for the pinned
checkout action; this did not invalidate the successful Lean build. No
Comparator, independent checker, proof sandbox, or editorial review has yet
been run. The TeX has not been changed.

## Chart-final topology and real-diagonal closure checkpoint

Two bounded steps, recorded together in the commit adding
`ProjectiveAtlasTopology.lean` and `ProjectiveAtlasClosure.lean`:

1. Construct the surjective four-chart atlas map and its coinduced topology.
   Prove every chart continuous and closedness equivalent to closed chart
   preimages. This construction contains no family equation or parameter.
2. Prove closedness of the projective family and its exact complex-affine
   closure for every positive m. For nonreal parameters, prove the stronger
   real-diagonal closure theorem using affine irreducibility and density.

Both new modules and the aggregate compiled with warnings as errors, reusing
the installed dependencies. The first step's audit passed 889 declarations;
the combined audit passed 894, using only `propext`, `Classical.choice`, and
`Quot.sound`. Preflight passed for 60 files and nine exact dependency revisions;
all six preflight tests passed. This is an incremental local check, not a
fresh whole-library rebuild or Palomar verification.

The previous checkpoint `9fb9136` passed private Linux run `34702115711`;
restoration checkpoint `3164274` also passed (`34701698303`). This new
checkpoint's Linux result is pending at commit time.

The topology is explicitly the chart-final topology. The remaining G01 gate
is to prove chart open embeddings and justify its identification with standard
projective Zariski geometry. No topology identification, completed G01, genus
theorem, or Palomar readiness is claimed. TeX and PDF remain untouched.

## Open atlas and affine embedding checkpoint

Three bounded steps are recorded together in the commit adding
`ProjectiveAtlasOpenCover.lean` and `ProjectiveAffineEmbedding.lean`:

1. Prove the exact affine-chart overlap domains: the whole plane, the first
   coordinate nonzero domain (for either mixed chart), and the two-coordinate
   torus. The second mixed chart retains its `(1/Y,X)` coordinate order.
2. Check all sixteen chart-range preimages and prove the four chart ranges
   constitute an open cover in the chart-final topology.
3. Prove the affine chart is an open map by pulling its open images back into
   all four charts. The inversion, exchanged inversion, and simultaneous
   inversion transitions are continuous on their proved open domains. Together
   with injectivity and continuity, this proves an actual open embedding.

Both new modules and the aggregate compiled with warnings as errors. The full
namespace audit passed for 922 declarations, allowing only `propext`,
`Classical.choice`, and `Quot.sound`. Preflight passed for 62 files and nine
exact dependency pins; all six preflight tests passed. `git diff --check`
passed, and TeX/PDF hashes remain unchanged. This was an incremental local
check using installed dependencies, not a fresh whole-library rebuild.

The preceding commit `6ee646d` passed private Linux run `34718581834`. The new
checkpoint's Linux result is pending at commit time. No Palomar verification
or independent checker has run.

Remaining G01 obligations: open embeddings for the two mixed charts and the
reciprocal chart, then the standard projective Zariski-topology identification.
An open range is not itself an embedding. The affine embedding is now proved
and should not be repeated as a future milestone. G01 stays incomplete.
