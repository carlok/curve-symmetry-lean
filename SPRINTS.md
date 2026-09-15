# Complete Lean port and private Palomar readiness

Agreed roadmap, 2026-09-06. Local folder: `curve_symmetry`; private GitHub
repository: `carlok/curve-symmetry-lean`; license: Apache-2.0.

The objective is the complete mathematical paper, not a submission limited to
Theorem 1. A missing foundation remains an explicit obligation; it is never
replaced by an axiom, convenient surrogate definition, or concealed hypothesis.
The TeX remains unchanged until the private dry run passes. Nothing authorizes
public visibility, Palomar intake, registration, or external expert outreach.

## Status ledger

| Sprint | Status | Completion evidence / commit |
|---|---|---|
| 0: relocation and private Git | Complete | `74e0e1228dc01aa1c8965b6818cf05f4e13750e7`; 81 migrated file hashes match, 33 modules / 85 axiom reports pass; remote verified private and pushed |
| 1: reproducible package and statement inventory | Complete | `459e644bb4919c2e71841e7ba62a8d6418c24d38`; [Linux run 34046925427](https://github.com/carlok/curve-symmetry-lean/actions/runs/34046925427) passed; 34 files / 532 declarations audited; [report](verification/SPRINT-1.md) and [coverage ledger](COVERAGE.md) |
| 2: global geometry and Möbius completeness | Complete at the classical complex-point atlas scope | Arbitrary ambient completeness, uniquely characterized Zariski atlas, projective closure and global irreducibility checked; 960 declarations audited; [checkpoint evidence](verification/SPRINT-2.md). Commit `d29fd22` passed Linux run `34749984410`. |
| 3: complete ambient symmetry theorem | In progress | Basic family geometry (T2.1), actual sphere coefficient tests/no anti-map (T2.3–T2.4), and both parameter equivalences (T2.7) proved. Exact group/count and full Euclidean identification still open. [Evidence](verification/SPRINT-3.md). |
| 4: genus and remaining mathematical claims | Not started | Foundational interface still missing |
| 5: Palomar contract and editorial preparation | Not started | Requires complete mathematical coverage |
| 6: private contract-faithful Linux dry run | Not started | Requires frozen contract and full proofs |
| 7: TeX integration and final snapshot | Not started | Requires successful dry run |

Starting checkpoint: 33 Lean modules and 85 axiom reports. Every clause of
Theorem 1 is checked, using real Cartesian polynomials and actual isometry
groups. Theorem 2 is incomplete. See `lean/README.md` for the precise boundary.

## Sprint 0 — relocation and private version control

Record a successful baseline build and content hashes; move the whole folder
from `transcendental/curve_symmetry` to the sibling Lean workspace without
overwriting a destination. Verify hashes and reproduce the build. Initialize
independent Git history, add Apache-2.0 and artifact exclusions, then create and
verify a private remote before pushing. Preserve unrelated source-repository
state. Work on `codex/sprint-*` branches and record scoped completion commits.

Gate: identical migrated contents, successful relocated build, private pushed
source snapshot, and no bundled library/toolchain copies.

## Sprint 1 — reproducible package and statement inventory

Use one root TOML Lakefile, a committed toolchain and exact manifest, retaining
the existing Lean source directory and declaration names. Pin Lean 4.32.0 and
Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`. Preserve the local command
that reads an existing compiled dependency installation; add private Linux
build CI for portable clean-checkout testing.

Inventory theorems, supporting lemmas, substantive mathematical remarks, and
proof claims needed to explain their scope. Map each to declarations or an
explicit obligation. Use ordinary Cartesian curves, genuine ambient actions,
spherical closure, geometric irreducibility, and genuine geometric genus.

Gate: portable configuration, full coverage ledger, and no runtime dependence
on the former project location.

## Sprint 2 — global geometry and Möbius completeness

Use standard projective-line coordinates and invertible-linear-map actions,
with a proved finite-chart/infinity interface. Construct the bihomogeneous
family in `P¹ × P¹`; connect the checked Jacobian and tangent-cone data to that
curve. Lift equivalences of spherical real loci to the complexification and
derive singular-pair preservation and the four possible map forms.

Gate: completeness for arbitrary Möbius/anti-Möbius equivalences, with neither
pair preservation nor the four-form reduction assumed.

The mixed corner now belongs to the Zariski closure of actual complex points
with nonzero first coordinate in its affine chart (`MixedCornerClosure`).
This is a chart-level theorem, not yet a projective closure identification.
The reciprocal chart at `(∞,∞)` now has the corresponding density theorem
with both axes deleted (`ReciprocalCornerClosure`). `OtherMixedCornerClosure`
transfers original affine points by `(X,Y) ↦ (1/Y,X)` and proves their chart
closure contains the corner `(0,∞)`. `AffineChartImages` supplies the matching
original-affine-point image and closure identities for the first mixed and
reciprocal charts. `ProjectiveChartMaps` constructs the four standard homogeneous
chart maps, their affine-overlap identities, curve-equation interfaces, and
boundary-origin identities. All four maps are now proved injective, and their
ranges cover the product of projective lines. Their ranges are now identified
exactly as complements of the relevant zero/infinity coordinate divisors.
`AffineZariskiTopology` now provides the induced complex-point topology, its
embedding into the prime spectrum, polynomial nonvanishing opens, and the
usual algebraic closure formula. It does not install a global instance on
coordinate vectors. `PolynomialZariskiMaps` now proves polynomial substitution
and Zariski continuity of arbitrary polynomial coordinate maps. `CoordinateExchange` proves the swap is a Zariski
homeomorphism of the plane and the two-coordinate nonzero domain, and connects
it to factor exchange in the projective charts. With explicit user approval,
`InversionDenominators` and `InversionContinuity` are restored: either coordinate
inversion is a Zariski homeomorphism of its nonzero-coordinate domain.
`SimultaneousInversion` now proves the two-coordinate torus homeomorphism and
the exact reciprocal-chart and curve-equation interfaces. `ProjectiveClosureGluing`
combines the chart density results: any chartwise closed set containing the
affine curve contains the full projective family. It also proves ambient
closure conditionally on chart continuity and closedness of the family.
`ProjectiveAtlasTopology` now constructs the family-independent chart-final
topology and discharges chart continuity. `ProjectiveAtlasClosure` proves
complex-affine and real-diagonal closure in it. `ProjectiveAtlasOpenCover` proves
the four chart ranges open and covering. `ProjectiveAffineEmbedding` proves the
affine chart is an open embedding. `ProjectiveAtlasEmbeddings` now transports
this result to the other three charts using explicit projective homeomorphisms.
All four chart open embeddings are proved. `ProjectiveAtlasUniqueness` now
characterizes the topology uniquely by this standard affine atlas, completing
the classical point-level G01 closure interpretation. `ProjectiveCurveIrreducibility`
proves global irreducibility. Next: Sprint 3's exact sphere-action coefficient
filters and full ambient group. Do not extend the completed chart programme
into an unnecessary scheme comparison; normalization and genus remain Sprint 4.

## Sprint 3 — complete the ambient symmetry theorem

2026-09-14 COMPLETE. Package 6, `family_arc_equivalence_iff`, closes R02.
Gate audit: T2.1–T2.7 and the Sprint 3 consequences G13/R02/R03 are proved
for actual transformations, including zero/infinity and m=2. G01's
classical complex-point scope is unchanged. Normalization/genus obligations
remain in Sprint 4 and are not certified by this completion.
Completion commit: the commit introducing `verification/arc-and-circle-completion.md`.
Both new modules and aggregate passed warnings-as-errors compilation;
whole-namespace audit passed (1,125), preflight and six package tests passed.

2026-09-14 packages 4 and 5 COMPLETE: actual Euclidean self-isometries are
exactly centered root rotations, with full group order 2m (including m=2);
every ambient symmetry for algebraic normalized alpha has an algebraic-entry
matrix representative. Coverage T2.6, G13, R03 is closed. Incremental module
and aggregate checks with warnings as errors, all-namespace audit (1,096),
preflight and six package tests passed. The completion commit introduces
`verification/packages-4-5-completion.md`. Package 6 remains before closing
Sprint 3; no genus or Palomar readiness claim follows.

2026-09-14 package 4 first part: `FamilyEuclidean` proves the affine-to-sphere
interface, exclusion of conjugate-affine self-inclusions, absence of opposite
symmetries including m=2, and directness of every actual Euclidean self-isometry.
Normalized nonreal parameters are required. Translation elimination, exact
rotations, and the full actual group count remain. Module and aggregate build
passed with warnings as errors; the full audit passed for 1,085 declarations;
preflight and six package tests passed. Evidence:
`verification/package-4-first-part.md`; its introducing commit is the checkpoint.

2026-09-14 package 3 COMPLETE: `FamilyDihedral` proves the isomorphism of the
actual ambient sphere group with `DihedralGroup (2*m)`, order `4m`, and
generators/relations/exhaustion. This includes `m=2`; T2.4 already excludes
anti-Möbius additions. Four explicit composition laws handle zero and infinity.
The completion commit is the commit adding
`verification/package-3-completion.md`. Local module/aggregate compilation
with warnings as errors, full namespace audit (1,075 declarations), preflight
and six tests passed. Full Sprint 3 is not complete: T2.6 and the remaining
algebraic-coefficient/parameter-family consequences remain.

2026-09-14 package 3 checkpoint: `FamilyAmbientGroup` defines actual sphere
symmetries independently of the normal forms. Completeness gives the two
root-constrained families; parameters are injective and the families disjoint.
Incremental warnings-as-errors build, aggregate compilation, all-namespace
axiom audit (1,021 declarations), preflight, and six package tests passed.
Package 3 remains incomplete: dihedral multiplication/isomorphism and order
`4m` are not yet proved. See `verification/ambient-group-checkpoint.md`.

Combine completeness with the exact coefficient filters. Prove the sphere
actions at zero and infinity, the dihedral group of order `4m`, exactly `2m`
Euclidean rotations, no anti-Möbius self-equivalence, and both complete
parameter-equivalence criteria. Include the algebraic-coefficient consequence,
the `m=2` case, and the stated exclusions.

Gate: all clauses of Theorem 2 on actual ambient transformations, not just
denominator-cleared polynomial identities.

## Sprint 4 — genus and remaining paper claims

2026-09-15 two bounded packages COMPLETE: projective tangent-direction count
and the explicit quintic calculation. BinaryTangentDirections proves that the
homogeneous zero condition is independent of representatives and has exactly
m points in the actual projective line. This advances G06 but does not close
its multiplicity/ordinary-point obligation. QuinticExample closes S10's
displayed formula, sign change, and exact order of the specified actual
Euclidean rotation. Both modules and aggregate passed warnings-as-errors
compilation; namespace audit 1,149; preflight 77 modules/nine pins; six tests.
Completion commit introduces `verification/tangents-and-quintic.md`.

2026-09-14 first package COMPLETE: G10's exact centered-circle section.
`familyCircleRootEquiv` gives a free transitive root-rotation parametrization,
and `family_metric_circle_card` gives exactly 2m actual points. This holds for
all m>0 and nonreal alpha, without parameter normalization. Sprint 4 itself
remains incomplete, especially G06–G09 and R01.

Construct normalization and the double cover with its ramification data.
Prove the required Riemann–Hurwitz machinery and actual genus `m`. Complete
bidegree, ordinary-point assertions, the quartic genus comparison, and all
remaining substantive claims in the coverage ledger.

Gate: the entire mathematical port is hole-free. A numerical branch-count
identity is not a geometric-genus theorem. This is the highest-risk sprint:
the installed Mathlib search did not locate a ready-made interface. Missing
foundations must be proved. No calendar estimate is promised.

## Sprint 5 — Palomar contract and editorial preparation

Create one compact Challenge/Solution pair and Comparator configuration for
the principal claims. Challenge imports only the permitted Mathlib closure;
statement definitions have explicit ordinary meanings and no definition holes.
Only the isolated statement-only Challenge may contain deliberate theorem
placeholders. The proof library and Solution must never depend on them.

Prepare valid metadata for sources, license, authorship, AI assistance, scope,
fidelity, and actual review status. Audit research positioning and preserve the
arXiv-versus-uninspected-journal qualification. Pin verifier, Comparator,
exporter, and independent checker revisions. No fabricated model provenance,
human review, novelty certificate, or Palomar ID.

Gate: accurate independently readable statements and passing static contract
checks. Policy: https://palomar-registry.org/how-to-submit and
https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md .

## Sprint 6 — private contract-faithful dry run

Use an immutable commit and clean private Linux GitHub Actions checkout.
Validate dependencies; compile Challenge in isolation; protect the comparison
configuration; run real sandboxed Comparator and NanoDa replay without network
access or credentials in the proof sandbox. Require disposable negative
controls for a changed theorem type, forbidden axiom, and forbidden Challenge
import to fail. Record exact revisions and distinguish mechanical evidence
from editorial self-review and anything not tested.

Gate: positive case passes and negative controls fail. No fake sandbox or
skipped checker qualifies. This is private CI, not Palomar intake. Ordinary
GitHub Actions usage was approved; repository publication was not.

## Sprint 7 — TeX integration and final snapshot

Only after Sprint 6, refactor the existing note without bloating its mathematical
exposition. Add a short formalization section/appendix with theorem-to-Lean
links, reproduction instructions, dependencies, exact scope, AI disclosure,
and the distinction between kernel checks, dry runs, novelty, and human review.
Do not imply registration. Rebuild, run ChkTeX, inspect the PDF, and rerun
verification against the final committed snapshot.

Gate: paper, formal statements, metadata, and verification evidence agree at
one private release-candidate commit.

## Completion discipline

Record each sprint's checks and completion commit here. The permitted proof
axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`. No proof
holes, `native_decide`, custom axioms, or hidden theorem assumptions may be
used to close a sprint. Palomar-ready is a reproducible, honestly described
candidate—not guaranteed editorial approval or registry acceptance.
