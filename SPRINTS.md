# Complete Lean port and private Palomar readiness

Agreed roadmap, 2026-09-06. Local folder: `curve_symmetry`; private GitHub
repository: `carlok/curve-symmetry-lean`; license: Apache-2.0.

The objective is the complete mathematical paper, not a submission limited to
Theorem 1. A missing foundation remains an explicit obligation; it is never
replaced by an axiom, convenient surrogate definition, or concealed hypothesis.
The TeX remains unchanged until the private dry run passes. Nothing authorizes
public visibility, Palomar intake, registration, or external expert outreach.
Exceptions granted since, each by the user: the separate public Theorem 1
repository and its Palomar registration (2026-09-17/18, the user's actions),
and a private email to Alcázar et al., drafted by the assistant outside this
repository and sent by the user (2026-09-28). This repository stays private.
No arXiv preprint is planned (user, 2026-09-29: no arXiv access, no novelty
claim); the Palomar registration of Theorem 1 is the public record.

## Status ledger

| Sprint | Status | Completion evidence / commit |
|---|---|---|
| 0: relocation and private Git | Complete | `74e0e1228dc01aa1c8965b6818cf05f4e13750e7`; 81 migrated file hashes match, 33 modules / 85 axiom reports pass; remote verified private and pushed |
| 1: reproducible package and statement inventory | Complete | `459e644bb4919c2e71841e7ba62a8d6418c24d38`; [Linux run 34046925427](https://github.com/carlok/curve-symmetry-lean/actions/runs/34046925427) passed; 34 files / 532 declarations audited; [report](verification/SPRINT-1.md) and [coverage ledger](COVERAGE.md) |
| 2: global geometry and Möbius completeness | Complete at the classical complex-point atlas scope | Arbitrary ambient completeness, uniquely characterized Zariski atlas, projective closure and global irreducibility checked; 960 declarations audited; [checkpoint evidence](verification/SPRINT-2.md). Commit `d29fd22` passed Linux run `34749984410`. |
| 3: complete ambient symmetry theorem | Complete | T2.1–T2.7, G13, R02 and R03 proved for actual transformations; completion commit introduces `verification/arc-and-circle-completion.md`. [Evidence](verification/SPRINT-3.md). |
| 4: genus and remaining mathematical claims | Complete (gate 2026-09-30) | S03, S04, S07, S10, G06 and G10 proved; G07a (function-field double cover), G07b-1 (integral closure) and G07b-2a/2b (Dedekind closure, points of the affine double cover), G07b-2c (places over the finite `t`-line) and G07b-3 (place over `t = ∞`, full classification) proved; G08 proved at the recorded fibre-count reading; G09 genus `m` proved at the route-B reading (`family_genus`, `c4a1857`, run 35738686055), by an explicit basis instead of the paper's Riemann–Hurwitz step (divisor identity not pursued, user decision 2026-09-28). R01 proved as printed (`paper_degree_four_genus`: genus three against two, packages R01a–R01f). Gate passed 2026-09-30 ([SPRINT-4](verification/SPRINT-4.md)), tag `sprint-4-complete`. |
| 5: Palomar contract and editorial preparation | In progress (Theorem 1 entry only) | Staged strategy, user decision 2026-09-17: first entry is Theorem 1, registered as `PALOMAR-2026-09-18-000007`; see the staged-submission section below. A Theorem 2 entry is undecided; no preprint is planned (user, 2026-09-29). |
| 6: private contract-faithful Linux dry run | Mechanical preflight and negative controls passed (Theorem 1 entry) | Palomar's own verifier, reusable workflow at PalomarSubmission@ec6064a, runs 35183549777 on public carlok/sharp-symmetry-bounds-lean@4408003 and 35184670576 on @85ddda8 (with reviewer docs): status pass, no errors or warnings; the registered commit passed Palomar's official verification (run 35351732435). Negative controls passed 2026-09-30 (run 36669665932): a changed theorem type, a forbidden axiom and a forbidden Challenge import are each rejected by their pre-check. |
| 7: TeX integration and final snapshot | Complete (2026-09-30) | Appendix A, "Formal verification": statement-to-Lean map, readings, route differences, registration scope, AI disclosure; six pages, chktex clean, verify.py passed ([SPRINT-7](verification/SPRINT-7.md)) |

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

2026-09-28 backlog decisions (user). R01 closes only when the quartic's genus
is exactly three, as Remark 5 prints; genus at least three would already
contradict genus two, but does not close the row. Order: an intrinsic genus
(places as valuation subrings, invariance under `ℂ`-algebra isomorphisms), the
family bridge, the Kummer field of `y⁴ = 2 − x⁴`, three holomorphic
differentials, the similarity-to-isomorphism step, then the Kummer places and
the upper bound. The Riemann–Hurwitz degree identity as a divisor statement is
not pursued: Lemma 4's genus claim is proved with an explicit basis, and the
route difference is recorded in COVERAGE (G09) and goes into the TeX appendix.
This is how the Sprint 4 gate reads "Riemann–Hurwitz machinery" below.

2026-09-29: R01 is closed as printed. The quartic's function field has genus
exactly three (`fermatFunctionField_genus`, R01e-3); endpoint
`paper_degree_four_genus`.

2026-09-30: Sprint 4 gate passed. All ten Sprint 4 rows were re-read against
the TeX; none is closed by a substitute invariant; the genus route (explicit
basis instead of Riemann–Hurwitz) is recorded. Record:
[SPRINT-4](verification/SPRINT-4.md); tag `sprint-4-complete`.

2026-09-22 G09 COMPLETE at the route-B reading. G09a-1 to G09a-2g: `Ω[K⁄ℂ]`
is one-dimensional over `K`, spanned by `dt`; at every place the differentials
of the local ring are generated by `du` for any uniformizer `u`, so an order is
well defined; `dt` has order `0`, `1` and `−3` at unramified, ramified and
infinite places, stated structurally. G09b-1 to G09b-3d: regularity at each
place, the holomorphic differentials as a `ℂ`-subspace, the basis
`tⁱ·dt/w` (`i < m`) and `family_genus`: dimension `m`. Namespace audit 1,679;
98 modules and nine pins; six tests. Proof snapshot `c4a1857` passed Linux run
35738686055 and the Palomar Theorem 1 entry build 35738686071. Notes:
`verification/differentials-rank.md`, `verification/place-differentials.md`,
`verification/holomorphic-differentials.md`.

2026-09-21/22 toolchain: Lean 4.34.0 and Mathlib `5ed2965` (tag `v4.34.0`),
prepared on `claude/2026-09-21-lean-v4.34.0`, reviewed against the public
repository's shared files and merged by fast-forward as `db011ac` (run
35734028877). The audit rose from 1,581 to 1,583 with no written declaration
added or removed; the statement spellings that Mathlib renames forced were
reviewed one by one before the merge.

2026-09-16 G08 COMPLETE at the recorded fibre-count reading (user decision:
branch point = fewer than two places over the point; no ramification indices).
FamilyBranchPoints proves exactly `2m+2` branch points: `∞` and the `2m+1`
distinct roots of `h_α`, including `0`. Module and aggregate passed
warnings-as-errors compilation; namespace audit 1,440; preflight 88 modules and
nine pins; six tests. Previous proof snapshot `24404dd` passed Linux run
35093882792. Completion commit introduces `verification/branch-points.md`.
User decision: next, prepare a first Palomar entry for Theorem 1 (Sprint 5
scope for that entry only); G09 and R01 are deferred, not abandoned.

2026-09-16 G07b-3 COMPLETE. QuadraticInfinity builds the ring isomorphism
`ℂ(t)[W]/(W² − h_α) ≃ ℂ(s)[W]/(W² − h_{conj α})`, `t ↦ 1/s`, and proves
`family_place_classification`: every valuation subring `O ≠ L` containing the
constants is a point place `(c,d)`, `d² = h_α(c)`, or the unique place over
`t = ∞`. G07 is now proved at the approved function-field reading. Module and
aggregate passed warnings-as-errors compilation; namespace audit 1,420;
preflight 87 modules and nine pins; six tests. Previous proof snapshot
`e209f92` passed Linux run 34945242761. Completion commit introduces
`verification/infinite-place.md`.

2026-09-15 G07b-2c COMPLETE. DedekindPlaces proves that a valuation subring
`O ≠ K` containing a Dedekind domain `A` is the localization at its nonzero
center, bijectively with nonzero primes. QuadraticPlaces makes
`ℂ[t][W]/(W² − h)` the Dedekind integral closure and proves that places
containing `ℂ[t]` are exactly the point places `(c,d)`, `d² = h(c)`, with two
over `t = c` when `h(c) ≠ 0` and one when `h(c) = 0`; the family case is
`family_finite_place_classification`. Both modules and the aggregate passed
warnings-as-errors compilation; namespace audit 1,383; preflight 86 modules
and nine pins; six tests. Previous proof snapshot `6e43f53` passed Linux run
34944104779. Completion commit introduces `verification/finite-places.md`.

2026-09-15 G07b-2a and G07b-2b COMPLETE. QuadraticDedekind makes the integral
closure of `ℂ[t]` in `ℂ(t)[W]/(W² − h)` a Dedekind domain with that fraction
field. QuadraticRing embeds `ℂ[t][W]/(W² − h)` onto it (squarefree `h`) and
proves its maximal ideals are exactly the evaluation kernels at points
`(c,d)` with `d² = h(c)`, distinct for distinct points. Both modules and the
aggregate passed warnings-as-errors compilation; namespace audit 1,343;
preflight 84 modules and nine pins; six tests. Previous proof snapshot
`9327385` passed Linux run 34943343401. Completion commit introduces
`verification/points-of-double-cover.md`.

2026-09-15 G07b-1 COMPLETE. QuadraticIntegralClosure proves that for
squarefree `h` the elements of `ℂ(t)[W]/(W² − h)` integral over `ℂ[t]` are
exactly `a + b·w` with `a, b ∈ ℂ[t]` (trace/norm argument and a squarefree
denominator lemma), and specializes it to the family. Module and aggregate
passed warnings-as-errors compilation; namespace audit 1,308; preflight 82
modules and nine pins; six tests. Previous proof snapshot `cac8e03` passed
Linux run 34940883130. Completion commit introduces
`verification/quadratic-integral-closure.md`.

2026-09-15 G07a COMPLETE. After the genus scope study (function-field genus
approved by the user), FamilyFunctionField proves that the function field of
the family curve is `ℂ(t)[W]/(W² − h)` with `t = X/Y` transcendental,
`h = −t(t^m+1)(α t^m + conj α)` squarefree of degree `2m+1`, and degree two
over `ℂ(t)`. Module and aggregate passed warnings-as-errors compilation;
namespace audit 1,286; preflight 81 modules and nine pins; six tests. Previous
proof snapshot `ba20da2` passed Linux runs 34938739018 and 34938739562.
Completion commit introduces `verification/function-field-double-cover.md`.
Work now happens on `main` only (`codex/main` until 2026-09-30); sprint completions are tagged.

2026-09-15 two packages COMPLETE: Lemma 3 sign (S03, S04) and equation (5)
(S07). IsometrySign proves `f∘T = ±f` for every actual isometry of a real
Cartesian curve, with sign `+1` and a fixed point (no glide reflection) for
every orientation-reversing symmetry. RadialAntiForm proves the
`X^m A(XY) + Y^m conj(A)(XY)` synthesis, both degree bounds, nonconstant `A`,
and the Cartesian endpoint starting from a rotation of order greater than the
degree. Both modules and aggregate passed warnings-as-errors compilation;
namespace audit 1,223; preflight 80 modules and nine pins; six tests. Previous
snapshot `2cff8af` passed Linux runs 34937614030 and 34937613937. Completion
commit introduces `verification/sign-and-radial-form.md`. Only the genus
foundations G07–G09 and the quartic comparison R01 remain in Sprint 4.

2026-09-15 ordinary multiple-point package COMPLETE, closing G06 at the
standard-chart algebraic-multiplicity scope. OrdinaryMultiplePoints defines
multiplicity by powers of the point's maximal ideal and proves that `(0,0)` and
`(∞,∞)` are ordinary `m`-fold points of their chart equations, with explicit
pairwise nonproportional linear factors of the displayed cones. Every other
zero of the four chart equations has multiplicity one. Chart-transition
invariance of multiplicity is not claimed. Module and aggregate passed
warnings-as-errors compilation; namespace audit 1,185; preflight 78 modules and
nine pins; six tests. The previous snapshot `6fb2109` passed Linux runs
34927233633 and 34927232893. Completion commit introduces
`verification/ordinary-multiple-points.md`.

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

2026-09-17 staged submission strategy (user decision). The first Palomar entry
covers Theorem 1 only (sharp bounds, sharpness, equality classification,
converse), all already proved. It lives in the nested project
`palomar/theorem1/` (Challenge, Solution, comparator.json, formalization.yaml).
Sprint 6's private contract-faithful dry run still precedes any submission.
After a review outcome: `revision_required` or alignment/metadata problems ->
fix and resubmit the corrected commit; `rejected` for research interest -> do
not expect Theorem 2 alone to pass; the user then considers going public in
stages (e.g. prove2me, then GitHub). Going public was authorized by the user on
2026-09-30. Genus work (G09, R01) was deferred then; both are proved now (2026-09-29).
Palomar limits checked 2026-09-16/17: Challenge hard limit 1,000 lines /
100 KiB, warning above 300 lines / 32 KiB; repository <= 500 MiB; several
entries may share one repository and commit via separate configuration paths.

Challenge draft 2026-09-17: `palomar/theorem1/Challenge.lean`, 90 lines,
4.7 KiB, imports only Mathlib, compiles with the five intended `sorry`
placeholders. Definitions: `realCurve`, `symmetries`, `directSymmetries`
(affine form `z ↦ az+b`, `|a| = 1`), `extremalCurve`; cyclicity stated as
"exactly the integer powers of one isometry".

2026-09-17 Solution and comparator. `palomar/theorem1/Solution.lean` copies the
four definitions verbatim and derives the five theorems from the library
endpoints (`paper_*`); `comparator.json` compares the five theorems with
`definition_names` empty and only the three permitted axioms. Nested
`lakefile.toml` requires the root package by path `../..`; `lean-toolchain` is
the root pin; `lake-manifest.json` is hand-derived from the root manifest
(path package plus inherited pinned Git packages) and awaits Lake validation in
CI. Local pre-checks (not Comparator): Solution compiles with warnings as
errors; `scripts/palomar/dump_decls.sh` shows identical elaborated theorem
types and definition types/values in Challenge and Solution; the five Solution
theorems use only propext, Classical.choice, Quot.sound. New workflow
`palomar-theorem1.yml` builds the nested project and repeats both pre-checks.
Not yet done: formalization.yaml, real Comparator/NanoDa run (Sprint 6).

2026-09-17 formalization.yaml drafted in `palomar/theorem1/` (original-proof
source = the note; Lebmeir–Richter-Gebert, Lebmeir, Pach–de Zeeuw and the
Alcázar–Lávička–Vršek arXiv v1 as background; AI agent disclosure; review
`self-assessed`, no independent human review; seven listed fidelity
divergences). Validated offline with Palomar's own loaders from
PalomarRegistry/PalomarSubmission@ec6064aea91e2f99187f3f46a2652e4d977ce755:
`submission_contract.load_formalization_metadata` and
`verify_submission.load_comparator_config` both accept the files; taxonomy
codes math.AG, math.MG, 14H50, 14P05, 51N20 exist in their snapshots. Lean
4.32.0 meets their minimum v4.28.0.

Sprint 6 blocker found 2026-09-17: Palomar's verifier (also the reusable
preflight workflow `submission.yml`, profile palomar-standard-v1: Comparator
575674928e239f5bc452aab72d1dd7b0f1326494, Landrun
811cfff51ceaf3d9843708aa6d22e9b84ccac8b4, NanoDa
68d5ca9db226849b41a6fff59d796ff19d0a8840) clones the submitted repository over
credential-free HTTPS and its input requires a public repository. A private
repository cannot be verified by the real pipeline, and a Palomar submission
itself requires a public repository. Options need a user decision: (A) make
`carlok/curve-symmetry-lean` public; (B) create a separate minimal public
repository containing only the Theorem 1 entry and the library modules in the
import closure of PaperBounds; (C) keep everything private and build/run the
pinned Comparator, Landrun and NanoDa in private CI against a local checkout,
which is a close approximation but not contract-faithful at the clone step.

2026-09-17 user decision: option B. User confirmed the metadata fields and the
Codex model name "Codex Sol". If Palomar refuses the entry, the small public
repository may be made private or deleted and work returns to this private
repository. Created PUBLIC repository `carlok/sharp-symmetry-bounds-lean`
(fresh history, commit 4408003da5abd6a6b6e3ad2643f3b7dcfc0c392c, noreply
author address) with only the 30 library modules in the import closure of
PaperBounds, the entry files at the repository root, and a Lean build workflow.
Its `palomar-preflight.yml` calls Palomar's reusable verifier at
PalomarSubmission@ec6064aea91e2f99187f3f46a2652e4d977ce755 in `full` mode; the
first preflight run is 35183549777 (advisory, not a submission). The paper
TeX/PDF is not included. The private repository remains private.

2026-09-17 preflight result: PASS. Public Lean build run 35183535298 passed.
Preflight run 35183549777 (profile palomar-standard-v1, mode full) built the
pinned Landrun, Comparator 575674928e23, NanoDa 68d5ca9db226 and lean4export,
ran Comparator with the challenge provenance audit, and reported status
`pass`, stage `complete`, no errors, no warnings. The Challenge (90 lines,
4,683 bytes, imports only Mathlib) was classified as allowlisted Mathlib
provenance; the licence was detected as Apache-2.0; the Mathlib cache was
available. The bounded report is saved as
`verification/palomar/theorem1-preflight-35183549777.json`. Limits: a
preflight is advisory (Palomar may still differ on rerun) and excludes
Challenge rendering, editorial review and registration. The disposable
negative controls from the original Sprint 6 plan (changed theorem type,
forbidden axiom, forbidden Challenge import) were not run; running them on the
public repository would publish throwaway commits.

2026-09-17 reviewer material added to the public repository (user request: make
it self-contained for Palomar review): `docs/THEOREM1.md` (informal statement,
11-step proof outline mapped to Lean declarations, fidelity notes,
reproduction); `formalization.yaml` now cites that document as the location of
the original proof, records the preflight and an eighth fidelity divergence;
README links it; a stale comment in DirectBound was corrected. Public commit
85ddda80b8f95c322bb0a80afd9e07e50f5b6f05: Lean build run 35184663672 passed;
Palomar preflight run 35184670576 status pass, stage complete, no errors or
warnings (report `verification/palomar/theorem1-preflight-35184670576.json`).
The public repository is now the canonical source for the Theorem 1 entry;
`palomar/theorem1/` here is the development copy and differs in metadata
wording. Submitting commit 85ddda8 is the user's action.

2026-09-18: the user submitted the entry at submit.palomar-registry.org
(repository carlok/sharp-symmetry-bounds-lean, commit
85ddda80b8f95c322bb0a80afd9e07e50f5b6f05). The status page URL carries a
secret fragment and is therefore NOT recorded here; the user holds it. Palomar
re-runs mechanical verification in its own public Actions and then performs a
private editorial review; the user decides afterwards whether to register or
withdraw. Nothing further is authorized here: no automated submission, no
registration, no publication of the note.

Palomar's own mechanical verification of the submission passed: public run
https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/35342709088
(request id ta4ks1u1dce6, mode full, profile palomar-standard-v1) fetched
carlok/sharp-symmetry-bounds-lean@85ddda80b8f95c322bb0a80afd9e07e50f5b6f05 and
reported status pass, stage complete, no errors or warnings; its bounded report
is saved as `verification/palomar/theorem1-official-verification-35342709088.json`.
Editorial review is private to the user; register vs withdraw is the user's
decision.

2026-09-18 automated editorial review (reviewer model codex:gpt-5.6-sol):
problems identified, registration not offered, one requested change. Mechanical
verification succeeded and the statements and account were called otherwise
sound; the single objection was a provenance contradiction, since the metadata
declared `original-proof` while the account says the working note came first.
Fix (public commit ced9fe2d4d2aa42aa03bbc19b1b56cdcd18c9413): the note is now
`type: unpublished working note`, `relationship: formalizes`, with the
chronology stated in its note field and in docs/THEOREM1.md, so the result
origin is source-based. No Lean, Challenge, Solution or comparator change.
Public Lean build run 35345758932 and Palomar preflight run 35345766939 both
pass (report `verification/palomar/theorem1-preflight-35345766939.json`).
The corrected commit must be submitted as a NEW submission with the Palomar ID
left blank; the earlier submission can be withdrawn. Both are user actions.

2026-09-18 second submission (commit ced9fe2d4d2aa42aa03bbc19b1b56cdcd18c9413,
submitted 13:41:49Z): mechanical verification passed (public run 35351732435,
status pass, stage complete, no errors or warnings; report saved as
`verification/palomar/theorem1-official-verification-35351732435.json`), the
Challenge rendering check ran, and the automated editorial review (model
codex:gpt-5.6-sol, 14:08:42Z) identified NO problems with statements,
definitions, presentation, literature account or research interest. Palomar now
offers register or withdraw. Registration is pre-launch: it makes the record,
review, repository and commit public and creates immutable source-preservation
tags; the submitter's GitHub identity is not published. That choice is the
user's alone and is not authorized here.

2026-09-18 registration (user action, 14:29:47Z). The record is public as
`PALOMAR-2026-09-18-000007` version 1, status `registered`, trust level `high`,
review outcome `neutral` with no warnings, challenge 90 lines / 4,683 bytes,
dependency provenance allowlisted. Human permalink
`https://palomar-registry.org/entry?id=PALOMAR-2026-09-18-000007&version=1`;
machine record
`https://data.palomar-registry.org/entries/PALOMAR-2026-09-18-000007-v1.json`,
also reachable by repository at
`https://data.palomar-registry.org/repositories/carlok/sharp-symmetry-bounds-lean.json`.
A copy of the record is stored as
`verification/palomar/theorem1-registry-record-PALOMAR-2026-09-18-000007-v1.json`.
Mechanical evidence cites run 35351732435, Comparator
`575674928e239f5bc452aab72d1dd7b0f1326494`, NanoDa
`68d5ca9db226849b41a6fff59d796ff19d0a8840`, Landrun
`811cfff51ceaf3d9843708aa6d22e9b84ccac8b4`, lean4export
`4e7915201d3f9f04470d9eae002fa695f7cdc589`. Source preservation created the
fork `PalomarArchive/carlok--sharp-symmetry-bounds-lean--f3036be09495` at commit
`ced9fe2d4d2aa42aa03bbc19b1b56cdcd18c9413` with an immutable tag, and archive
forks of all ten pinned dependencies including Mathlib
`81a5d257c8e410db227a6665ed08f64fea08e997`. Registration is not a novelty
certificate and not a human review: the editorial review was automated
(`codex:gpt-5.6-sol`). Only Theorem 1 is registered; the rest of this private
library is not covered. The submission status URL keeps its secret fragment and
is still not stored here.

2026-09-28 (user): a second entry for Theorem 2 is decided after the preprint;
nothing is prepared before. It would need a `paper_*` endpoint packaging
T2.1–T2.7, a second Challenge/Solution and a public copy of the family
modules. The private `palomar/theorem1/formalization.yaml` was brought in line
with the registered metadata on 2026-09-29; it remains the development copy.

2026-09-29 (user): no arXiv preprint (no arXiv access) and no novelty claim;
the specialist decides whether the bounds are known. The Palomar registration
of Theorem 1 is the public record, and the email to Alcázar et al. is an FYI
pointing to it. A Theorem 2 entry and publishing this repository are
undecided. Whether the Sprint 7 TeX appendix is still wanted is open.

2026-09-29 (user), later the same day: queue making this repository public
before the email is sent, since there is no arXiv. A scrub comes first (local
paths, predecessor-project references, personal tooling notes, an outsider
README, a secret scan over the whole history, which is published unchanged).
The Lemma 9 counterexample is already public in the registered Theorem 1
entry's metadata.

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

2026-09-28 plan for the missing negative controls: a `workflow_dispatch` job in
this private repository mutates its own checkout (changed theorem type, a
forbidden axiom, a forbidden Challenge import) and requires each check to
fail. No throwaway commits, nothing public.

2026-09-30: done, in the repository (public since that day).
`palomar-negative-controls.yml` runs three jobs on `workflow_dispatch` and on
changes to the entry or its scripts. Each mutates its own throwaway checkout
with `scripts/palomar/negative_control.py`, builds the entry (every mutation
still compiles) and requires the targeted pre-check to fail for the intended
reason: the Challenge bounding the full group by `3d` makes the statement
dumps differ; the Solution proving `full_bound_sharp` from a new axiom is
named by the axiom check; a Challenge importing `PaperBounds` is rejected by
the new `check_challenge_imports.sh`, which the entry build now also runs. Run
`36669665932` (commit `35f51bc`): all three controls rejected; entry build
`36669665920` and Linux run `36669665863` passed. These exercise the CI
pre-checks; Palomar's own Comparator and NanoDa replay already passed for the
registered entry.

## Sprint 7 — TeX integration and final snapshot

Only after Sprint 6, refactor the existing note without bloating its mathematical
exposition. Add a short formalization section/appendix with theorem-to-Lean
links, reproduction instructions, dependencies, exact scope, AI disclosure,
and the distinction between kernel checks, dry runs, novelty, and human review.
Cite registration only where it exists: Theorem 1, `PALOMAR-2026-09-18-000007`,
automated editorial review; imply it for nothing else. State the proof-route
differences (genus by an explicit basis, not Riemann–Hurwitz; irreducibility by
Eisenstein). Rebuild, run ChkTeX, inspect the PDF, and rerun verification
against the final committed snapshot.

Gate: paper, formal statements, metadata, and verification evidence agree at
one private release-candidate commit.

2026-09-30: done. Appendix A of `sharp_symmetry_bounds.tex` maps every
theorem, lemma and remark to its Lean declarations and states the readings,
the route differences and the registration scope; the mathematical text is
unchanged. latexmk, chktex, a page-by-page inspection and `uv run verify.py`
passed. Record: [SPRINT-7](verification/SPRINT-7.md).

## Completion discipline

Record each sprint's checks and completion commit here. The permitted proof
axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`. No proof
holes, `native_decide`, custom axioms, or hidden theorem assumptions may be
used to close a sprint. Palomar-ready is a reproducible, honestly described
candidate—not guaranteed editorial approval or registry acceptance.
