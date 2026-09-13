Continue CurveSym: a complete Lean formalization of a paper on sharp symmetry bounds for real algebraic curves, ultimately targeting a private Palomar-ready candidate.

PROJECT
Repository: /Users/carlo/Documents/varie/hacks/lean4/curve_symmetry
Private GitHub: carlok/curve-symmetry-lean
Remote: git@github.com:carlok/curve-symmetry-lean.git
Working branch: codex/sprint-2
License: Apache-2.0

First inspect the current Git status, branch, history, and repository instructions. Preserve unrelated changes. Read:
- SPRINTS.md
- COVERAGE.md
- verification/SPRINT-2.md
- lean/README.md
- CHECKS.md
- sharp_symmetry_bounds.tex

These files, not this handoff, are authoritative if the state has changed.

WORKING AGREEMENT
Work one bounded, mathematically meaningful step per request, unless the user explicitly requests more. Verify the step, update the coverage and verification records, and commit and push to the existing private branch. Clearly distinguish local checks from completed Linux CI.

Do not create recurring background work. The previous readiness automation was paused to avoid consuming tokens between sessions.

Do not publish the repository, contact Palomar or mathematicians, or submit anything externally. Private readiness is not registry acceptance.

Use the user's current AGENTS.md instructions, including:
- Read /Users/carlo/.codex/RTK.md and /Users/carlo/.codex/KARPATHY.md.
- Prefix shell commands with rtk, normally `rtk proxy`.
- If the repository contains .codegraph/, consult CodeGraph before locating or understanding code. Check whether Lean is actually indexed; earlier checks found limited language coverage.
- Use apply_patch for source edits.
- The relocated repository may lie outside writable sandbox roots; request appropriate tool escalation rather than bypassing restrictions.
- Do not duplicate or modify the installed Lean/Mathlib dependencies.

CURRENT CHECKPOINT AND ROLLBACK
Updated 2026-09-12. Inspect Git for the current immutable HEAD; this handoff
is updated through the open four-chart cover and affine-chart open embedding.
- Baseline 1398e34 reverted the inversion work and passed private Linux CI.
- 1632652 reverted ee55b46; 1398e34 reverted 128b416.
- New checkpoint 1f49d05 proves polynomial-map Zariski continuity.
- The subsequent CoordinateExchange checkpoint proves the swap homeomorphisms.
- After those checkpoints the user explicitly approved restoring and re-verifying both inversion steps. They are now reinstated alongside the polynomial-map and coordinate-exchange results.
- Restoration was committed as 3164274. Subsequent modules SimultaneousInversion and ProjectiveClosureGluing are now checked; see the latest verification report and Git HEAD.

The earlier rollback removed:
- lean/InversionDenominators.lean
- lean/InversionContinuity.lean
and their associated imports and documentation changes.

The rollback decision has since been explicitly resolved: the user answered
yes to restoring and re-verifying these two steps. Both files are now present,
using the historical proofs from 128b416 and ee55b46. No further restoration
approval is needed for these files. Do not mistake this restoration for new
mathematics, or undo it based on an older handoff.

The discussion about “44/51 verified candidates,” a novelty-filtering prompt, and a TeX dossier on an external disk was explicitly identified as belonging to another project and cancelled. No such dossier should be pursued here. No prompt or dossier file was created, committed, or pushed.

OBJECTIVE AND HONESTY BOUNDARY
The fixed objective is the full mathematical paper, not Theorem 1 alone.

Theorem 1 is formalized against real Cartesian curves and actual Euclidean isometry groups. Theorem 2 and supporting global geometry are incomplete.

Never close a gap by:
- assuming the conclusion as a hypothesis;
- redefining an invariant to make the conclusion tautological;
- replacing geometric genus with a numerical branch-count formula;
- treating polynomial-pullback classification as classification of arbitrary ambient maps without proving the bridge;
- treating chart-level closure as global projective closure.

The proof library must remain hole-free. The allowed proof axioms are exactly:
propext, Classical.choice, Quot.sound.

Only a future isolated statement-only Challenge file may contain intentional theorem placeholders. Library definitions and Solution must not depend on them. No custom axioms, sorry, or native_decide.

Kernel verification does not certify novelty, statement fidelity, usefulness, or independent human review.

SPRINT STATUS
0 — relocation and private Git: complete.
1 — portable package and coverage inventory: complete.
2 — global geometry: in progress; arbitrary ambient four-form completeness is proved, but projective Zariski-closure identification remains incomplete.
3 — full ambient symmetry theorem: not complete.
4 — normalization, ramification, genuine genus, remaining claims: not complete; highest foundational risk.
5 — Palomar statement contract and metadata: not started.
6 — faithful private Linux dry run: not started.
7 — TeX integration: not started.

Do not refactor the original TeX/PDF for formalization before Sprint 6 passes. Keep the full-port objective explicit.

MATHEMATICAL SETTING
The family is
C_{m,α} = {z ∈ C : Re(z^m (|z|² + α)) = 0}.

Its complexified affine equation is
P_{m,α}(X,Y)
  = X^m(α + XY) + Y^m(conjugate(α) + XY).

Important distinctions:
- ordinary total degree: m+2;
- bihomogeneous degree: (m+1,m+1);
- claimed normalization genus: m, still requiring genuine formal foundations.

Nonreal parameters are essential in the relevant theorems.
Some results allow any nonreal α; others require |α|=1.
Some hold for m>0, some m≥2, and the extremal classification requires m≥3, equivalently degree≥5.
Read each declaration rather than propagating stronger or weaker hypotheses informally.

The formal core uses:
- BPoly = MvPolynomial (Fin 2) C;
- realLocus P evaluates P at (z, conjugate z);
- actual Euclidean isometries for paper-facing symmetry groups;
- Sphere = OnePoint C;
- standard Projectivization C (Fin 2 → C);
- arbitrary GL(2,C) matrices for Möbius transformations.

PROVED GLOBAL COMPLETENESS
Relevant modules:
- FamilyGlobalTransport
- HomogeneousDifferential
- PolynomialDifferential
- HomogeneousCharts
- FamilyGlobalSingularities

The global chart-Jacobian singular locus of the constructed bihomogeneous family is exactly the two diagonal points:
(0,0), (∞,∞).

For m≥2 and nonreal parameters, arbitrary ambient Möbius or anti-Möbius maps satisfying the relevant spherical containment are proved to have the two holomorphic or two conjugated forms:
cz, c/z, c conjugate(z), c/conjugate(z).

Pair preservation is derived, not assumed. The formulas cover every sphere point, including zero and infinity.

This does not itself complete the exact group, parameter equivalence, projective-closure, or genus claims.

RECENT CHART AND TOPOLOGY WORK
The following modules are in the retained source:

AffineClosure:
- exact vanishing ideal of the infinite real diagonal of an irreducible curve;
- actual affine spectral Zariski closure using Mathlib PrimeSpectrum.

ProjectiveBoundary:
- the constructed projective curve outside its finite-by-finite chart consists exactly of:
  (∞,0), (0,∞), (∞,∞).
- This is a set decomposition, not a closure theorem.

MixedCornerClosure:
- deleting an irreducible divisor not dividing the equation preserves hypersurface closure;
- density also holds using actual complex evaluation points, through Nullstellensatz/Jacobson arguments;
- mixed-chart origin lies in the relevant closure.

ReciprocalCornerClosure:
- reciprocal chart density after deleting both coordinate axes;
- includes the origin representing (∞,∞);
- checks nondivisibility by both coordinates.

OtherMixedCornerClosure:
- explicit original-point map (X,Y) ↦ (1/Y,X);
- exact image identity with the punctured second mixed chart;
- corresponding affine spectral closure and origin membership.

AffineChartImages:
- matching original-point image and closure identities for:
  (X,Y) ↦ (1/X,Y);
  (X,Y) ↦ (1/X,1/Y).

ProjectiveChartMaps:
- standard line charts [z:1] and [1:z];
- four product chart maps, with the second mixed chart ordered as (1/Y,X);
- affine-overlap identities with explicit nonzero conditions;
- curve-membership equivalences;
- exact boundary-origin identities;
- injectivity of all charts;
- four-chart coverage;
- exact chart ranges as zero/infinity coordinate-divisor complements.

These results in ProjectiveChartMaps are set-theoretic. The later atlas modules
now prove an open cover and the affine chart's open embedding (see below).

AffineZariskiTopology:
- topology on complex coordinate vectors induced by evaluation into PrimeSpectrum;
- evaluation is injective and a topological embedding;
- polynomial nonvanishing sets are open;
- polynomial zero sets are closed;
- coordinate-deletion domains are open;
- closure equals the common zero set of the vanishing ideal;
- real-diagonal closure transferred to complex coordinate points.

Its topology instance is LOCAL. Do not overwrite the ordinary Euclidean topology on coordinate vectors globally or confuse Euclidean and Zariski continuity.

WHAT COMES NEXT
Two additional prerequisites are now proved:

PolynomialZariskiMaps:
- polynomialPointMap evaluates two coordinate polynomials;
- polynomialPointMap_eval proves substitution commutes with evaluation;
- polynomialPointMap_continuous proves continuity in the explicitly local Zariski topology, using polynomial zero sets.

CoordinateExchange:
- exchangeCoordinates swaps the two coordinates and is involutive;
- coordinateExchangeHomeomorph is a Zariski homeomorphism of the affine plane;
- coordinateExchangeTorusHomeomorph restricts it to both coordinates nonzero;
- affine/reciprocal chart identities agree with projective factor exchange;
- otherMixedProjectiveChart already uses reversed coordinate order: it equals the swapped mixedProjectiveChart WITHOUT applying exchangeCoordinates again.

InversionDenominators and InversionContinuity are now restored:
- polynomial denominators under one-coordinate inversion can be cleared;
- inverse images of polynomial zero sets have polynomial numerators on the nonzero domain;
- coordinateInversionHomeomorph gives a Zariski homeomorphism for either coordinate's nonzero domain.

SimultaneousInversion is now checked:
- simultaneousInversionHomeomorph is a Zariski homeomorphism of the torus;
- simultaneousInversion_val gives the exact vector (1/X,1/Y);
- simultaneousInversion_chart matches the affine/reciprocal projective charts;
- simultaneousInversion_curve matches their curve equations.

ProjectiveClosureGluing is now checked:
- ClosedInProjectiveCharts S means all four chart preimages of S are affine-Zariski closed. It is a predicate, NOT a topology declaration.
- family_projective_chart_gluing: if such S contains all complex affine curve points in the projective affine chart, it contains the full constructed projective family, for every m>0 and every complex parameter.
- family_closed_in_projective_charts: the family satisfies that predicate.
- family_projective_closure_of_chart_continuity: for ANY ambient topology in which the four chart maps are continuous and the family is closed, the closure of the complex affine curve image is the full projective family.

The last theorem is CONDITIONAL, but ProjectiveAtlasTopology now supplies a
family-independent topology: the final topology of the disjoint union of the
four standard affine charts, each with its proved affine Zariski topology.
projectiveAtlas_isClosed_iff identifies closed sets with ClosedInProjectiveCharts;
projectiveChart_continuous proves continuity of every chart. Instances stay LOCAL.
ProjectiveAtlasClosure proves family_projectiveAtlas_affine_closure for m>0
and arbitrary alpha, and family_projectiveAtlas_real_closure for m>0 and
nonreal alpha. The latter starts from the actual affine real diagonal and
includes all boundary points, using irreducibility and infinite real locus.

These are unconditional theorems IN THE CHART-FINAL TOPOLOGY. Its identification
with standard projective Zariski geometry is still pending. Do not mark G01
complete. ProjectiveAtlasOpenCover now proves the exact affine-overlap domains,
openness of all four chart ranges (checking all sixteen overlaps), and coverage.
ProjectiveAffineEmbedding proves affineProjectiveChart_isOpenMap and
affineProjectiveChart_isOpenEmbedding using the actual inversion transitions.
Thus the affine chart's subspace topology is proved to be the affine Zariski
topology; this is not just a continuous injective map.

Next: prove open embeddings for the two mixed charts and the reciprocal chart,
then justify the standard atlas topology. Open range alone does NOT imply an
embedding. Do not repeat the density, inversion, open-cover, affine-embedding,
or topology-relative closure proofs as new milestones.
The search found Mathlib ProjectiveSpectrum.Topology, but it uses projective
spectrum objects rather than the current Projectivization point type; a bridge
or a justified standard atlas construction still needs work. Merely declaring
a topology to make the family closed does not meet the fidelity requirement.

The individual inversion continuity step is done after explicit approval;
do not ask again or redo it as a new result. Read the latest verification
report for the recheck evidence and current Linux CI status.

Do not keep multiplying tiny helper milestones without explaining how they close an actual coverage obligation. Favor coherent verified steps and report which gap remains afterward.

BUILD ENVIRONMENT
Lean toolchain: leanprover/lean4:v4.32.0
Mathlib revision:
81a5d257c8e410db227a6665ed08f64fea08e997

Existing dependency installation:
 /Users/carlo/Documents/varie/hacks/lean4/diaz-modulus-lean

Use the root lakefile.toml and exact lake-manifest.json. There are nine pinned package revisions. Do not run dependency updates casually.

Full local library check, from the project root:
rtk proxy sh lean/check.sh /Users/carlo/Documents/varie/hacks/lean4/diaz-modulus-lean

Source/dependency preflight:
rtk proxy python3 -B scripts/check_sources.py --reuse /Users/carlo/Documents/varie/hacks/lean4/diaz-modulus-lean

Package tests:
rtk proxy python3 -B -m unittest discover -s scripts -p 'test_*.py'

The full imported namespace audit is verification/Audit.lean.
Run it with `lean`, not `lean --run`; it uses run_cmd and has no main.

For incremental compilation, assemble LEAN_PATH from:
- this project's lean/.build;
- each existing dependency package's .lake/build/lib/lean.

Compile changed dependencies before dependents, then the aggregate:
lean/CurveSymmetry.lean
and then verification/Audit.lean.
Use -DwarningAsError=true.

Be alert to stale ignored .olean files after rollback. Audit the current aggregate and source inventory, not whatever compiled artifacts happen to remain in lean/.build.

The current source has 62 Lean files including the aggregate. Consult the latest
entry of verification/SPRINT-2.md for its completed audit count and CI status.
These counts include implementation/helper/generated declarations; they are
not counts of novel theorems. In particular this is NOT the cancelled
44/51-candidate project.

VERIFICATION REPORTING
Record:
- exact commit;
- changed modules and mathematical statements;
- hypotheses and exceptional cases;
- local full build versus incremental build;
- complete namespace axiom audit;
- preflight and tests;
- actual private Linux CI result, when available;
- remaining coverage obligations.

A queued, cancelled, or superseded CI run is not a successful run.
Ordinary private Lean CI is not a Palomar-style dry run.

The eventual faithful private dry run must include the real contract checks, protected Comparator configuration, isolated Challenge, sandboxed verification without credentials/network, NanoDa replay, and failing negative controls. Do not claim these happened before they actually happen.

PRESERVATION
Original TeX SHA256:
3aff1c6edf6f189de6fa56c690631c266364a3b129408eb0fd5a200ceb186925

Original PDF SHA256:
8b1f71e7a4f5dbce7fce3de383b675411e3fbba21bea4939609991f47a10ffd1

Keep these unchanged until the agreed editorial sprint.
Preserve shared dependency sources and unrelated parent-repository files.

FIRST RESPONSE
Briefly report what the current repository confirms and identify the next
coherent proof obligation. Polynomial-map continuity and coordinate exchange
and individual inversion continuity are done: do not repeat them as new work.
The inversion restoration was explicitly approved. Do not resume the cancelled
contribution-dossier task or advertise Palomar readiness.
