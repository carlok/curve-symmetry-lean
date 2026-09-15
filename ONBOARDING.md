# CurveSym — handoff prompt for the next LLM

Continue the complete Lean formalization of sharp symmetry bounds for real
algebraic curves, ultimately producing a private Palomar-ready candidate.
Read this entire handoff before acting. Updated 2026-09-15.

## Work in the correct checkout

**Active repository:**
`/Users/carlo/Documents/varie/hacks/lean4/curve_symmetry`

Private GitHub: `carlok/curve-symmetry-lean`
Remote: `git@github.com:carlok/curve-symmetry-lean.git`
Working branch: `codex/main` only (GitHub default; not literally `main`).
Sprint completion points are annotated tags `sprint-0-complete` to
`sprint-3-complete`. The old `codex/sprint-*` branches were deleted on
2026-09-15 with user approval; all their commits are in `codex/main`.
License: Apache-2.0.

**A second local checkout exists:**
`/Users/carlo/Documents/varie/hacks/lean4/curve-symmetry-lean`.
It was inspected read-only on this date: clean at `004c3df`, an old Sprint 1
checkpoint, tracking the same remote. It is NOT where the recent work was
done. Do not switch to it, delete it, merge it, or overwrite it without a
user request. Use explicit working directories in tools.

The desktop task may start in the still older directory
`/Users/carlo/Documents/varie/hacks/t/transcendental`; that is not this
project's active root either.

## First actions and working agreement

1. Inspect current Git status, branch, log and applicable repository instructions.
2. Read STATUS.md, COVERAGE.md, SPRINTS.md, CHECKS.md, lean/README.md,
   verification/genus-scope-study.md, verification/function-field-double-cover.md,
   and sharp_symmetry_bounds.tex.
3. Confirm the next requested scope with the current user message. Without a
   request to continue proofs, do not begin another package merely because this
   handoff lists it.

Current source and Git evidence override this document if they have advanced.
Preserve unrelated or uncommitted changes. Work one meaningful bounded step
per request unless more are explicitly requested. Explain what coverage gap
each step closes; avoid endless helper milestones.

Read /Users/carlo/.codex/RTK.md and /Users/carlo/.codex/KARPATHY.md.
Prefix shell commands with `rtk`, normally `rtk proxy`. Use apply_patch for
edits. If .codegraph/ exists, consult CodeGraph before code exploration; it
was absent in this active repository at the recent checks.
Do not spawn agents unless authorized by the current instructions.

The active repository can be outside the task's writable sandbox roots.
Use the appropriate escalation; never bypass rejection. Earlier approval
service capacity errors were not GitHub failures.

After a verified implementation checkpoint, update coverage, status,
verification evidence and this handoff as needed. Use scoped commits directly
on codex/main and push it (one CI run per push; the workflow cancels an
in-progress run on the same branch, so wait for CI before pushing again when
its result matters). Do not force-push. Do not delete branches or tags
without a user request. Tag a sprint's completion commit `sprint-N-complete`.

Do not create recurring work, publish the repository, contact experts or
Palomar, or make an external submission. Those are not authorized.

## Current immutable proof checkpoint

The current completion snapshot is the commit introducing
`verification/function-field-double-cover.md`; recover its exact hash with
`git log -1 --format=%H -- verification/function-field-double-cover.md`.
It adds G07a (FamilyFunctionField) on top of ba20da2 and the documentation-only
scope-study and branch-policy commits.
Inspect Git rather than assuming a clean tree.

Local checks for that proof checkpoint:

- New module and aggregate compiled incrementally with warnings as errors.
- Complete namespace axiom audit: 1,286 declarations.
- Source preflight: 81 Lean modules, nine exact dependency pins.
- All six package tests passed; whitespace check passed.
- 577 written theorem/lemma declarations, 152 written definitions/etc.,
  9,166 Lean source lines. Counts include machinery, not novel results.

Private Linux runs 34938739018 and 34938739562 for ba20da2 both passed.
The new completion snapshot needs its own CI result; do not inherit that success.
The preceding 2cff8af passed runs 34937614030 and 34937613937.
Ordinary CI is not a Palomar dry run or independent replay.

## Fixed objective and honesty boundary

The goal remains the FULL paper, not Theorem 1 alone. Never close gaps by
assuming conclusions, using custom axioms, redefining invariants conveniently,
or replacing genuine genus by an arithmetic branch-count formula.
Only propext, Classical.choice, and Quot.sound are permitted proof axioms.
No sorry or native_decide in the library. Only a future isolated Challenge
may contain intentional theorem placeholders; neither definitions nor Solution
may depend on them.

Kernel checking does not establish novelty, usefulness, statement fidelity,
editorial acceptance or independent human review. No such certification exists.
Do not edit the paper TeX/PDF for formalization until Sprint 6 passes.

## Mathematics and completed coverage

The real family is
`C(m,alpha) = {z in C : Re(z^m (|z|^2 + alpha)) = 0}`.
Its affine complexification is
`X^m(alpha + XY) + Y^m(conjugate(alpha) + XY)`.
Total degree is m+2; bidegree is (m+1,m+1). Claimed genuine normalization
genus m remains unproved in Lean.

Types: BPoly is MvPolynomial (Fin 2) C; realLocus evaluates at (z,conj z);
Sphere is OnePoint C; Möbius matrices are GL(2,C) acting on the standard
projective line. Actual symmetry groups use transformations, not redundant
matrix representatives. Euclidean groups use Mathlib isometry equivalences.

Read exact hypotheses. Most current normalized family conclusions assume
m>=2, alpha nonreal, and norm alpha=1. Some earlier statements allow any
nonreal alpha; equality classification requires m>=3. Do not silently alter
these boundaries.

Theorem 1 is formalized for real Cartesian curves and actual isometry groups.
Sprint 2 is complete at the classical complex-point Zariski-atlas scope:
arbitrary ambient completeness, global closure and irreducibility are proved.
Singular-pair preservation is DERIVED, not assumed.

Sprint 3 packages 1–6 are complete:

| Package | Main checked declarations/modules |
|---|---|
| 1: basic family geometry | PaperFamilyGeometry.paper_family_geometry (namespace CurveSymmetry) |
| 2: exact parameter equivalence | family_mobius_equivalence_iff; family_anti_mobius_equivalence_iff in FamilySphereClassification |
| 3: full ambient group | familyAmbientGroup_dihedral, familyAmbientGroup_card, familyAmbientGroup_generators in FamilyDihedral |
| 4: full Euclidean group | family_affine_self_filter, family_isometry_iff_rotation, family_isometry_card in FamilyEuclidean |
| 5: algebraic coefficients | familyAmbientGroup_algebraic_representative in FamilyAlgebraic |
| 6: distinct parameter family | family_arc_equivalence_iff in FamilyParameterArc |

The first table entry refers to the file PaperFamilyGeometry; the actual Lean
name is CurveSymmetry.paper_family_geometry, not a nested file namespace.
All declarations above are under CurveSymmetry.

Important details:

- familyAmbientGroup is the Möbius permutation image intersected with the
  spherical-set stabilizer, defined independently of normal forms.
- Its group is dihedral of order 4m, with generators/relations/exhaustion;
  no anti-Möbius self-inclusion exists. Zero and infinity are included.
- The full Euclidean group consists exactly of centered root rotations,
  a^(2m)=1, with order 2m. Translation is eliminated, not assumed absent.
  The m=2 opposite-symmetry gap is closed for normalized parameters.
- Algebraic alpha gives an algebraic-entry matrix REPRESENTATIVE of every
  ambient symmetry. Arbitrary scalar rescalings need not be algebraic.
- Polynomial pullbacks alone were not used as substitutes for actual maps.

## Completed new packages; next proof work

The final Sprint 3 consequence is now proved:
for fixed m>=2, alpha=exp(i theta), 0<theta<pi, gives pairwise fully
Möbius-inequivalent examples.

FamilyParameterArc supplies the unit/nonreal/injective/conjugation-exclusion
facts and family_arc_equivalence_iff for actual spherical equivalences of
both parities. R02 is closed; the Sprint 3 gate audit is recorded in the
completion report. Do not redo any of packages 1–6.

The first Sprint 4 package also closes G10. FamilyCircleSections proves
familyCircleRootEquiv (a free root-rotation orbit) and
family_metric_circle_card (exactly 2m points on every positive-radius centered
metric circle). It only assumes m>0 and nonreal alpha, not normalization.

Two further bounded packages are now checked:
BinaryTangentDirections defines the homogeneous zero locus on the actual
projective line, proves representative independence, and counts exactly m
directions for the two diagonal tangent cones. QuinticExample proves the
printed Cartesian expression, sign reversal under exp(pi*i/3), exact order
six of the actual Euclidean rotation, and the six-element isometry count.
S10 is closed. Do not repeat the direction count.

OrdinaryMultiplePoints now closes G06 at the standard-chart algebraic scope.
pointIdeal/HasMultiplicityAt use powers of the maximal ideal; OrdinaryAtOrigin
adds a tangent cone equal to a nonzero multiple of n pairwise nonproportional
linear forms. family_ordinary_multiple_points (m>=2, nonreal alpha) proves both
chart origins (0,0) and (∞,∞) ordinary m-fold, and multiplicity one at every
other zero of the four chart equations. Invariance of multiplicity under
nonlinear chart transitions or ambient maps is NOT claimed; do not advertise it.

IsometrySign closes S03/S04: paper_isometry_sign gives f(Tz) = ε f(z) with
ε = ±1 for every actual isometry, ε = 1 for opposite ones, and
opposite_symmetry_fixed_point excludes glide reflections. RadialAntiForm
closes S07: paper_high_order_radial_form derives N = 2m, sign -1, equation (5)
with 1 <= deg A <= (d-m)/2 and m <= d-2. Do not redo these.

All bounded non-genus Sprint 4 rows are now closed. The genus meaning is the
user-approved function-field genus (verification/genus-scope-study.md).
FamilyFunctionField proves G07a: family_functionField_double_cover identifies
Frac(ℂ[X,Y]/(P_α)) with ℂ(t)[W]/(W² − h), h squarefree of degree 2m+1, using
Fact instances for 0 < m and α ≠ star α. Continue with G07b from the tracker.
G07–G09 require genuine
normalization/ramification/genus foundations; do not replace them by numerical
identities or opportunistically rename helper steps as completed packages.

## Package tracker (done / todo)

Keep this list current after every package; it is the working queue.
Status words: DONE = checked, committed and pushed; WIP = uncommitted work in
the tree; TODO = not started. Coverage IDs refer to COVERAGE.md.

Done:

- [x] Sprints 0–2 (baseline, package, global geometry/completeness; G01–G05, G11)
- [x] Sprint 3 packages 1–6 (T2.1–T2.7, G12, G13, R02, R03)
- [x] Sprint 4: G10 circle sections (`8688b5e`)
- [x] Sprint 4: tangent directions + S10 quintic (`6fb2109`, CI passed)
- [x] Sprint 4: G06 ordinary multiple points (`2cff8af`, CI passed)
- [x] Sprint 4: S03 + S04 Lemma 3 sign, S07 equation (5) (IsometrySign,
      RadialAntiForm; commit introducing verification/sign-and-radial-form.md)

Todo, in intended order:

- [x] Genus scope study: verification/genus-scope-study.md (no Lean changes)

Todo, in intended order:

- [x] CI for ba20da2 passed (runs 34938739018, 34938739562)
- [x] User decision: genus = function-field genus (route B); R01 must go
      through genus as printed
- [x] User decision: single codex/main branch, sprint completion tags,
      old codex/sprint-* branches deleted
- [x] G07a function field of V_α = ℂ(t)[w]/(w² − h_α), h_α squarefree of
      degree 2m+1, degree-two extension (FamilyFunctionField)
- [x] CI for G07a commit cac8e03 passed (run 34940883130, codex/main)
- [ ] G07b first step: prove ℂ[t][w]/(w² − h) is integrally closed (the
      integral closure of ℂ[t] in K) using squarefree h; then place
      classification via RatFunc.valuation_isEquiv_infty_or_adic
- [ ] G07b places of K_α over ℂ(t) (Ostrowski + integral closure)
- [ ] G08 exactly 2m+2 ramified places incl. 0, ∞; index two
- [ ] G09a Ω_{K/ℂ} rank one, order of differentials at places
- [ ] G09b holomorphic differentials span t^i dt/w (i<m): genus m;
      Hurwitz degree identity for this cover
- [ ] R01 quartic genus 3 vs 2 (likely Kummer-cover generalization)
- [ ] Sprint 4 gate audit, then Sprints 5–7 (contract, dry run, TeX)

## Remaining major work

Sprints 0–3 complete at their stated scopes.
Sprint 4 is the highest-risk foundation task: actual normalization/double
cover, ramification, Riemann–Hurwitz and genuine genus m, and the quartic
genus comparison R01. No ready-made full genus interface was found in the
installed Mathlib. Do not manufacture an invariant or weaken the goal.

Sprint 5: accurate compact Challenge/Solution, permitted import closure,
Comparator configuration, schema-valid metadata, pinned tools and honest
literature/review status. Preserve inspected arXiv vs uninspected journal
version distinctions.
Sprint 6: immutable clean private Linux contract-faithful dry run, protected
Comparator, isolated Challenge, credential/network-free proof sandbox,
NanoDa replay and failing negative controls. No simulated sandbox counts.
Sprint 7: only then TeX integration, theorem links, reproducibility and AI
disclosures, PDF checks and final revision-bound verification.

Palomar-ready does not mean accepted, registered or human-reviewed.

## Do not reopen resolved history

All atlas/gluing/inversion continuity work is complete at its stated scope.
ProjectiveAtlasUniqueness supplies the standard affine-Zariski open-atlas
characterization; ProjectiveCurveIrreducibility closes global irreducibility.
A separate scheme comparison is not currently a missing paper obligation.
Topology instances remain local: do not confuse Euclidean and Zariski topology.

Earlier rollback of 128b416 and ee55b46 was followed by explicit authorization
to restore and reverify the inversion work. It is restored and used. Do not
undo it or ask again based on stale history.
The “44/51 candidates”, novelty-filter prompt and external-disk TeX dossier
discussion belonged to another project and was cancelled here. Do not resume it.

## Build and audit commands

Run from the active repository. Lean: leanprover/lean4:v4.32.0.
Mathlib: 81a5d257c8e410db227a6665ed08f64fea08e997.
Reuse installation: /Users/carlo/Documents/varie/hacks/lean4/diaz-modulus-lean.
Do not clone duplicate dependencies, modify their sources, or update pins.
Root lakefile.toml and lake-manifest.json describe the portable package.

```sh
rtk proxy sh lean/check.sh /Users/carlo/Documents/varie/hacks/lean4/diaz-modulus-lean
rtk proxy python3 -B scripts/check_sources.py --reuse /Users/carlo/Documents/varie/hacks/lean4/diaz-modulus-lean
rtk proxy python3 -B -m unittest discover -s scripts -p 'test_*.py'
rtk proxy git diff --check
```

For an incremental build, construct LEAN_PATH from this project's lean/.build
plus each installed dependency's .lake/build/lib/lean. Compile changed modules
in dependency order, then CurveSymmetry.lean, then verification/Audit.lean.
Use elan run leanprover/lean4:v4.32.0 lean -DwarningAsError=true.
Audit.lean uses run_cmd, not main: do NOT pass --run.
New modules must appear in both the aggregate imports and Lake roots.
Beware stale ignored oleans; report incremental checks as incremental.

## Paper preservation

Unchanged hashes:

```text
3aff1c6edf6f189de6fa56c690631c266364a3b129408eb0fd5a200ceb186925 sharp_symmetry_bounds.tex
8b1f71e7a4f5dbce7fce3de383b675411e3fbba21bea4939609991f47a10ffd1 sharp_symmetry_bounds.pdf
```

First response: identify the correct checkout, summarize current evidence,
and state the next bounded obligation authorized by the user's request.
Do not advertise full-port completion or Palomar readiness.
