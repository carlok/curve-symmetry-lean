# CurveSym — handoff prompt for the next LLM

Continue the complete Lean formalization of sharp symmetry bounds for real
algebraic curves, ultimately producing a private Palomar-ready candidate.
Read this entire handoff before acting. Updated 2026-09-29.

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
   verification/quadratic-integral-closure.md, verification/points-of-double-cover.md,
   verification/finite-places.md, verification/infinite-place.md,
   verification/branch-points.md, verification/differentials-rank.md,
   verification/place-differentials.md,
   verification/holomorphic-differentials.md, verification/quartic-genus.md,
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
Exception (user, 2026-09-28): a private email to Alcázar, Lávička and Vršek
is drafted outside this repository and sent by the user; the assistant sends
nothing. This repository goes public only together with the preprint.

## Current immutable proof checkpoint

The current completion snapshot is `c4a1857` (Prove the family has genus m,
G09b-3d); `681bc60` records its CI. It adds G09 (the genus `m`) on top of the
Lean 4.34.0 merge `db011ac`. Inspect Git rather than assuming a clean tree.

Local checks for that proof checkpoint:

- Full clean `lean/check.sh` against the v4.34 reuse installation, warnings
  as errors.
- Complete namespace axiom audit: 1,679 declarations.
- Source preflight: 98 Lean modules, nine exact dependency pins.
- All six package tests passed; whitespace check passed.
- 760 written theorem/lemma declarations, 185 written definitions/etc.,
  12,805 Lean source lines. Counts include machinery, not novel results.

Private Linux run 35738686055 and the Palomar Theorem 1 entry build
35738686071 passed on `c4a1857`. The merge `db011ac` passed run 35734028877.
A new completion snapshot needs its own CI result; do not inherit that success.
Ordinary CI is not a Palomar dry run or independent replay.

## Fixed objective and honesty boundary

The goal remains the FULL paper, not Theorem 1 alone. Staged exception (user
decision 2026-09-17, SPRINTS Sprint 5): the first Palomar entry, Theorem 1 only,
was developed in palomar/theorem1/, published as the separate public repository
carlok/sharp-symmetry-bounds-lean and registered by the user as
PALOMAR-2026-09-18-000007. Any further entry needs an explicit user go; a
Theorem 2 entry is decided after the preprint (user, 2026-09-28). Never close gaps by
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
Total degree is m+2; bidegree is (m+1,m+1). The normalization genus m is
proved at the approved function-field reading (family_genus, G09); the
quartic comparison R01 is open.

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
Fact instances for 0 < m and α ≠ star α. G07b, G08 and G09 are now done (see
the tracker); the next proof work is R01. G07–G09 required genuine
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

Sprint 4 genus track and later work, in order (checked = done):

- [x] Genus scope study: verification/genus-scope-study.md (no Lean changes)
- [x] CI for ba20da2 passed (runs 34938739018, 34938739562)
- [x] User decision: genus = function-field genus (route B); R01 must go
      through genus as printed
- [x] User decision: single codex/main branch, sprint completion tags,
      old codex/sprint-* branches deleted
- [x] G07a function field of V_α = ℂ(t)[w]/(w² − h_α), h_α squarefree of
      degree 2m+1, degree-two extension (FamilyFunctionField)
- [x] CI for G07a commit cac8e03 passed (run 34940883130, codex/main)
- [x] G07b-1 integral closure of ℂ[t] in ℂ(t)[W]/(W² − h) is ℂ[t] ⊕ ℂ[t]·w
      for squarefree h (QuadraticIntegralClosure; commit introducing
      verification/quadratic-integral-closure.md)
- [x] CI for G07b-1 commit 9327385 passed (run 34943343401)
- [x] G07b-2a integral closure of ℂ[t] in L is a Dedekind domain with
      fraction field L (QuadraticDedekind)
- [x] G07b-2b concrete ring S = ℂ[t][W]/(W² − h) embeds onto that integral
      closure; maximal ideals of S ↔ points (c, d), d² = h(c), via evaluation
      kernels, distinct points distinct ideals (QuadraticRing; commit
      introducing verification/points-of-double-cover.md)
- [x] CI for G07b-2a/2b commit 6e43f53 passed (run 34944104779)
- [x] G07b-2c places containing t ↔ points (c, d), d² = h(c) (DedekindPlaces
      generic, QuadraticPlaces family; commit introducing
      verification/finite-places.md). Original plan, kept for reference:
      work inside R := integralClosure ℂ[X] L (Dedekind, fraction field L,
      = image of QuadRing by quadRingMap_range). Place := ValuationSubring L
      containing ℂ, ≠ ⊤. (i) O ∋ t ⇒ O ⊇ R: constants, t ∈ O and w ∈ O since
      w² = h(t) ∈ O (in a valuation ring x² ∈ O ⇒ x ∈ O). (ii) center
      𝔪 := comap of O's maximal ideal is maximal and nonzero. (iii)
      existence for each 𝔪: LocalSubring.exists_le_valuationSubring applied
      to R_𝔪. (iv) uniqueness: R_𝔪 is a DVR
      (IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain),
      its overrings are R_𝔪 and L (ValuationSubring.primeSpectrumOrderEquiv),
      so a dominating O equals R_𝔪. Then count: two places over t = c when
      h(c) ≠ 0, one when h(c) = 0 (quadRing_isMaximal_iff,
      quadEval_ker_injective). Expect instance friction transporting
      IsFractionRing and DVR structure to a ValuationSubring of L.
- [x] CI for G07b-2c commit e209f92 passed (run 34945242761)
- [x] G07b-3 places not containing t (over t = ∞) (QuadraticInfinity; commit
      introducing verification/infinite-place.md). G07 complete.
- [x] CI for G07b-3 commit 24404dd passed (run 35093882792)
- [x] User decision (2026-09-16): ramification uses the simplest honest
      reading: branch point = fewer than two places over the point; no
      ramification indices; "simple" not separately formalized.
- [x] G08 exactly 2m+2 branch points (FamilyBranchPoints; commit
      introducing verification/branch-points.md)
- [x] CI for G08 commit 4a526be passed (run 35118101524)
- [x] Strategy recorded in SPRINTS Sprint 5 (user decision 2026-09-17): staged
      Palomar entry for Theorem 1 first; triage by review outcome; going
      public only on explicit user go.
- [x] Theorem 1 Challenge draft palomar/theorem1/Challenge.lean (90 lines,
      4.7 KiB, Mathlib-only, compiles with 5 sorry placeholders)
- [x] Solution.lean, comparator.json, nested lakefile/toolchain/manifest,
      statement and axiom pre-checks (scripts/palomar/), CI workflow
      palomar-theorem1.yml (commit adding palomar/theorem1/Solution.lean)
- [x] CI for e09725c passed: Lean Linux build run 35182828662 and Palomar
      Theorem 1 entry build run 35182828668 (Lake accepted the hand-derived
      nested manifest unchanged; statement and axiom pre-checks passed)
- [x] formalization.yaml drafted; accepted by Palomar's own offline loaders
      (SPRINTS Sprint 5, 2026-09-17). USER TO CONFIRM: author/maintainer
      name, model names in automation.models (Codex model not recorded),
      review status self-assessed, cost fields.
- [x] User decision 2026-09-17: option B, fields confirmed, Codex model
      "Codex Sol". Public repo carlok/sharp-symmetry-bounds-lean created
      (commit 4408003, 30 closure modules + entry at root). If refused: make it
      private or delete it and continue here. This private repo stays private.
- [x] Public repo Lean build run 35183535298 passed; Palomar preflight run
      35183549777 (full mode, their real verifier) status pass, no errors or
      warnings; report saved in verification/palomar/
- [x] Public repo made self-contained for review: docs/THEOREM1.md, yaml
      and README updated; commit 85ddda8 build run 35184663672 and preflight
      run 35184670576 both pass (no errors/warnings). Public repo is canonical
      for the entry.
- (moved) Negative controls, formerly "optional, would add public throwaway
      commits": now planned in private CI, a workflow_dispatch job that
      mutates its own checkout. Tracked with the open items at the end.
- [x] User submitted carlok/sharp-symmetry-bounds-lean@85ddda8 on 2026-09-18.
      Status page URL holds a secret fragment; the user keeps it, it is not
      stored in this repository.
- [x] Palomar mechanical verification PASSED on the submitted commit (public
      run 35342709088, request ta4ks1u1dce6; report saved in verification/palomar/)
- [x] Automated editorial review 2026-09-18: one requested change, a
      provenance contradiction (original-proof vs a preceding working note).
      Fixed in public commit ced9fe2d4d2aa42aa03bbc19b1b56cdcd18c9413: the
      note is now a `formalizes` source, result origin source-based. Build run
      35345758932 and preflight run 35345766939 pass.
- [x] Second submission of ced9fe2d4d2aa42aa03bbc19b1b56cdcd18c9413 passed
      mechanical verification (run 35351732435) and the automated editorial
      review with NO problems identified (2026-09-18).
- [x] USER REGISTERED the result on 2026-09-18 (assistant not involved in the
      action). Registry record `PALOMAR-2026-09-18-000007`, version 1,
      registered 14:29:47Z, status `registered`, trust level `high`, review
      outcome `neutral` with no warnings. Permalink
      https://palomar-registry.org/entry?id=PALOMAR-2026-09-18-000007&version=1 ;
      record JSON
      https://data.palomar-registry.org/entries/PALOMAR-2026-09-18-000007-v1.json
      (copy saved as
      verification/palomar/theorem1-registry-record-PALOMAR-2026-09-18-000007-v1.json).
      Preservation fork PalomarArchive/carlok--sharp-symmetry-bounds-lean--f3036be09495
      with immutable tag
      refs/tags/palomar/PALOMAR-2026-09-18-000007-v1/ced9fe2d4d2aa42aa03bbc19b1b56cdcd18c9413,
      plus archive forks of all ten pinned Lean dependencies. Only the public
      repository carlok/sharp-symmetry-bounds-lean is exposed; this private
      repository is not referenced by the record.
- [x] Public README links the record (public commit c31d363, 2026-09-18). The
      registered commit stays ced9fe2; later public commits do not alter the
      record, which would need a new version to cover them.
- [x] The first submission (85ddda8, provenance contradiction) was withdrawn by
      the user; it never registered.
- [x] Public repository presentation (commits c31d363, 5cc8c57): twelve topics,
      homepage set to the record permalink, CITATION.cff citing
      PALOMAR-2026-09-18-000007, README badges for build, record, toolchain and
      license. No Lean, Challenge, Solution, comparator or formalization.yaml
      change, so the registered artifact is untouched.
- [x] Obsolete todo, kept for history: "only after a passing preflight and an
      explicit user go, the actual Palomar submission". The user submitted and
      registered the entry on 2026-09-18 (above).
- (context, historical) First Palomar entry for Theorem 1 only (user decision 2026-09-16).
      Palomar limits (checked 2026-09-16, how-to-submit + PalomarPolicy
      CONTRIBUTING): Challenge hard limit 1,000 lines / 100 KiB, warning above
      300 lines / 32 KiB; repository ≤ 500 MiB; one repo/commit may carry
      several entries with separate configuration paths. Steps: draft an
      isolated Challenge with the five Theorem 1 statements (paper_sharp_bounds,
      paper_rotation_sharp, paper_full_sharp, paper_equality_classification,
      paper_family_converse) and only the definitions they need; Solution
      proving them from the library; comparator.json; formalization.yaml;
      static contract checks. Still no submission: Sprint 6 dry run first.
      (Superseded by the submission and registration recorded above.)
- [x] G09a-1 Ω_{K/ℂ} is free of rank one on dt, for every squarefree h and for
      the family (QuadraticDifferentials; commit introducing
      verification/differentials-rank.md). Base change along the two formally
      étale maps ℂ[t] → ℂ(t) → K; also the chain rule and 2w·dw = h'(t)·dt.
- [x] CI for G09a-1 commit f2b650d passed (run 35431502060; the Palomar
      Theorem 1 entry workflow, run 35431501962, also passed unchanged)
- [x] G09a-2a generic local lemma: for a local R-algebra whose residue field is
      generated by R and whose maximal ideal is (u), Ω[A⁄R] is generated by du,
      hence independent of the chosen u (LocalDifferentials, with the generic
      localization residue lemma). Nakayama plus Leibniz; no order, divisor or
      genus is defined. Note: verification/place-differentials.md.
- [x] G09a-2b the local ring at every point place is a DVR with residue field ℂ,
      so its differentials are generated by du for any uniformizer, and the
      submodule does not depend on the choice (PlaceDifferentials; commit
      introducing verification/place-differentials.md). The place at infinity
      still needs the same argument in the chart of G07b-3.
- [x] CI for G09a-2a/2b commit 8957029 passed (run 35432466431; the run on the
      intermediate commit 61c51e3 was cancelled by the concurrency group, and
      8957029 contains it). Palomar Theorem 1 entry build 35432466491 also passed.
- [x] G09a-2c at a point place: du spans the differentials of the function field
      over it, du ≠ 0, every differential is f·du, and two uniformizers give
      coefficients differing by a unit of the local ring — so an order at the
      place does not depend on the uniformizer (PlaceDifferentials, with the
      generic base-change span lemma in LocalDifferentials). The package was
      re-split here: infinity and the numerical values are 2d and 2e.
- [x] CI for G09a-2c commit 6b77f3e passed (run 35433426654; Palomar Theorem 1
      entry build 35433426677 also passed)
- [x] G09a-2d the place over t = ∞, through the chart isomorphism of G07b-3:
      it is upgraded to a ℂ-algebra isomorphism, and the preimage of a
      uniformizer of the conjugate family's point place (0,0) lies in the local
      ring at infinity with a nonzero spanning differential
      (InfinityDifferentials, with the generic transport lemma
      kaehler_span_D_equiv in LocalDifferentials). Not included: the
      coefficient-unit statement at infinity.
- [x] CI for G09a-2d commit 8411384 passed (run 35434427547; Palomar Theorem 1
      entry build 35434427573 also passed)
- [x] G09a-2e at an unramified point place (h(c) ≠ 0): t − c generates the
      maximal ideal and its differential is dt, so the coefficient of f·dt at
      that place is f itself — ord_v(dt) = 0 without a ℤ-valued order
      (PlaceUniformizers).
- [x] CI for G09a-2e commit a0ff4e7 passed (run 35435065432; Palomar Theorem 1
      entry build 35435065437 also passed)
- [x] G09a-2f the ramified point places: h(c) = 0 forces d = 0, w generates the
      maximal ideal (t − c = w²/k with k(c) ≠ 0 from squarefreeness), h'(t) is a
      unit there, and h'(t)·(f·dt) = (2·f·w)·dw, which is ord_v(dt) = 1
      (PlaceUniformizers).
- [x] CI for G09a-2f commit 2f2eba6 passed (run 35455600594; Palomar Theorem 1
      entry build 35455600604 also passed)
- [x] G09a-2g the value at ∞: through the chart isomorphism t ↦ 1/s, dt reads at
      the conjugate ramified place (0,0) as −2w'·dw' over s²·h'(s), with h'(s) a
      unit and s = w'²·(unit), i.e. ord(dt) = 1 − 4 = −3 (InfinityDifferentials).
- [x] G09b-1 regularity of a differential at a point place: definition free of
      uniformizer choices, plus the two criteria — f·dt is regular where
      h(c) ≠ 0 iff f is in the local ring, and where h(c) = 0 iff f·w is
      (HolomorphicDifferentials; verification/holomorphic-differentials.md).
- [x] G09b-2 regularity at the place over t = ∞, defined as regularity of the
      transported differential at the conjugate point place, with the closed
      form of the coefficient against w' (InfinityRegularity; the generic
      transport map kaehlerTransport is in LocalDifferentials).
- [x] CI: G09a-2g commit 8ef2b25 passed; G09b-1 commit 349973b was cancelled by
      the concurrency group; head commit ad40a51 (G09b-2) passed (run 35456966169,
      Palomar Theorem 1 entry build 35456966177), and contains both.
- [x] Lean v4.34.0 bump merged into codex/main (db011ac, reviewed; local reuse
      installation mathlib-v4.34.0-reuse; CI runs 35734028877, 35734028940).
- [x] G09b-3a the infinity criterion with units cancelled: f·dt is regular at ∞
      iff φ(f)/w'³ lies in the local ring of the conjugate place (0,0)
      (isRegularAtInfinity_iff_cube; helpers quadLocal_poly_unit,
      quadRoot_ne_zero).
- [x] G09b-3b the holomorphic differentials as a ℂ-subspace
      (holomorphicDifferentials in HolomorphicSpace): regular at every point
      place and at ∞, which by family_place_classification are all the places;
      isHolomorphic_smul_dt_iff lists the conditions on f for f·dt.
- [x] G09b-3c the t^i dt/w, i < m, are holomorphic (holoBasisVec_mem) and
      linearly independent over ℂ (holoBasisVec_linearIndependent), in
      HolomorphicBasis; so the space has dimension at least m.
- [x] G09b-3d-1 regular at every point place ⇒ f·w = a(t) + b(t)·w
      (quad_regular_points_coeff in HolomorphicSpan, via Mathlib's
      MaximalSpectrum.iInf_localization_eq_bot and quadRing_isMaximal_iff).
- [x] G09b-3d-2 at ∞, parity with the place's valuation: a/w gives valuation
      v(w')^(2m−2−2 deg a), b gives v(w')^(−2 deg b − 3); different parity, so
      the triple zero forces b = 0, deg a < m (holomorphic_coeff_form).
- [x] G09b-3d-3 the t^i dt/w span (holomorphicDifferentials_eq_span); basis
      holomorphicBasis; family_genus: finrank ℂ (holomorphicDifferentials) = m.
      GENUS m PROVED at the route-B reading (G09 genus half closed).
- [x] CI for the genus commit c4a1857 passed (run 35738686055; Palomar entry
      build 35738686071).
- [x] G09 remainder (the Riemann–Hurwitz degree identity as a divisor
      statement): NOT PURSUED, user decision 2026-09-28. Lemma 4's genus claim
      is proved with an explicit basis; the route difference is recorded in
      COVERAGE (G09) and goes into the TeX appendix.
- [x] User decisions 2026-09-28: R01 closes only with the quartic's genus
      exactly 3 (as Remark 5 prints); the Alcázar email is drafted now and sent
      by the user in parallel; a Theorem 2 Palomar entry is decided after the
      preprint.
- [x] L01 ledger refresh: SPRINTS, ONBOARDING, COVERAGE, STATUS, CHECKS, both
      READMEs and the private formalization.yaml brought up to the genus commit.
- [x] R01a intrinsic genus (FunctionFieldGenus, generic in K/ℂ): places are
      valuation subrings ≠ ⊤ containing ℂ (IsComplexPlace); regular at O = in
      the ℂ-span of the a·db with a, b ∈ O (regularAt; K-coefficients, avoiding
      the O-module diamond of G09a-2c); holomorphicSpace = regular at every
      place; genus = finrank ℂ. mem_regularAt_iff_of_generator (ω = f·du with
      f ∈ O when du generates), exists_D_eq_smul_of_span_eq_top, and invariance:
      kaehlerTransportEquiv, IsComplexPlace.comap,
      kaehlerTransport_mem_holomorphicSpace (automorphisms too),
      holomorphicSpaceEquiv, genus_congr. Note: verification/quartic-genus.md.
- [ ] R01b family bridge (FamilyGenus): the intrinsic space of
      QuadField (familyH m α) equals holomorphicDifferentials m α
      (family_place_classification; quadPlace and quadLocalRing agree by rfl);
      ℂ-algebra upgrade of the G07a isomorphism; genus of FamilyFunctionField = m.
- [ ] R01c-1 Kummer field ℂ(x)[y]/(yⁿ − f), f squarefree (KummerField):
      irreducibility by Eisenstein at a simple root plus Gauss; Ω = K·dx;
      n·yⁿ⁻¹·dy = f'(x)·dx; fermatNested 4 is the Kummer polynomial of 2 − x⁴.
- [ ] R01d quartic lower bound (FermatHolomorphic): dx/y³, x·dx/y³ and dx/y²
      are regular at every place (valuation-ring arguments, no classification)
      and independent over ℂ.
- [ ] R01f similarity ⇒ ℂ-algebra isomorphism of the function fields
      (shift/dilate, proportional_of_realLocus_subset); non-similarity of
      Re(z⁴) = 1 and the m = 2 family through genus (QuarticComparison).
- [ ] R01c-2 Kummer ring places (KummerPlaces): maximal ideals are the points
      (a, b), bⁿ = f(a); uniformizers x − a (f(a) ≠ 0) and y (f(a) = 0); DVR
      from a principal maximal ideal; Dedekind; DedekindPlaces instantiated.
- [ ] R01e quartic genus exactly 3 (FermatGenus): chart at infinity
      (x ↦ 1/s, y ↦ r/s, r⁴ = 2s⁴ − 1), F·y³ ∈ ℂ[x][y] at the affine places,
      isotypic split under y ↦ i·y, degree bound at one infinite place;
      endpoints paper_family_genus and paper_degree_four_scope in a new
      PaperRemarks module. Closes R01.
- (done) G07b-3 original plan, kept for reference:
      Refinement: the chart at infinity is the family with conj α,
      w'² = h_{conj α}(s), so transfer places along the ring iso. Plan: t ∉ O ⇒ s = 1/t ∈ O
      with s in O's maximal ideal. Use the chart s = 1/t, w' = w·s^(m+1):
      w'² = s·h̃(s), h̃(s) = s^(2m+1) h(1/s) = reversal of h, of degree 2m with
      h̃(0) = leading coeff of h ≠ 0 (h(0) = 0 since t ∣ h). s·h̃ is squarefree.
      Build a ring/field iso L ≅ QuadField (X·h̃) sending t ↦ 1/s, w ↦ w' /
      s^(m+1), then apply quad_finite_place_classification to X·h̃: places
      containing s with s in the center are the points (0, e), e² = 0·h̃(0),
      so exactly one place over ∞. Combine with G07b-2c for the full list.
      No need for Ostrowski: every valuation subring contains t or 1/t.
- (superseded 2026-09-29) The original plan lines for G08, G09a, G09b and R01
      were replaced by the entries above; G08 was proved at the fibre-count
      reading ("index two" is not formalized) and G09 at the route-B reading.
- [ ] Sprint 4 gate audit; tag sprint-4-complete (the tag push needs the
      user's word).
- [ ] Negative controls in private CI (Sprint 6 gate), then Sprint 7 TeX
      integration.
- [ ] Release, every step the user's: Alcázar's answer, arXiv, this
      repository public with a scrub, journal, Lean Zulip, Mathlib PRs.

## Remaining major work

Sprints 0–3 complete at their stated scopes.
Sprint 4: the function field, its places, the branch points and the genus m
are proved at the recorded readings (G07–G09). R01 remains: an intrinsic
genus, then the quartic's genus three (tracker). The Riemann–Hurwitz divisor
identity is not pursued (user, 2026-09-28). Mathlib still has no genus,
Riemann–Roch or Riemann–Hurwitz. Do not manufacture an invariant or weaken
the goal.

Sprint 5: accurate compact Challenge/Solution, permitted import closure,
Comparator configuration, schema-valid metadata, pinned tools and honest
literature/review status. Preserve inspected arXiv vs uninspected journal
version distinctions. Done and registered for Theorem 1; a Theorem 2 entry is
decided after the preprint.
Sprint 6: immutable clean private Linux contract-faithful dry run, protected
Comparator, isolated Challenge, credential/network-free proof sandbox,
NanoDa replay and failing negative controls. No simulated sandbox counts.
For Theorem 1, Palomar's own verifier passed on the public repository; the
negative controls are still to run, in private CI.
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

Run from the active repository. Lean: leanprover/lean4:v4.34.0.
Mathlib: 5ed2965256430c3649e86755f9576b54eca72435 (tag v4.34.0).
Reuse installation: /Users/carlo/Documents/varie/hacks/lean4/mathlib-v4.34.0-reuse
(dependency-only, pins copied from lake-manifest.json; never run `lake update` there).
The old v4.32 installation /Users/carlo/Documents/varie/hacks/lean4/diaz-modulus-lean no longer matches the pins.
Do not clone duplicate dependencies, modify their sources, or update pins.
Root lakefile.toml and lake-manifest.json describe the portable package.

```sh
rtk proxy sh lean/check.sh /Users/carlo/Documents/varie/hacks/lean4/mathlib-v4.34.0-reuse
rtk proxy python3 -B scripts/check_sources.py --reuse /Users/carlo/Documents/varie/hacks/lean4/mathlib-v4.34.0-reuse
rtk proxy python3 -B -m unittest discover -s scripts -p 'test_*.py'
rtk proxy git diff --check
```

For an incremental build, construct LEAN_PATH from this project's lean/.build
plus each installed dependency's .lake/build/lib/lean. Compile changed modules
in dependency order, then CurveSymmetry.lean, then verification/Audit.lean.
Use elan run leanprover/lean4:v4.34.0 lean -DwarningAsError=true.
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
