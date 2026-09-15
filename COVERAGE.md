# Mathematical coverage ledger

Paper: `sharp_symmetry_bounds.tex`, SHA-256
`3aff1c6edf6f189de6fa56c690631c266364a3b129408eb0fd5a200ceb186925`.
Inventory date: 2026-09-06. The TeX has not been edited for formalization.
All declaration names below are in `CurveSymmetry`; links point to their modules.

**Proved** means the stated mathematical claim has checked declarations using
the meanings below. **Partial** means only named ingredients are proved, not
the advertised global statement. **Open** is a remaining formalization
obligation, not a claim that the mathematical statement is an open problem.
No open obligation is a hypothesis supplied to the public Theorem 1 endpoints.
The abstract repeats the two main theorems and inherits their statuses.

## Statement vocabulary and fidelity boundary

| Meaning in the paper | Formal meaning / required interface |
|---|---|
| Real plane polynomial and its curve | `RPoly = MvPolynomial (Fin 2) ℝ`; `cartesianLocus` evaluates at the actual real and imaginary parts of `z : ℂ`. |
| Geometric irreducibility | `GeometricallyIrreducible f` is irreducibility of the coefficient extension to `ℂ`, not just real irreducibility. |
| Degree | Mathlib polynomial `totalDegree`; coordinate-change invariance is proved. |
| Euclidean symmetry / direct symmetry | Actual subgroups of `ℂ ≃ᵢ ℂ` preserving the locus; directness agrees with real-linear determinant `+1`. These are not merely coefficient stabilizers. |
| Noncircle | Exclusion of every `Metric.sphere c R` with `R > 0`, not just centered circles. |
| Extremal family | `extremalCurve m α = {z : ℂ | (z^m * ((‖z‖ : ℂ)^2 + α)).re = 0}`; `family_locus_eq` connects the polynomial. |
| Nonreal normalized parameter | `α ≠ star α` and `‖α‖ = 1`; theorems needing neither normalization nor the stronger degree cutoff say so explicitly. |
| Ambient Möbius action | **Proved interface:** `MobiusMatrix` is Mathlib's full `GL(2,ℂ)`, acting on `Sphere = OnePoint ℂ`; `sphereProjectiveEquiv_action` connects the standard projectivization action. Finite/pole/infinity formulas are checked. No projective-topology homeomorphism is asserted; the sphere itself has its standard topology. |
| Spherical closure | **Proved:** `sphericalFamily` is the actual topological closure. `sphericalFamily_eq` proves it gains exactly infinity; `sphericalFamily_projective_iff` identifies it with the real diagonal of the projective zero locus. |
| Compactified complex curve | **Proved at the classical complex-point level:** `familyProjectiveCurve` is the bihomogeneous zero locus and Zariski closure in the unique topology making the four standard affine-Zariski charts open embeddings. Global topological irreducibility is proved. This is not a scheme/normalization construction; geometric multiplicities and genus remain separate. |
| Geometric genus | **Pending:** genus of the genuine smooth normalization (or a proved equivalent invariant). A defined branch-count expression is not a substitute. |

## Principal claims

| ID | Paper claim | Status and checked endpoint / obligation | Sprint |
|---|---|---|---|
| T1.1 | Both actual groups finite; direct group cyclic; bounds `max(d,2d−4)` and `2d` | **Proved:** [`paper_sharp_bounds`](lean/PaperBounds.lean), including all geometry hypotheses. | baseline |
| T1.2 | Each bound attained in every degree `d ≥ 2` | **Proved:** `paper_rotation_sharp`, `paper_full_sharp` in [PaperBounds](lean/PaperBounds.lean). | baseline |
| T1.3 | Degree `d ≥ 5` equality implies the normalized family under orientation-preserving similarity | **Proved:** `paper_equality_classification`; the actual image of the Cartesian locus is the stated real-part equation. | baseline |
| T1.4 | Every family member with `m ≥ 3` attains the rotation bound | **Proved:** `paper_family_converse` (even without modulus-one normalization). | baseline |
| T2.1 | For `m ≥ 2`, the family is infinite, geometrically irreducible, of degree `m+2` | **Proved:** `paper_family_geometry` in [PaperFamilyGeometry](lean/PaperFamilyGeometry.lean) provides one real Cartesian equation with all these properties and its exact family locus, including `m=2`. Any nonreal parameter is allowed; modulus-one normalization is unnecessary. | 3 |
| T2.2 | Every ambient holomorphic equivalence has form `cz` or `c/z`; every anti-equivalence has a conjugated form | **Proved:** `family_mobius_complete` and `family_anti_mobius_complete` in [FamilyGlobalSingularities](lean/FamilyGlobalSingularities.lean), for `m ≥ 2` and nonreal parameters, starting even from one-sided actual spherical containment. The forms hold at every sphere point. Pair preservation follows from the global Jacobian locus and is not an input hypothesis. | 2 |
| T2.3 | Exact self-map coefficients `c^(2m)=1` or `c^(2m)=conj(α)^2` | **Proved:** `family_mobius_self_filter` in [FamilySphereClassification](lean/FamilySphereClassification.lean) covers arbitrary ambient matrices. [FamilySphereDilation](lean/FamilySphereDilation.lean) and [FamilySphereInversion](lean/FamilySphereInversion.lean) give exact actual-sphere tests, including `0,∞`; `family_mobius_self_mem_iff` proves preservation in both directions. | 3 |
| T2.4 | All self-equivalences holomorphic; no anti-Möbius symmetry | **Proved:** `family_no_anti_mobius_self` in [FamilySphereClassification](lean/FamilySphereClassification.lean) excludes even one-sided anti-Möbius self-inclusion, for every ambient matrix and `m ≥ 2`. | 3 |
| T2.5 | Full ambient group is dihedral of order `4m` | **Proved:** `familyAmbientGroup_dihedral`, `familyAmbientGroup_card`, and `familyAmbientGroup_generators` in [FamilyDihedral](lean/FamilyDihedral.lean). The independently defined actual sphere group is isomorphic to `DihedralGroup (2*m)`; generators have orders `2m` and `2`, satisfy the conjugation relation, and exhaust all elements. T2.4 excludes anti-Möbius additions. Includes `m=2`. | 3 |
| T2.6 | Full Euclidean group consists of exactly the `2m` rotations | **Proved:** `family_affine_self_filter` eliminates translation; `family_isometry_iff_rotation` characterizes actual self-isometries as precisely the root rotations; `family_isometry_card` gives order `2m`. All hold for normalized nonreal parameters and every `m ≥ 2`. See [FamilyEuclidean](lean/FamilyEuclidean.lean). | 3 |
| T2.7 | Fixed-`m` holomorphic equivalence iff `β=α`; anti-equivalence iff `β=conj(α)` | **Proved:** `family_mobius_equivalence_iff` and `family_anti_mobius_equivalence_iff` in [FamilySphereClassification](lean/FamilySphereClassification.lean) use existential ambient matrices and equality of the actual spherical images. Necessity follows even from inclusion; identity and conjugation provide sufficiency. Both normalized parameters are nonreal and `m ≥ 2`. | 3 |

## Supporting geometry and proof claims

| ID | Claim | Status and evidence / remaining obligation | Sprint |
|---|---|---|---|
| S01 | Infinite real locus forces polynomial divisibility/proportionality | **Proved:** [Elimination](lean/Elimination.lean), via a cleared-denominator Bézout argument. This is the affine density interface, not yet projective transport. | baseline |
| S02 | No nonzero translations; direct maps have a common center | **Proved:** [Translation](lean/Translation.lean), [EuclideanCenter](lean/EuclideanCenter.lean), [ChangeCenter](lean/ChangeCenter.lean). | baseline |
| S03 | No nontrivial glide reflection; opposite symmetries have index two when present | **Proved:** `opposite_symmetry_no_glide` (the square of an opposite symmetry is the zero translation) and `opposite_symmetry_fixed_point` (every opposite symmetry fixes `b/2`, so it is a reflection in a line) in [IsometrySign](lean/IsometrySign.lean); `oppositeDirectEquiv` in [EuclideanParameters](lean/EuclideanParameters.lean) gives the index-two bijection. | 4 |
| S04 | Lemma 3: every actual isometry has real polynomial multiplier `±1`; every reflection fixes the equation | **Proved:** `paper_isometry_sign` in [IsometrySign](lean/IsometrySign.lean): for a geometrically irreducible real Cartesian `f` of degree at least two with infinite zero set, every actual isometry `T` preserving the zero set satisfies `f(T z) = ε f(z)` at every point, with `ε = ±1`, and `ε = 1` for every orientation-reversing `T`. Complex form: `isometry_sign_of_realLocus`. Translations and glide reflections are eliminated, then the centered rotation and reflection results apply after moving the fixed point to the origin. Finiteness and cyclicity were already proved in `paper_sharp_bounds`. The identity is between polynomial functions on the real plane. | 4 |
| S05 | Complex Cartesian substitution, conjugate coefficient symmetry, weight identity | **Proved:** [CartesianCoordinates](lean/CartesianCoordinates.lean), [CartesianReal](lean/CartesianReal.lean), [RealEquation](lean/RealEquation.lean), [GeometricRotation](lean/GeometricRotation.lean). | baseline |
| S06 | Irreducible radial equation with infinite real locus defines a circle; homogeneous binary endpoint impossible | **Proved:** [Irreducibility](lean/Irreducibility.lean), [RealLocus](lean/RealLocus.lean). | baseline |
| S07 | High-order negative multiplier forces weights `±m`, the radial-polynomial form in equation (5), and its degree restriction | **Proved:** `anti_support` in [RotationSupport](lean/RotationSupport.lean) gives the weights. [RadialAntiForm](lean/RadialAntiForm.lean) proves `anti_radial_form` (`P = X^m A(XY) + Y^m B(XY)` with both degrees at most `⌊(d-m)/2⌋`) and `irreducible_anti_radial_form` (conjugate coefficients give `B = conj A`, `A` is nonconstant, so `m+2 ≤ d`). `paper_high_order_radial_form` starts from a real Cartesian curve with a rotation of order `N > d` and derives `N = 2m`, the sign `-1`, and equation (5) with its degree bounds. | 4 |
| S08 | Nondegeneracy and nonreal ratio in the equality case; normalized nonzero similarity | **Proved:** [EqualityForm](lean/EqualityForm.lean), [Normalization](lean/Normalization.lean), [ExtremalClassification](lean/ExtremalClassification.lean). | baseline |
| S09 | Fermat examples irreducible and infinite, with exactly `d` direct and `2d` total isometries | **Proved:** [Fermat](lean/Fermat.lean), [Sharpness](lean/Sharpness.lean), [CartesianDescent](lean/CartesianDescent.lean). | baseline |
| S10 | Printed quintic Cartesian expansion, negative sign at a 60-degree rotation, exact order six | **Proved explicit calculation:** [QuinticExample](lean/QuinticExample.lean) has `quinticValue_eq`, `quintic_sixtyDegree_negates`, `sixtyDegree_isometry_order` (actual Euclidean rotation), and `quintic_isometry_count`. `quintic_locus_eq` connects the displayed expression to the existing family results. | 4 |
| G01 | Bidegree `(m+1,m+1)` and the bihomogeneous closure | **Proved, classical complex-point interpretation:** [FamilyProjective](lean/FamilyProjective.lean) gives the representative-independent equation and block scaling; `family_degreeOf` proves both exact degrees. [ProjectiveAtlasClosure](lean/ProjectiveAtlasClosure.lean) proves the complex-affine and real-diagonal closures including all boundary points. [ProjectiveAtlasUniqueness](lean/ProjectiveAtlasUniqueness.lean) characterizes the topology uniquely by the four standard affine-Zariski open embeddings. [ProjectiveCurveIrreducibility](lean/ProjectiveCurveIrreducibility.lean) proves the full curve topologically irreducible. No scheme-theoretic intersection or normalization invariant is substituted for genus. | 2 |
| G02 | Strict transform `H(t,Y)`; coprime coefficients; irreducibility descends | **Proved:** [FamilyQuadratic](lean/FamilyQuadratic.lean), [Blowup](lean/Blowup.lean), [FamilyIrreducibility](lean/FamilyIrreducibility.lean). Eisenstein replaces the paper's rational-function nonsquare argument for irreducibility. | baseline |
| G03 | Only affine Jacobian singularity is the origin; same at the reciprocal chart | **Proved:** [FamilySingularities](lean/FamilySingularities.lean), using formal partial derivatives. | baseline |
| G04 | Three denominator-clearing chart identities; mixed corners nonsingular | **Proved:** [FamilyCharts](lean/FamilyCharts.lean) and [FamilyProjective](lean/FamilyProjective.lean) give the equations. [PolynomialDifferential](lean/PolynomialDifferential.lean) identifies formal partial derivatives with the analytic differential; [HomogeneousCharts](lean/HomogeneousCharts.lean) proves local-normalization compatibility, including the reciprocal and mixed charts. Factor exchange covers the other mixed corner. | 2 |
| G05 | Singular pair exactly `(0,0),(∞,∞)` on the global curve | **Proved for the ordinary chart-Jacobian condition on the constructed projective zero locus:** `family_projective_critical_eq_pair` in [FamilyGlobalSingularities](lean/FamilyGlobalSingularities.lean). The predicate is representative-independent and its chart interpretation is proved, not defined to select the two points. G01's closure identification and G06's geometric multiplicity assertion remain separate. | 2 |
| G06 | Both points ordinary `m`-fold, with the displayed tangent cones and `m` distinct tangent directions | **Proved, standard-chart algebraic multiplicity:** `family_ordinary_multiple_points` in [OrdinaryMultiplePoints](lean/OrdinaryMultiplePoints.lean), for `m ≥ 2` and nonreal `α`. Multiplicity is the usual maximal-ideal order (`HasMultiplicityAt`); `OrdinaryAtOrigin` requires multiplicity `n` and a degree-`n` component equal to a nonzero multiple of `n` pairwise nonproportional linear forms. The affine origin `(0,0)` and reciprocal origin `(∞,∞)` are ordinary `m`-fold; every other zero of those two chart equations, and every zero of both mixed chart equations, has multiplicity one. The cones are the displayed forms by `fourTermForm_tangent_data` in [FamilyCharts](lean/FamilyCharts.lean); [BinaryTangentDirections](lean/BinaryTangentDirections.lean) counts their `m` projective directions. Each singular point lies in exactly one standard chart. Invariance of multiplicity under nonlinear chart transitions or ambient automorphisms is not claimed. | 4 |
| G07 | Normalization is the quadratic function-field/double-cover model | **Open:** actual normalization/birational identification; polynomial irreducibility does not supply this by itself. | 4 |
| G08 | Cover has exactly `2m+2` simple branch points, including `0,∞`; defining rational function is not a square | **Partial:** coefficient coprimality and polynomial separability are available. Valuations, ramification, the degree-two map, and all branch cases remain. | 4 |
| G09 | Riemann–Hurwitz for that cover and geometric genus `m` | **Open:** prove missing foundations, not an assumed formula or numerical genus definition. | 4 |
| G10 | Every positive-radius circle meets the family in exactly `2m` points | **Proved:** `family_metric_circle_card` in [FamilyCircleSections](lean/FamilyCircleSections.lean) counts the actual centered metric-circle intersection. `familyCircleRootEquiv` identifies it with the `2m` roots of unity acting on any chosen point: a single free rotation orbit. Assumptions are only `m>0`, nonreal `α`, and positive radius; no modulus-one normalization. | 4 |
| G11 | Equivalence of spherical real loci induces the product-projective complex equivalence | **Proved for the constructed bihomogeneous zero loci:** `family_mobius_complex_transport` and `family_anti_mobius_complex_transport` in [FamilyGlobalTransport](lean/FamilyGlobalTransport.lean) cover all projective points, including boundary charts, starting even from one-sided spherical inclusion. The affine scalar identity extends to homogeneous coordinates by polynomial continuity on complex vector spaces; no unproved topology on projectivization is used. G01's Zariski-closure identification remains separate. | 2 |
| G12 | Coefficient ratios in the four cases force scale one and the parameter tests | **Proved polynomial calculations:** [FamilyTransport](lean/FamilyTransport.lean). Their sphere-action application is T2.2–T2.7, not already proved by the calculation. | baseline, 3 |
| G13 | Dihedral generators and relations; only the first map family is Euclidean | **Proved:** [FamilyDihedral](lean/FamilyDihedral.lean) gives generators, relations and actual sphere actions; `family_isometry_iff_rotation` in [FamilyEuclidean](lean/FamilyEuclidean.lean) identifies exactly the Euclidean maps. | 3 |

## Substantive remarks and scope

| ID | Claim | Status / obligation | Sprint |
|---|---|---|---|
| R01 | The degree-four Fermat example is not similar to the `m=2` family, by genera three versus two | **Open:** genuine genus calculations for both normalizations and invariance under the relevant equivalence. Equality of their rotation counts is already proved. | 4 |
| R02 | Parameters `exp(iθ)`, `0<θ<π`, give pairwise full-Möbius-inequivalent curves at fixed `m` | **Proved:** `family_arc_equivalence_iff` in [FamilyParameterArc](lean/FamilyParameterArc.lean) states that existence of either parity of actual spherical equivalence is equivalent to equality of angles, for `m>=2`. Norm, nonreality, injectivity and conjugation exclusion are proved. | 3 |
| R03 | Algebraic `α` implies algebraic coefficients for every map in the full ambient group | **Proved:** `familyAmbientGroup_algebraic_representative` in [FamilyAlgebraic](lean/FamilyAlgebraic.lean) gives an actual GL(2,C) representative with entries algebraic over Q, inducing the same sphere action. Normal-form coefficients are algebraic by the two power equations. Arbitrary scalar rescalings are not asserted algebraic. | 3 |
| R04 | The results concern ambient transformations, not every normalization automorphism; nonexistence of anti-Möbius maps does not deny a real structure | Scope restriction, not a new theorem. Do not replace the actual ambient action with an abstract curve automorphism group. | fidelity audit |
| R05 | Exclusions of `m=1`, real `α`, and low-degree equality classification | Retain the printed restrictions; a theorem under the weaker restrictions is not advertised. Degree-four comparison is R01. | fidelity audit |

Literature comparisons, version qualifications, novelty searches, and the
claimed usefulness of a sharper auxiliary constant are not kernel-checkable
historical claims. Their evidence remains in [CHECKS.md](CHECKS.md) and requires
the Sprint 5 editorial audit. The arXiv version of Alcázar–Lávička–Vršek was
inspected; the journal version was not. No independent human review or novelty
certification is claimed.

## Verification and updates

The starting checkpoint is 33 mathematical modules / 85 selected axiom reports.
Sprint 1 adds an aggregate import and an audit of every declaration in the
`CurveSymmetry` namespace, including private names, against exactly `propext`,
`Classical.choice`, `Quot.sound`. This checks proof dependencies; it does not
by itself validate the statement ledger, missing geometry, or novelty.

Every sprint must update the affected rows and record checks and commits in
[SPRINTS.md](SPRINTS.md). A partial row stays partial until its full claim is
proved with the stated ordinary meaning. Completed T1 rows do not compensate
for incomplete T2 or genus rows.

Sprint 2 adds thirty-one mathematical modules, for 65 Lean files including
the aggregate at its completion. Sprint 3 now adds four modules (69 files total).
T2.2 is now proved because pair preservation has been derived
from actual spherical containment, not because the earlier conditional helper
was relabeled. G01 is now proved via the classical affine-atlas construction.
The paragraphs below record the route, not remaining chart obligations. Sprints 4–7 and the full-port objective are
unchanged.

Next G01 target: [ProjectiveBoundary](lean/ProjectiveBoundary.lean) proves
that the constructed curve is its affine part plus exactly `(∞,0)`, `(0,∞)`,
and `(∞,∞)`. [MixedCornerClosure](lean/MixedCornerClosure.lean) proves that the
mixed-chart origin is in the Zariski closure of actual complex evaluation
points with nonzero first coordinate. It uses Mathlib's prime spectrum and
Jacobson topology, not a replacement definition of closure.
[ReciprocalCornerClosure](lean/ReciprocalCornerClosure.lean) now proves density
of complex points with both coordinates nonzero in the reciprocal chart,
including its origin `(∞,∞)`. [OtherMixedCornerClosure](lean/OtherMixedCornerClosure.lean)
identifies the image of original affine points under `(X,Y) ↦ (1/Y,X)` with
the punctured second mixed chart and proves closure membership of its origin
`(0,∞)`. [AffineChartImages](lean/AffineChartImages.lean) supplies the analogous
original-point image and closure identities for the first mixed and reciprocal
charts. Thus all three boundary charts have closure descriptions sourced from
original affine points. [ProjectiveChartMaps](lean/ProjectiveChartMaps.lean)
now gives their standard homogeneous chart maps, affine-overlap identities,
curve-equation interfaces, and exact boundary origins. G01 stays partial:
the projective Zariski-topology/gluing interface remains. Chart injectivity
and a four-chart cover are now proved in `ProjectiveChartMaps`, as are exact
range descriptions by zero/infinity coordinate exclusions.
[AffineZariskiTopology](lean/AffineZariskiTopology.lean) equips complex coordinate
points with the topology induced from the prime spectrum, proves the evaluation
map is an embedding, proves polynomial nonvanishing sets open, and verifies
the usual vanishing-ideal closure formula. Its instance is local: no Euclidean
topology is overwritten. [PolynomialZariskiMaps](lean/PolynomialZariskiMaps.lean)
proves the substitution identity and continuity of polynomial coordinate maps.
[CoordinateExchange](lean/CoordinateExchange.lean) proves coordinate-swap
homeomorphisms of the plane and torus, with the corresponding projective factor
identities. With explicit approval, [InversionDenominators](lean/InversionDenominators.lean)
and [InversionContinuity](lean/InversionContinuity.lean) are restored and prove
denominator clearing and the individual inversion homeomorphisms on nonzero
coordinate domains. [SimultaneousInversion](lean/SimultaneousInversion.lean)
proves the torus homeomorphism and reciprocal-chart compatibility.
[ProjectiveClosureGluing](lean/ProjectiveClosureGluing.lean) proves chartwise
minimal closed containment and an ambient closure theorem conditional on
four continuous charts and closedness of the projective family. G01 remains
partial: [ProjectiveAtlasTopology](lean/ProjectiveAtlasTopology.lean) now supplies
the family-independent final topology of the four affine Zariski charts and
proves their continuity. [ProjectiveAtlasClosure](lean/ProjectiveAtlasClosure.lean)
proves the exact closure of both the complex affine curve and (for nonreal
parameters) its real diagonal in that topology. Identifying this construction
with standard projective Zariski geometry remains.
[ProjectiveAtlasOpenCover](lean/ProjectiveAtlasOpenCover.lean) now proves exact
affine-overlap domains and an open four-chart cover, checking all sixteen
overlap sets. [ProjectiveAffineEmbedding](lean/ProjectiveAffineEmbedding.lean)
proves the affine chart is an open embedding using the inversion transitions.
[ProjectiveAtlasEmbeddings](lean/ProjectiveAtlasEmbeddings.lean) now proves the
other three open embeddings by homogeneous-coordinate flip and factor-exchange
homeomorphisms. `projectiveChart_isOpenEmbedding` covers all four charts.
[ProjectiveAtlasUniqueness](lean/ProjectiveAtlasUniqueness.lean) completes the
atlas characterization: this is the unique topology making all four standard
affine-Zariski charts open embeddings. This supplies the classical Zariski
interpretation of the paper's closure assertion, without assuming any curve
closed or any density statement. [ProjectiveCurveIrreducibility](lean/ProjectiveCurveIrreducibility.lean)
also proves global topological irreducibility. G01 is complete at that ordinary
complex-point scope; a separate scheme-theoretic comparison is not claimed.
