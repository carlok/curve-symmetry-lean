# Lean port: Theorem 1 and ambient four-form completeness checked

Date: 2026-09-06. All clauses of Theorem 1 are checked: both symmetry upper
bounds, finiteness, sharpness in every degree, the normalized equality
classification, and its converse. The endpoints start with real Cartesian
polynomials and count actual Mathlib Euclidean isometries. The direct subgroup
is also proved cyclic and identified with determinant `+1` of the real-linear
part. **The complete paper is not yet formalized. No Palomar dry run or
submission has occurred.**

## Exact formal scope

`BPoly` is Mathlib's `MvPolynomial (Fin 2) ℂ`. For such a polynomial `P`,

```text
realLocus P = { z : ℂ | P(z, conjugate(z)) = 0 }
```

The internal hypotheses are `Irreducible P`, total degree `d ≥ 2`, infinitely many
points in `realLocus P`, and exclusion of every circle, with arbitrary center
and positive radius. No smoothness or compactness is assumed.

The public endpoints in [PaperBounds.lean](PaperBounds.lean) instead take
`f : MvPolynomial (Fin 2) ℝ`. `GeometricallyIrreducible f` means irreducibility
after mapping its coefficients into `ℂ`, not merely real irreducibility.
`cartesianLocus f` evaluates `f` at `(z.re,z.im)`.

The coordinate substitution `x=(X+Y)/2`, `y=(X-Y)/(2i)` is proved invertible
and degree-preserving. The real zero sets agree. In the other direction, an
arbitrary irreducible complexified equation with infinite real locus descends,
after a nonzero scalar, to a real Cartesian equation without changing degree.
This also transfers the sharp examples, not just the upper bounds.

Internally, direct symmetries are pairs `(a,b)` for `z ↦ az+b`, and opposite
ones use `z ↦ a conjugate(z)+b`, with `‖a‖=1` and preservation of the entire
locus in both directions. Their disjoint sum is now proved equivalent to the
actual subgroup of `ℂ ≃ᵢ ℂ` preserving the set. Mazur–Ulam and Mathlib's complex
linear-isometry classification supply exhaustiveness. The direct subgroup's
affine description is separately proved equivalent to determinant `+1`.

| Paper-facing endpoint | Conclusion |
|---|---|
| `paper_sharp_bounds` | Both actual isometry subgroups are finite; the direct subgroup is cyclic; their cardinalities obey `max(d,2d-4)` and `2d`. |
| `paper_equality_classification` | In degree at least five, equality forces an explicit nonzero affine similarity onto `Re(z^m (‖z‖²+α))=0`, with `m=d-2`, `‖α‖=1`, and nonreal `α`. |
| `paper_rotation_sharp`, `paper_full_sharp` | Real geometrically irreducible Cartesian examples attain each bound in every degree. |
| `paper_family_converse` | Every displayed nonreal-parameter family with `m ≥ 3` has degree `m+2`, infinite noncircular real locus, and exactly `2m` direct isometries. |

| Checked endpoint | Conclusion |
|---|---|
| [`direct_euclidean_bound`](DirectBound.lean) | All direct symmetries form a finite type of cardinality at most `max(d, 2d-4)`. No center is assumed in advance. |
| [`full_euclidean_bound`](ReflectionBound.lean) | All symmetries of both orientations form a finite type of cardinality at most `2d`. |
| [`rotation_bound_sharp`](Sharpness.lean) | In every degree `d ≥ 2`, an irreducible polynomial with infinite noncircular real locus attains the rotation bound. |
| [`full_bound_sharp`](Sharpness.lean) | In every degree `d ≥ 2`, such a polynomial attains the full `2d` bound. |
| [`familyPolynomial_irreducible`](FamilyIrreducibility.lean) | `X^m(α+XY)+Y^m(conj(α)+XY)` is irreducible for `m ≥ 1` and nonreal `α`. Modulus one is not needed for this assertion. |
| [`family_point_of_norm`](FamilyRealLocus.lean) | That family's real locus meets every circle centered at zero; infinitude and exclusion of all circles follow. |
| [`family_degree`, `family_direct_card`](FamilyRotations.lean) | Its degree is `m+2`; for `m ≥ 2` it has exactly `2m` direct symmetries. For `m ≥ 3`, `family_no_opposite` excludes opposite Euclidean symmetries. |
| [`fermat_irreducible`](Fermat.lean), [`fermat_full_card`](Sharpness.lean) | `X^d+Y^d-2` is irreducible and supplies exactly `d` direct and `2d` total symmetries for `d ≥ 2`. |
| [`anti_four_normal_form`, `anti_real_normal_form`](RotationSupport.lean) | The high-order anti-invariant polynomial has four terms. [EqualityForm.lean](EqualityForm.lean) excludes degenerate coefficients and real ratios; [Normalization.lean](Normalization.lean) constructs the normalized similarity. |

## What removes the earlier assumptions

The first feasibility pass assumed non-radiality, non-homogeneity, and a
polynomial sign identity. The current main bounds derive what they need:

- [Elimination.lean](Elimination.lean) proves a cleared-denominator Bézout
  identity over a one-variable fraction field. Infinite real-locus containment
  then gives polynomial divisibility, and the degree condition gives
  proportionality. This is proved, not added as an axiom.
- [Irreducibility.lean](Irreducibility.lean) excludes the homogeneous endpoint
  and classifies irreducible radial equations. [RealLocus.lean](RealLocus.lean)
  turns an infinite radial locus into an actual circle.
- [GeometricRotation.lean](GeometricRotation.lean) derives the polynomial
  sign from a genuine zero-set rotation. Infinite real locus also forces
  symmetric support, so no separate coefficient-reality assumption is needed
  for this step.
- [Translation.lean](Translation.lean), [EuclideanCenter.lean](EuclideanCenter.lean),
  and [ChangeCenter.lean](ChangeCenter.lean) exclude translations, prove a
  common center, and justify shifting it without changing degree or
  irreducibility.
- [RotationGroup.lean](RotationGroup.lean) proves that the entire centered
  rotation group is finite and cyclic. Finite cardinalities are established
  before counting; the convention `Nat.card` equals zero on infinite types is
  not used to obtain a vacuous bound.
- [Reflection.lean](Reflection.lean) proves a reflection fixes the equation:
  any other scalar would put a whole line in the curve. The opposite part is
  equinumerous with the direct part when nonempty; this yields the full bound.
- [FamilyQuadratic.lean](FamilyQuadratic.lean) uses Eisenstein on the reversed
  strict-transform quadratic. [Blowup.lean](Blowup.lean) proves the injective
  substitution and the transfer back to the original equation, including
  exclusion of an exceptional coordinate factor.
- [RealEquation.lean](RealEquation.lean) constructs the scalar giving a real
  equation. [ExtremalClassification.lean](ExtremalClassification.lean) combines
  this with a primitive generator, nondegeneracy, and normalization, then
  restores the original center. No extra reality or centeredness hypothesis
  is left in the final classification.
- [CartesianCoordinates.lean](CartesianCoordinates.lean),
  [CartesianReal.lean](CartesianReal.lean), and
  [CartesianDescent.lean](CartesianDescent.lean) provide the coordinate and
  real-coefficient interfaces. [IsometryInterface.lean](IsometryInterface.lean)
  and [DirectIsometries.lean](DirectIsometries.lean) provide the actual groups.

The sharpness proofs count roots of unity for arbitrary degree; they are not
finite computational tests. They use the upper bounds and directly proved
examples, not the unported Möbius classification, so there is no circular
dependency through that classification.

## Checked ingredients for Theorem 2

- [FamilySingularities.lean](FamilySingularities.lean) uses Mathlib's formal
  partial derivatives. For the generic four-term equation, a nonzero
  coefficient determinant excludes singular points on the torus. With the
  nonzero low coefficients, the origin is the only affine Jacobian singularity
  for `m ≥ 2`. This applies to both diagonal chart equations.
- [FamilyCharts.lean](FamilyCharts.lean) verifies all three
  denominator-clearing identities, smoothness of the two mixed corners,
  the exact lowest homogeneous components, and separability of their
  tangent-direction polynomials. These are concrete local polynomial facts;
  their interface to the compactified curve is still pending.
- [FamilyTransport.lean](FamilyTransport.lean) proves the coefficient
  comparisons after a dilation or a denominator-cleared inversion. For unit
  parameters, proportionality forces scale one and identical parameters.
  The exact self-pullback tests are `c^(2m)=1` and `c^(2m)=conj(α)^2`.
  Exchanging coordinates conjugates the parameter, and the two conjugated
  pullbacks cannot be proportional when `α` is nonreal. These statements
  cover arbitrary positive `m`; they do not assume completeness of the four
  map types.
- [SphereGeometry.lean](SphereGeometry.lean) uses the standard one-point
  compactification and Mathlib's full invertible-matrix projective action.
  The family is defined by topological closure; the theorem that this adds
  exactly infinity is proved from closedness and noncompactness.
- [FamilyProjective.lean](FamilyProjective.lean) constructs the bihomogeneous
  product-projective zero locus, proves its independence of representatives,
  connects its four chart equations, and identifies its real diagonal with
  the actual spherical closure. Both arbitrary Möbius and anti-Möbius actions
  agree with the indicated product-projective actions on the real diagonal.
- [FamilyMobiusPullback.lean](FamilyMobiusPullback.lean) proves that arbitrary
  Möbius inclusion of spherical families forces polynomial divisibility of
  the denominator-cleared pullback. It handles poles on the curve and assumes
  no special matrix form.
- [FamilyBidegree.lean](FamilyBidegree.lean) strengthens this to **nonzero
  scalar proportionality**. It proves both separate affine degrees are exactly
  `m+1`, bounds the corresponding degrees of any matrix pullback, and rules
  out an identically zero pullback using density on the sphere.
- [FamilyGlobalTransport.lean](FamilyGlobalTransport.lean) extends the scalar
  identity to all homogeneous coordinates and proves that arbitrary Möbius
  or anti-Möbius spherical inclusion transports the entire constructed
  product-projective zero locus, including its boundary. One-sided inclusion
  therefore already gives exact spherical equivalence.
- [HomogeneousDifferential.lean](HomogeneousDifferential.lean) defines vanishing
  of the homogeneous equation and its complex differential using `HasFDerivAt`,
  proves independence from homogeneous representatives, and derives invariance
  under both orientations from actual spherical inclusion. No
  nondifferentiability default is used.
- [PolynomialDifferential.lean](PolynomialDifferential.lean) identifies formal
  partial derivatives with the actual differential in any finite coordinate
  space and proves equivalence with the existing chart-Jacobian predicate.
- [HomogeneousCharts.lean](HomogeneousCharts.lean) proves that the homogeneous
  differential condition is equivalent to its dehomogenized counterpart, using
  differentiable local normalization and nonzero denominators. It connects the
  affine, reciprocal, and mixed family equations to this condition.
- [FamilyGlobalSingularities.lean](FamilyGlobalSingularities.lean) gives the
  exact global Jacobian locus, handles the other mixed corner by factor
  exchange, derives preservation of `0,∞`, and proves both ambient completeness
  statements for `m ≥ 2`. These statements start from actual spherical
  containment, with no assumed map form or pair preservation.
- [MobiusPair.lean](MobiusPair.lean) proves the standard matrix reduction to
  dilation or inversion **if** the pair `0,∞` is preserved, including exact
  actions at zero and infinity. The required hypothesis is now derived in
  `family_mobius_preserves_pair` before this helper is applied.
- [AffineClosure.lean](AffineClosure.lean) proves that the real diagonal points
  generate exactly the principal vanishing ideal of an irreducible plane curve
  with infinite real locus. It gives the complex-point algebraic closure and
  the actual Zariski closure in Mathlib's affine prime spectrum. This is not
  yet the projective boundary-closure theorem.
- [ProjectiveBoundary.lean](ProjectiveBoundary.lean) identifies the complement
  of the standard affine chart on the curve as exactly `(∞,0)`, `(0,∞)`,
  and `(∞,∞)`. It isolates the next closure targets without assuming that any
  of them belongs to the required closure.

## Remaining proof obligations

1. **Sprint 2 is complete.** Arbitrary ambient completeness and G01's closure
   identification are proved using the uniquely characterized standard affine
   Zariski atlas. The whole projective curve is topologically irreducible.
   This is classical complex-point geometry, not a normalization construction.
2. **Sphere group and genus.** Establish the actual sphere actions, the
   dihedral group of order `4m`, and the complete holomorphic/antiholomorphic
   parameter-equivalence statements. The local tangent-cone data are checked,
   but the normalization and genus calculation are not. The Euclidean
   nonreflection result and the four pullback tests are not substitutes for
   a proof that no other anti-Möbius maps exist.
3. **Registry validation.** Only after the requested port, prepare and validate
   the registry contract, metadata, comparator, and clean pinned build. A
   successful local Lean build is not a Palomar dry run or acceptance result.

## Reuse the installed libraries

From the repository root on this machine:

```sh
rtk proxy sh lean/check.sh \
  /Users/carlo/Documents/varie/hacks/lean4/diaz-modulus-lean
```

On another machine, pass an existing populated Lake project with compiled
Mathlib and an installed matching toolchain. The script checks its toolchain
and all nine dependency checkout revisions against this project's committed
pins, then uses the compiled package directories through `LEAN_PATH`. It invokes
neither Lake nor a package fetch, and invokes `elan run` without `--install`.
Only this project's own module outputs go into the ignored `lean/.build/`.
No Mathlib checkout, library cache, or toolchain is duplicated.

Verification environment:

- Lean `leanprover/lean4:v4.34.0`.
- Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435` (tag `v4.34.0`).
- Existing Mathlib at
  `/Users/carlo/Documents/varie/hacks/lean4/diaz-modulus-lean/.lake/packages/mathlib`.

The script compiles all 68 mathematical modules and the aggregate import with
warnings treated as errors. In addition to the selected endpoint reports,
`verification/Audit.lean` checks every `CurveSymmetry` declaration, including
private names, against only `propext`, `Classical.choice`, and `Quot.sound`.
There are no intentional proof holes, added axioms, or
`native_decide` calls. This check reuses trusted local compiled dependencies;
it is not a clean rebuild of Mathlib itself.

The root TOML Lakefile, toolchain and exact manifest support a portable Lake
build. Private Linux CI checks a clean project checkout with the pinned upstream
dependency artifacts. See the [full coverage ledger](../COVERAGE.md) for the
supporting claims that still need interfaces or proofs; completion of Theorem 1
does not imply completion of every lemma and remark in its exposition.

The existing library checkouts and TeX are unchanged. Local kernel verification
does not certify novelty or replace the literature and independent-review
checks recorded in [the audit](../CHECKS.md).
