# Verification and literature audit

Date: 2026-09-06. Scope: `sharp_symmetry_bounds.tex` and its Lean port.

## Verdict and remaining limits

The mathematical statements have complete proofs in the note. A separate adversarial pass over those proofs and 2,082 exact symbolic/regression checks found no counterexample or remaining proof gap. These passes were performed by the same assistant, not by independent reviewers. They are not formal verification.

A subsequent [Lean port](lean/README.md) verifies all clauses of Theorem 1, including normalized equality classification and its converse. The public endpoints use real Cartesian polynomials and actual Euclidean isometry subgroups, with the direct subgroup identified by determinant `+1`. Proportionality, the sign identity, a common center, finiteness, and the example families' irreducibility are derived, not assumed. For Theorem 2, the affine and reciprocal Jacobian tests, mixed-corner smoothness, tangent-cone data, and exact coefficient tests for the four proposed forms are checked. The global passage from arbitrary Möbius equivalences to those forms, the sphere-group classification, and the normalization/genus assertions remain unported. This is not a fully checked paper or a Palomar dry run.

Update 2026-09-29: the Lean port has since advanced. Every clause of Theorem 2 is proved for actual ambient transformations, and Lemma 4's genus `m` is proved at the approved function-field reading, with an explicit basis instead of the note's Riemann–Hurwitz step. Remark 5's quartic comparison (R01) is not yet formalized. Theorem 1 alone, from a separate public repository, is registered with Palomar as `PALOMAR-2026-09-18-000007` after mechanical verification and an automated editorial review; that is neither a human review nor a novelty certificate. [STATUS.md](STATUS.md) and [COVERAGE.md](COVERAGE.md) carry the current scope.

The novelty gate is **provisional**: the coefficient method is known and explicitly credited; the sharp bounds and full ambient equality-case classification were not found in the checked sources. It would be unjustified to promise that no earlier source contains them. Before presenting this as new research, obtain a specialist duplicate-result check and inspect the unavailable journal/accepted version identified below.

## Statement lock

All degree bounds concern a polynomial `f` in `R[x,y]` that is irreducible in `C[x,y]`, has ordinary total degree `d >= 2`, and has infinitely many real zeros. A circle is excluded. Symmetry means preservation of the entire real zero set, not of one selected branch and not equality of polynomial values.

The first group is the ambient Euclidean isometry group; its direct subgroup includes the identity. Thus a curve with no nonidentity rotation has `N = 1`. The second theorem concerns Möbius and anti-Möbius maps of the ambient sphere preserving the spherical closure. It does not compute the full automorphism group of an abstract curve or its normalization.

The family is `Re(z^m (|z|^2 + alpha)) = 0`, where `m >= 2`, `|alpha| = 1`, and `alpha` is nonreal. Its ordinary degree is `m+2`; the bidegree of its complexification in `P1 x P1` is `(m+1,m+1)`; its normalization has genus `m`. These three numbers are not interchangeable.

The classification of *all* curves attaining the ordinary-degree rotation bound is restricted to `d >= 5`. The family theorem itself also holds for `m = 2`.

## What was retained from the earlier direction

The useful starting point from `p20_astra.tex` was the restriction imposed on monomial weights by a Möbius rotation, and the use of the conjugation-symmetric complexification in `P1 x P1`. The autonomous result here uses those ideas over arbitrary real coefficients, with no transcendental-point or algebraic-coefficient hypothesis.

The general finite Möbius-group bounds, orbit/descriptive-set-theoretic material, and semialgebraic algebraicity argument were not copied. They would broaden the paper and make its contribution less distinct. The familiar Cassini quartics were also dropped as a novelty candidate: Rigby's discussion already gives their order-eight inversive groups.

## Proof dependency graph

```text
Bézout + elementary Euclidean group identities
  -> finiteness, common rotation center, polynomial sign character (Lemma 3)
       -> every reflection fixes the polynomial
       -> positive-sign rotations have order <= d
       -> all Euclidean symmetries number <= 2d

Classical coefficient-weight criterion + irreducibility
  -> rotations with N > d have weights exactly +/-N/2
       -> N <= 2d-4
       -> equality forces four monomials and the normalized family

Quadratic blow-up chart + an odd valuation + Gauss's lemma
  -> geometric irreducibility (Lemma 4)
       -> two ordinary singularities and no others in P1 x P1
       -> every ambient equivalence preserves their unordered pair
       -> four possible map types
       -> exact group, absence of anti-Möbius maps, parameter classification (Theorem 2)
       -> sharp examples needed for Theorem 1
```

Theorem 1 cites Theorem 2 for examples, but the proof of Theorem 2 does not use Theorem 1. There is no circular sharpness argument. The genus calculation uses Riemann–Hurwitz and is not needed for the group bound.

## Adversarial checks

1. **Real zeros versus complex curves.** Infinitely many real points on a geometrically irreducible complex curve are Zariski dense. This justifies proportional polynomial equations and the extension of an ambient equivalence to the complexification. No finite or empty real locus is allowed.
2. **The sign cannot be discarded.** A finite-order symmetry gives `f o T = +/- f`. The quintic is negated by a 60-degree rotation. The proof treats the two signs separately.
3. **Why reflections have positive sign.** A negative-sign reflection forces `f` to vanish on its entire fixed line. Degree at least two and geometric irreducibility exclude this. In a group containing a reflection, every rotation is a product of two reflections, so all rotations have positive sign. This is the extra step that changes the general symmetry bound from the Bézout-based `4d` to `2d`.
4. **Noncompact curves and singularities.** Neither compactness nor nonsingularity is assumed. The extremal examples are unbounded and have a multiple point at their rotation center. Omitting singular curves would remove the main equality family.
5. **Irreducibility, not a numerical factor test.** In the chart `X = tY`, the strict transform is `A(t) + t D(t) Y^2`. The two coefficients are coprime; `-A/(tD)` has an odd pole at zero and cannot be a square in `C(t)`. Gauss and localization then prove irreducibility over `C`, not merely over `Q(i)`.
6. **No component lost in the chart.** The change of coordinates is an isomorphism after inverting `Y`; the original polynomial has no factor `Y`. Thus the irreducible strict transform implies irreducibility of the original polynomial. Coprimality rules out vertical components of the strict transform.
7. **All four boundary points.** The torus is smooth because `H_Y = 0` there would force `t^m = -1`, where `H` is nonzero. The two diagonal boundary points are ordinary `m`-fold singularities; the two mixed points are smooth. Explicit equations at the boundary are given in the paper.
8. **Möbius versus Euclidean equivalence.** Using the singular pair in `P1 x P1`, not just the visible plane curve, restricts all ambient Möbius/anti-Möbius maps to four forms. The coefficient-ratio test checks all four. Merely checking linear reflections would not establish the claimed absence of anti-Möbius symmetries.
9. **Exceptional parameters.** If `alpha = +/-1`, the equation factors as `(XY+alpha)(X^m+Y^m)`. These parameters are excluded. If `m = 1`, the distinguished points are not singular and the singular-pair argument is unavailable; the theorem excludes that case.
10. **Low degrees.** The rotation maximum is 2 in degree 2, 3 in degree 3, and 4 in degree 4. In degree 4 there are equality cases outside the displayed family, so the exhaustive classification starts at degree 5. `Re(z^d) = 1` supplies the sharp `2d` total-symmetry examples for every `d >= 2`.
11. **Reducible counterexamples to overgeneralization.** `Re(z^d) = 0` is a union of lines with `2d` rotations and `4d` isometries. It defeats both strengthened bounds without irreducibility. A circle has infinitely many symmetries.
12. **Algebraic coefficients.** The only arithmetic observation retained is immediate from the explicit group equations: if `alpha` is algebraic, the permitted `c` are algebraic. No unproved descent or effectivity assertion is used.
13. **Genus check by a second calculation.** Arithmetic genus in bidegree `(m+1,m+1)` is `m^2`. Subtracting the two ordinary-point contributions, each `m(m-1)/2`, gives `m`, agreeing with the double cover's `2m+2` branch points. The genus is that of the normalization, not the singular model.
14. **No claim to solve a problem in transcendence.** No Díaz input or conclusion is present. The standalone contribution is in plane-curve symmetry.

## Literature audit

The following comparisons concern inspected sources, not inferred contents of paywalled articles. Search-result crawl dates were not treated as publication dates.

### Closest coefficient work: already known, credited

- Peter Lebmeir and Jürgen Richter-Gebert, *Rotations, translations and symmetry detection for complexified curves*, CAGD 25 (2008), 707–719, [DOI](https://doi.org/10.1016/j.cagd.2008.09.004). Read the relevant Section 4, especially Theorem 8 and the paragraphs following it, in the [author manuscript](https://science-to-touch.com/Articles/jrg/53_VorauPaper.pdf), printed pp. 18–20. It already recovers rotation order as the gcd of differences of nonzero coefficient weights. It explicitly accounts for polynomial proportionality. This method is not ours. The sharp irreducible degree bound and the ambient Möbius equality classification were not found there.
- Peter Michael Lebmeir, *Feature Detection for Real Plane Algebraic Curves*, TUM thesis (2009), [repository PDF](https://mediatum.ub.tum.de/doc/681056/512338.pdf). Inspected Section 5.1.1–5.1.2, printed pp. 102–105, and the start of 5.1.3. Theorem 5.4 gives the same weight criterion. The full thesis text was searched for degree bounds, irreducibility, and rotational-symmetry terms; this was not a cover-to-cover review of its 150-plus pages. The proposed extremal classification was not found in the inspected material.

### Concrete comparisons

- János Pach and Frank de Zeeuw, *Distinct distances on algebraic curves in the plane*, [arXiv:1308.0177v3](https://arxiv.org/abs/1308.0177v3), 2014; [author-hosted PDF](https://www.math.tau.ac.il/~michas/pdz.pdf). Read Section 2.3, especially Lemma 2.6, printed p. 6: it bounds the full isometry group by `4d` using Bézout. Our `2d` estimate sharpens that lemma under the hypotheses stated in this note. The finiteness argument is credited background, not new. Improving this auxiliary constant is not an improvement of the distance exponent.
- Juan G. Alcázar, Miroslav Lávička and Jan Vršek, *Symmetries and similarities of planar algebraic curves using harmonic polynomials*, [arXiv:1801.09962v1](https://arxiv.org/abs/1801.09962v1), 2018. Read the definitions and sign lemma in Section 2 and Lemma 9 in Section 3, printed p. 6. Lemma 9 restricts the size of a preserved regular polygon to at most the ordinary curve degree. The irreducible quintic in the note has an element of order 6, which no Euclidean symmetry group of a regular polygon with 2–5 vertices contains. This is a counterexample to that specific version's statement.
- The preceding paper appeared in JCAM 357 (2019), 302–318, [DOI](https://doi.org/10.1016/j.cam.2019.02.036). Its institutional [repository record](https://ebuah.uah.es/dspace/handle/10017/58574) identifies an accepted manuscript, but attempted PDF access failed (403/cache miss). **The accepted and publisher versions were not inspected.** The TeX deliberately cites the arXiv statement only. Neither all results of that paper nor its implementations are declared incorrect. In particular, the effect on its algorithms has not been audited.

### Material excluded from the novelty claim

- John F. Rigby, *Inversive symmetry*, [article PDF](https://symmetry-us.com/Journals/1-1/rigby.pdf), Symmetry 1 (1990), 63–76: inspected the discussion of Cassinian ovals and order-eight inversive groups on p. 65. This disqualifies the earlier Cassini order-eight example as a novelty claim. It is not the family used here.
- Joel C. Langer and David A. Singer, *Orthogonal Families of Bicircular Quartics, Quadratic Differentials, and Edwards Normal Form*, [Axioms 12 (2023), 870](https://www.mdpi.com/2075-1680/12/9/870): inspected indexed text describing the self-inversion theorem for bicircular quartics. The direct page had an access/rate-limit failure; this is a partial check, not a complete paper review. The note does not claim new quartic inversion theory.
- Irina A. Kogan, Michael Ruddy and Cynthia Vinzant, *Differential signatures of algebraic curves*, [arXiv:1812.11388](https://arxiv.org/abs/1812.11388): abstract-level adjacent-work check only. Curve equivalence and symmetry are established topics; the present note does not claim a new general signature method or an implemented general equivalence algorithm.
- A publisher listing for Juan Gerardo Alcázar's *Symmetries of Algebraic Varieties in Two and Three Dimensions: A Computational Approach* has [copyright 2027](https://www.routledge.com/Symmetries-of-Algebraic-Varieties-in-Two-and-Three-Dimensions-A-Computational-Approach/Alcazar/p/book/9781041088202). Only its description and contents were available here, including a chapter on implicit planar curves. It remains a potentially relevant source to check when its text is available; a search-result date does not establish that the book's theorems were inspected.

### Searches and what they can establish

Queries included combinations of “real/irreducible algebraic curve”, “rotation order”, “symmetries”, “sharp”, “degree”, “2d-4”, “2d − 4”, “at most 2d”, “Möbius”, “chiral”, and the exact titles/authors above. These led to the coefficient literature, the thesis, and the two concrete comparisons. No matching sharp-bound plus Möbius equality-classification theorem was found.

This was a targeted web and source search, not a MathSciNet/zbMATH systematic review, author consultation, or exhaustive search of classical inversive-geometry literature. The strongest defensible claim is “not located in the checked sources,” not “proved unprecedented.” The bound proofs are short consequences of classical methods; a reviewer may regard them as elementary refinements. The full equality-case classification is the less immediate part of the note.

## Computation

`verify.py` ran successfully with SymPy 1.14.0, giving 2,082 exact checks:

| Category | Checks | Scope |
|---|---:|---|
| Quintic | 8 | Cartesian expansion, complexification, exact 60-degree sign, rotation order, degree |
| Weight support | 1,471 | Degrees 2–40, candidate orders above degree through `2d+2` |
| Equality support | 36 | Exactly four allowed monomials in degrees 5–40 |
| Geometry | 330 | Blow-up, degrees, coefficient gcd, odd pole, simple branch points, boundary charts |
| Rotation order | 33 | Exact gcd criterion for `m=2,...,12` and three algebraic parameters |
| Excluded parameters | 66 | Factorization at `alpha=+/-1` |
| Transport ratios | 32 | All four ambient map types for `m=2,...,9`, with symbolic coefficients |
| Group identities | 84 | Polynomial remainders verifying all permitted roots for `m=2,...,8` |
| Reflection sign | 22 | Exact odd-part/mirror-line identities |

No floating-point sampling is used. The algebraic root remainder checks test all roots of the specified equations, not just a chosen numerical root. Finite tests do not establish statements for arbitrary degree or parameters; those conclusions depend on the written proofs.

## Build and presentation

Completed checks:

- Lean verification on 2026-09-06: all 33 modules compiled with warnings treated as errors; all 85 endpoint axiom reports list only `propext`, `Classical.choice`, and `Quot.sound`. Source scanning found no proof holes, added axioms, unsafe declarations, or `native_decide` calls. The installed Lean 4.32.0 and Mathlib commit `81a5d257c8e410db227a6665ed08f64fea08e997` were reused; no dependency checkout or toolchain was copied or downloaded. The library checkouts retain exactly their pre-existing file-type changes. Theorem 1 is checked; Theorem 2's global and genus obligations remain as detailed in the Lean status.
- `latexmk -pdf -interaction=nonstopmode -halt-on-error`: success; final PDF is **four A4 pages**, 11pt, with one-inch margins. All references resolve.
- Final log search: no LaTeX warnings, undefined references, multiply defined labels, overfull boxes, or underfull boxes.
- `chktex -q`: exit 0, no diagnostics. Three local suppressions cover the two conventional declaration lines and the correct Riemann–Hurwitz en dash; no mathematical-content warnings are hidden globally.
- All four PDF pages were rendered and visually inspected for clipped equations, overbars, reference rendering, and page flow. No layout defect requiring a change was found.
- A deterministic prose-only `unslop` pass protected the mathematics, TeX syntax, and bibliography. Two transition words were removed; an automatic lowercase sentence start was corrected manually. The final pass, with 346 protected spans, reported an empty diff. This was stylistic checking only.
- A final theorem-wording check made the spherical closure explicit in the full Möbius-group statement: `c/z` sends zero to infinity and must not be described as a self-map of the affine real locus alone.
- The only new workspace subtree is `curve_symmetry/`. No existing tracked file was changed by this task; the pre-existing dirty/untracked state was preserved. No git staging, commit, push, or external communication occurred.
- SHA-256 checks match the values recorded before this task:

```text
dcbd80d9d3de369717784dfc8c7729d18f8e2b94766d011becff83ba37f95072  p20.tex
f5efbe7773c9cd5e96a0eb200564fbc21fba8a1ca248b45fae6f5076c646c710  p20_astra.tex
```

## Before making a public novelty claim

- Inspect the accepted and published ALV version and check for corrections; do not silently promote the arXiv counterexample into a journal-error claim.
- Ask a specialist in plane-curve symmetry to look for an existing sharp-degree/equality theorem, especially in classical inversive-geometry and curve-recognition literature.
- Obtain an independent mathematical review of the normalization/localization step and the completeness of the ambient group classification. The current checker shares the author's derivation.
- Continue the Lean development with the global Möbius completeness argument, actual sphere actions and group classification, and normalization/genus. Theorem 1 now checks in full; Theorem 2 does not. Its local chart and four-form coefficient calculations have been checked without assuming that the four forms exhaust arbitrary Möbius equivalences. No registry validation has run. (2026-09-06 text. Since then Theorem 2 and the genus are proved and Theorem 1 is registered; see the update above. What remains of this item is R01.)
- Private email to Alcázar, Lávička and Vršek (user decision 2026-09-28): drafted outside this repository and sent by the user. It covers the first two items: the Lemma 9 counterexample and whether the bound is known.
