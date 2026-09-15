# Genus scope study (G07–G09, R01) — 2026-09-15

Scope study only: no Lean declarations were added. Purpose: choose an
honest meaning for "normalization" and "genus" before any genus package, and
split the remaining Sprint 4 rows into bounded packages.

## Paper obligations

- Lemma 4: the normalization of `V_α ⊂ P¹×P¹` has genus `m`.
- Its proof: with `X = tY`, the strict transform
  `H(t,Y) = (α t^m + conj α) + t(t^m+1) Y²` is a double cover of the
  `t`-line with `2m+2` simple branch points, including `0` and `∞`;
  Riemann–Hurwitz gives `2g−2 = −4 + (2m+2)`.
- Remark (R01): `Re(z^4)=1` is not similar to the `m=2` family because its
  normalization has genus three rather than two.

## Inventory of the pinned Mathlib (`81a5d25`)

Available and relevant:

| Area | Declarations / files |
|---|---|
| Function fields | `FunctionField F K` (finite extension of `RatFunc F`), `FunctionField.ringOfIntegers` in NumberTheory/FunctionField |
| Places of `ℂ(t)` | `RatFunc.valuation_isEquiv_infty_or_adic` (Ostrowski for `K(X)`: every discrete valuation trivial on `K` is adic at a height-one prime or at infinity); `RatFunc.inftyValuation` |
| Dedekind theory | `integralClosure.isDedekindDomain`, `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain`, AdicValuation |
| Ramification | `Ideal.ramificationIdx`, `Ideal.inertiaDeg`, `Ideal.sum_ramification_inertia`; KummerDedekind factorization |
| Different | `differentIdeal`, `not_dvd_differentIdeal_iff` (unramified primes), `conductor_mul_differentIdeal` |
| Valuation rings | `LocalSubring.exists_le_valuationSubring`, Valuation/Extension |
| Differentials | `KaehlerDifferential` (`Ω[S⁄R]`), polynomial and MvPolynomial bases |
| Local expansions | `LaurentSeriesRingEquiv` (completion of `RatFunc` at `X`) |
| Integral closure | `IsIntegrallyClosed.of_localization_maximal` |
| Schemes | relative `Scheme.Hom.normalization`, `Scheme.ord` (order of vanishing at codimension-one points), `Scheme.functionField` |

Searched and absent: any genus (arithmetic, geometric or topological),
Riemann–Roch, Riemann–Hurwitz, Weil or Cartier divisors on curves, canonical
divisors, adeles/répartitions of function fields, cohomology dimensions of
coherent sheaves, orders of differentials at places, the rank of `Ω_{K/ℂ}` for
a transcendence-degree-one field, integral closedness of `ℂ[t,w]/(w²−h)` for
squarefree `h`, and classification of places of a finite extension of `ℂ(t)`.

## Options for a genuine genus

**A. Scheme route.** Build `V_α` as a projective scheme, normalize with
`Scheme.Hom.normalization`, define genus through `H⁰(Ω)` or `H¹(O)`. Blocked by
missing coherent-cohomology dimensions and product projective schemes; it
would also require comparing with the classical atlas of Sprint 2. Very high
cost. Not recommended.

**B. Function-field route (recommended).** For a one-variable function field
`K/ℂ`, a place is a discrete valuation of `K` trivial on `ℂ`; the genus is
`dim_ℂ` of the holomorphic differentials, the `ω ∈ Ω_{K/ℂ}` with `ord_v ω ≥ 0`
at every place. This is a standard definition (Chevalley, Stichtenoth) and,
over `ℂ`, agrees with the genus of the smooth projective model, which is the
normalization. It is intrinsic, so invariance under field isomorphisms (and
hence birational maps and similarities, needed for R01) is free.

Fidelity statement to record in COVERAGE: "genus of the normalization of
`V_α`" is read as the genus of the function field of `V_α`. The classical
identification of the normalization with the set of places is not formalized.
This mirrors G01, whose closure is proved in the classical atlas, not as a
scheme.

**C. Topological genus.** Needs a Riemann-surface structure on the
normalization, homology and surface classification. Not viable.

**D. Formula definitions** (`2g−2 = Σ(e−1) − 2n`, `g = ⌊(deg h − 1)/2⌋`).
Forbidden: an arithmetic branch-count expression is not a geometric genus.

## Package decomposition under route B

Sizes are relative guesses, not calendar estimates.

| Package | Content | Depends on | Size / risk |
|---|---|---|---|
| G07a | `K_α := Frac(ℂ[X,Y]/(P_α))`. With `t = X/Y` and `w = t(t^m+1)Y`, show `K_α ≅ ℂ(t)[w]/(w² − h_α)`, `h_α = −t(t^m+1)(α t^m + conj α)`, squarefree of degree `2m+1`, and `[K_α : ℂ(t)] = 2`. Squarefreeness uses the existing coprimality and `α ≠ conj α`. | FamilyQuadratic, Blowup; no genus choice | medium / low |
| G07b | Places of `K_α`: two unramified places over `t=c` with `h(c) ≠ 0`, one ramified place (uniformizer `w`) over each root of `h`, one ramified place over `∞`. Uses Ostrowski for `ℂ(t)`, integral closedness of `ℂ[t][w]`, and extension of valuations. | G07a | large / high |
| G08 | Exactly `2m+2` ramified places of `ℂ(t)` including `0` and `∞`, each of index two; `h_α` is not a square. | G07b | medium / medium |
| G09a | `Ω_{K/ℂ}` is one-dimensional over `K`, spanned by `dt`; order of a differential at a place, independent of the uniformizer; `ord_v(dt)` at each place type. | G07b | large / highest |
| G09b | Holomorphic differentials are exactly the span of `t^i dt/w`, `i < m`; genus `m`. Hurwitz identity for this cover: the degree of `div(dt)` is `−4 + (2m+2) = 2m−2`, computed from the place data (general Riemann–Roch is not claimed). | G08, G09a | medium-large / medium |
| R01 | Genus of `X⁴+Y⁴−2` is three (degree-four Kummer cover `y⁴ = 2 − x⁴`), the `m=2` family has genus two, and genus is invariant under the similarity-induced field isomorphism. | G09a/b generalized to Kummer covers `yⁿ = f` | large / medium |

Design note: writing G07b–G09 for Kummer covers `yⁿ = f` with squarefree `f`
covers both the family (`n=2`, `deg f = 2m+1`) and R01's quartic (`n=4`,
`deg f = 4`). Recommended order: do the odd-degree hyperelliptic case first,
then decide whether to generalize for R01.

## Decisions (user, 2026-09-15)

1. Route B approved: genus means the function-field genus defined above, with
   the fidelity statement recorded in COVERAGE.
2. R01 must go through genus as printed; another non-similarity invariant
   does not close it.

G07a is the next bounded package.
