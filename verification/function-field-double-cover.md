# Function-field double cover (G07a) — 2026-09-15

The introducing commit is the checkpoint for this package. It follows the
approved genus scope study (`verification/genus-scope-study.md`) and the
previous proof snapshot `ba20da2`, which passed private Linux runs
34938739018 and 34938739562.

## Objects

In FamilyFunctionField, for `m > 0` and nonreal `α` (as `Fact` instances):

- `FamilyCoordinateRing m α = ℂ[X,Y]/(P_α)`, a domain because `P_α` is
  irreducible (`familyPolynomial_irreducible`), hence prime.
- `FamilyFunctionField m α` is its fraction field: the function field of the
  affine curve, which is dense in `V_α` (G01), so it is the function field of
  `V_α`.
- `familyPoint` gives the coordinate functions `x, y`; `familyT = x/y`;
  `familyW = t(t^m+1)·y`; `familyH = −t(t^m+1)(α t^m + conj α)`;
  `familyQuadraticRat = W² − h` over `RatFunc ℂ`.

## Results

- `familyT_aeval_eq_zero`: `t` is transcendental over `ℂ`. If `t` satisfied
  a polynomial, some `t = c` would make `X − cY` divisible by `P_α`, which is
  impossible by degree.
- `familyRatFuncHom`: the induced `ℂ`-algebra embedding `ℂ(t) → K`.
- `family_quadratic_relation`: `A(t) + B(t) y² = 0` (the strict transform).
- `familyW_sq`: `w² = h(t)`.
- `familyH_natDegree_of`, `familyH_squarefree_of`: `h` has degree `2m+1` and
  is squarefree; its three factors are separable and pairwise coprime.
- `familyQuadraticRat_irreducible_of`: `W² − h` is irreducible over `ℂ(t)`,
  because a square root `num/denom` would give `num² = h·denom²`, which is
  impossible for odd `deg h`.
- `familyLift_injective`, `familyLift_surjective` and
  `family_functionField_double_cover`: the lift
  `ℂ(t)[W]/(W² − h) → K`, `W ↦ w`, is a ring isomorphism compatible with
  `ℂ(t) → K`; the source has dimension two over `ℂ(t)`.

## Scope boundary

This is a statement about fields. It does not construct places, valuations,
ramification data, differentials or a genus. The identification of "the
normalization" with the places of this field is the approved fidelity reading
recorded in COVERAGE, not a formalized theorem. G07b (places), G08, G09 and
R01 remain.

## Checks

- New module and aggregate compiled incrementally with warnings as errors.
- Namespace axiom audit: 1,286 declarations; only propext, Classical.choice,
  Quot.sound.
- Preflight: 81 modules, nine exact pins. Six package tests and
  `git diff --check` passed.
- Paper TeX/PDF hashes unchanged from ONBOARDING.md.

This snapshot requires its own CI result. No clean local rebuild,
independent checker, Palomar dry run or human review is claimed.
