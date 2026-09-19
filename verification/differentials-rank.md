# Rank of the differentials of the double cover (G09a-1) — 2026-09-19

The introducing commit is the checkpoint for this package. It follows G08
(`4a526be`, private Linux run 35118101524) and the Palomar entry for Theorem 1,
which touched no Lean source in this library.

## What is proved

For every squarefree `h ∈ ℂ[t]` with `W² − h` irreducible over `ℂ(t)`, in
[QuadraticDifferentials](../lean/QuadraticDifferentials.lean):

- `quadKaehlerBasis` — a basis of `Ω[K⁄ℂ]` indexed by `Unit`, whose single
  vector is `dt` (`quadKaehlerBasis_apply`).
- `quad_kaehler_finrank` — `finrank K Ω[K⁄ℂ] = 1`.
- `quad_kaehler_span_eq_top` — `Ω[K⁄ℂ]` is spanned by `dt`.
- `quad_D_t_ne_zero`, `quad_exists_smul_D_t` — `dt ≠ 0`, and every differential
  is `c · dt` for a unique-up-to-the-basis `c ∈ K`.
- `quad_D_algebraMap` — the chain rule `d(p(t)) = p'(t)·dt`.
- `quad_D_root` — `2w·dw = h'(t)·dt`, obtained by differentiating `w² = h(t)`.
- `family_kaehler_dt` — the same statement for the family's function field.

Two intermediate results are generic and independent of this project:
`polynomialKaehlerBasis` (`Ω[ℂ[t]⁄ℂ]` free of rank one on `dt`, a repackaging of
Mathlib's `polynomialEquiv`) and `ratFuncKaehlerBasis` (the same for `ℂ(t)`).

## Route

`Ω` is transported twice by `kaehlerBasisOfEtale`, which base-changes a basis of
`Ω[S⁄R]` to one of `Ω[T⁄R]` whenever `T` is formally étale over `S`, using
Mathlib's `KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale`:

1. `ℂ[t] → ℂ(t)`: formally étale as a localization
   (`Algebra.FormallyEtale.of_isLocalization` at `nonZeroDivisors ℂ[t]`).
2. `ℂ(t) → K`: `ℂ(t)` has characteristic zero, hence is perfect, so the finite
   extension `K` is separable (`Algebra.FormallyEtale.of_isSeparable`).

The chain rule is Mathlib's `Derivation.map_aeval` applied to the universal
derivation; nothing about derivations is re-proved here.

## Scope and honesty

This is the rank statement only. No order of vanishing, divisor, canonical
class, genus or Riemann–Roch statement is defined, assumed or implied, and the
pinned Mathlib contains none of them (see `genus-scope-study.md`). G09a-2 will
define `ord_v` of a differential at the places classified in G07b-2c and
G07b-3, where `quad_D_root` supplies the behaviour at the ramified places, whose
uniformizer is `w`.

## Checks

- `QuadraticDifferentials` compiles with `-DwarningAsError=true`; the aggregate
  `CurveSymmetry` rebuilds.
- Namespace axiom audit: 1,475 declarations, allowlist `propext`,
  `Classical.choice`, `Quot.sound`. The module's own `#print axioms` lines show
  the same three for `quad_kaehler_finrank`, `quad_D_root` and
  `family_kaehler_dt`.
- `scripts/check_sources.py`: 89 modules, 9 exact dependency revisions.
- Package tests: 6 passing.
