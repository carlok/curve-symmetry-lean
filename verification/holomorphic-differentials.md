# Regularity of a differential at a place (G09b-1) — 2026-09-19

Follows the G09a chain (`8ef2b25`, order of `dt` at every place). The file is
[HolomorphicDifferentials](../lean/HolomorphicDifferentials.lean).

## Definition

`IsRegularAt h c d hd ω`: for every uniformizer `u` of the local ring at the
point place `(c, d)` and every `f` with `ω = f·du`, the coefficient `f` lies in
that local ring. Quantifying over all uniformizers keeps the definition free of
choices; `isRegularAt_iff` shows one uniformizer decides it, using the
coefficient-unit lemma of G09a-2c.

## The two criteria

With the uniformizers identified in G09a-2e and G09a-2f, for `ω = f·dt`:

| place | uniformizer | regular iff |
|---|---|---|
| `h(c) ≠ 0` | `t − c` | `f` in the local ring |
| `h(c) = 0` | `w` | `f·w` in the local ring |

The ramified case goes through `quad_ramified_coeff`: the coefficient against
`w` is `(2·f·w)/h'(t)`, and `2` and `h'(t)` are units of that local ring
(`quadLocal_const_mem`, `quad_ramified_derivative_isUnit`,
`quadLocal_inv_mem_of_isUnit`), so they can be dropped. In words: at a ramified
place a holomorphic differential may have one pole in `f`, which is the
`ord_v(dt) = 1` of G09a-2f seen from the other side.

`family_isRegularAt_criteria` states both for the family.

`quad_derivative_ne_zero` records that `h'` is nonzero in the function field at
a ramified place: `h` is squarefree, so it is nonzero, and in characteristic
zero a nonzero derivative follows from `h(c) = 0`.

## Regularity at infinity (G09b-2)

`kaehlerTransport` (generic, in `LocalDifferentials`): an isomorphism of
`R`-algebras carries `Ω[A⁄R]` to `Ω[B⁄R]`, with `d a ↦ d (e a)` and
`c·ω ↦ e(c)·(transport ω)`. It is built from `KaehlerDifferential.map` for the
algebra structure that the isomorphism itself provides.

`IsRegularAtInfinity ω` is regularity of `kaehlerTransport ω` at the conjugate
family's point place `(0, 0)`, which is where the chart isomorphism sends the
place over `t = ∞`. For `ω = f·dt` the transport is `φ(f)·d(1/s)`, and G09a-2g
turns that into a coefficient against the uniformizer `w'`:
`φ(f)·(−2w')/(s²·h_conj'(s))` (`isRegularAtInfinity_iff`).

The units are cancelled in G09b-3a below.

## The criterion at infinity with the units cancelled (G09b-3a) — 2026-09-22

First package on Lean 4.34.0 (`db011ac`). `familyInfinity_shift_sq` carries the
ramified-place identity `(t − c)·k = w²` of G09a-2f into the conjugate function
field at `c = 0`: `s·k = w'²` with `k(0) ≠ 0`. `quadLocal_poly_unit` (in
`HolomorphicDifferentials`) makes any polynomial nonvanishing at `c` a unit of
the local ring at a place over `c`, and `quadRoot_ne_zero` gives `w ≠ 0`.

`isRegularAtInfinity_iff_cube`: the raw coefficient of G09b-2 equals
`e·(φ(f)/w'³)` with `e = −2k²/h_conj'(s)`, a unit of the local ring (inverse
`−h_conj'(s)/(2k²)`), so `f·dt` is regular at infinity iff `φ(f)/w'³` lies in
that local ring. This is `ord_∞(f) ≥ 3`, matching `ord_∞(dt) = −3`.

## The holomorphic differentials as a subspace (G09b-3b)

`isRegularAt_zero`, `isRegularAt_add`, `isRegularAt_smul` (point places) and the
matching `isRegularAtInfinity_*` (through `kaehlerTransport_smul_base`) close
regularity under the vector-space operations. `holomorphicDifferentials` in
[HolomorphicSpace](../lean/HolomorphicSpace.lean) is the `ℂ`-subspace of
differentials regular at every point place and at infinity; G07b's
`family_place_classification` is what makes those all the places.
`isHolomorphic_smul_dt_iff` spells out holomorphy of `f·dt`: `f` in the local
ring where `h(c) ≠ 0`, `f·w` in it where `h(c) = 0`, `φ(f)/w'³` in the local
ring at infinity.

## `m` independent holomorphic differentials (G09b-3c)

[HolomorphicBasis](../lean/HolomorphicBasis.lean). `holoBasisVec_mem`: for
`i < m`, `tⁱ·dt/w` is holomorphic, checked with `isHolomorphic_smul_dt_iff` at
each kind of place — `w` is a unit where `h(c) ≠ 0` (`quadLocal_root_inv_mem`),
`(tⁱ/w)·w = tⁱ` where `h(c) = 0`, and at infinity, writing `m = i + 1 + j`,
`φ(tⁱ/w)/w'³ = s^(j+2)/w'⁴ = w'^(2j)·k^(−(j+2))` using `s·k = w'²`.

`holoBasisVec_linearIndependent`: a vanishing `ℂ`-combination gives
`(p(t)/w)·dt = 0` with `p = Σ gᵢXⁱ`; `dt ≠ 0` and `w ≠ 0` force `p(t) = 0` in the
function field, `ℂ[t]` embeds injectively (`algebraMap_polynomial_injective`),
so every `gᵢ` is zero. The holomorphic differentials therefore have dimension
at least `m`.

## Scope

Not here: the space of holomorphic differentials and the claim that it is spanned by
`tⁱ·dt/w` for `i < m`; the genus; and the degree identity
`deg div(dt) = 2m − 2`. No divisor, Riemann–Roch or Riemann–Hurwitz statement is
assumed anywhere.

## Checks

- Compiles with `-DwarningAsError=true`; the aggregate rebuilds.
- Namespace axiom audit: 1,635 declarations (Lean 4.34.0), allowlist `propext`,
  `Classical.choice`, `Quot.sound`.
- `scripts/check_sources.py`: 97 modules, 9 exact dependency revisions.
- Package tests: 6 passing.
- Private Linux run 35456966169 passed on the head commit `ad40a51`.
