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

## Scope

Not here: regularity at the place over `t = ∞`, which needs the transport of an
identity in `Ω` along the chart isomorphism (the piece G09a-2d left out); the
space of holomorphic differentials and the claim that it is spanned by
`tⁱ·dt/w` for `i < m`; the genus; and the degree identity
`deg div(dt) = 2m − 2`. No divisor, Riemann–Roch or Riemann–Hurwitz statement is
assumed anywhere.

## Checks

- Compiles with `-DwarningAsError=true`; the aggregate rebuilds.
- Namespace axiom audit: 1,567 declarations, allowlist `propext`,
  `Classical.choice`, `Quot.sound`.
- `scripts/check_sources.py`: 94 modules, 9 exact dependency revisions.
- Package tests: 6 passing.
