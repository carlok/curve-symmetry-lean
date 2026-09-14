# Mathematical and verification snapshot

Snapshot: Sprint 3 package 3 complete, 2026-09-14.
Full claim-by-claim detail is in [COVERAGE.md](COVERAGE.md).

## Paper-facing results

| Result | Checked scope |
|---|---|
| Theorem 1: symmetry bounds | Actual Euclidean groups are finite; the direct group is cyclic, of order at most `max(d, 2d−4)`; full group order at most `2d`. |
| Theorem 1: sharpness | Both bounds are attained in every degree `d ≥ 2`. |
| Theorem 1: equality classification | For `d ≥ 5`, maximal direct symmetry forces the normalized family under an orientation-preserving similarity. |
| Theorem 1: converse | The family with `m ≥ 3` and nonreal parameter attains the rotation bound. |
| Theorem 2: basic family geometry | One real Cartesian equation is geometrically irreducible, has degree `m+2`, and has the exact infinite family locus, for every `m ≥ 2` and nonreal parameter. |
| Theorem 2: ambient completeness | For `m ≥ 2`, arbitrary Möbius/anti-Möbius containment forces the two holomorphic or two conjugated map forms, including zero and infinity. |
| Theorem 2: coefficient tests and no anti-map | Exact two root conditions characterize actual Möbius self-inclusion, which preserves membership in both directions; no anti-Möbius self-inclusion exists. |
| Theorem 2: parameter equivalence | Actual spherical loci are holomorphically equivalent iff `β=α`, antiholomorphically equivalent iff `β=conj(α)`, for normalized nonreal parameters and `m ≥ 2`. |
| Theorem 2: full ambient group | Actual sphere symmetry group is dihedral of order `4m`, with exact-order generators and exhaustive normal forms, for every `m ≥ 2` and normalized nonreal parameter. No anti-Möbius additions exist. |
| Projective geometry (G01) | Bihomogeneous closure and exact separate degrees `(m+1,m+1)` in the uniquely characterized classical Zariski atlas; global topological irreducibility. |

Theorem 1 has five `paper_*` theorem endpoints. Ambient completeness has two
endpoints. A sixth `paper_*` endpoint now packages Theorem 2's basic geometry.
Endpoint counts are not independent-new-result counts. Theorem 2 as a whole
is still incomplete.

## Internal proved machinery

- Cartesian/complex coordinate equivalence, polynomial divisibility from an
  infinite real locus, actual isometry interfaces and a common rotation center.
- Sharp examples, weight restrictions, equality normal form and normalization
  of its parameters by similarity (not normalization of an algebraic curve).
- Family polynomial irreducibility, degree and infinitude; four-form coefficient
  filters; chart Jacobians, singular pair and global transport under ambient maps.
- Affine spectrum density, all boundary-chart closure identities, inversion
  homeomorphisms, four open projective charts, atlas uniqueness and projective
  irreducibility. These are proved ingredients, not a genus theorem.

## Still missing

Sprint 3: full Euclidean-group identification including `m=2`,
algebraic-coefficient consequence, and the remaining parameter-family consequence.
Sprint 4: ordinary multiple-point geometry, normalization,
ramification, Riemann–Hurwitz, genuine genus `m`, and remaining paper remarks.
Sprints 5–7: Palomar contract, faithful private dry run and final TeX integration.

## Counts and trust boundary

| Metric | Value |
|---|---:|
| Lean source files (including aggregate) | 71 |
| Written theorem/lemma declarations | 489 |
| Written definitions/abbreviations/structures/inductives | 130 |
| Lean source lines, including comments and blank lines | 7,633 |
| Audited namespace declarations, including generated/private machinery | 1,075 |
| Exact dependency pins | 9 |
| Package-test cases | 6 passing |

Written-declaration counts use line-anchored source declarations, including
private/protected declarations; they are not novelty counts. The audit allows
only `propext`, `Classical.choice`, and `Quot.sound`. There are no intentional
proof placeholders in the library. Local verification was incremental, with
warnings as errors and installed dependencies reused. Lean is 4.32.0; Mathlib
is pinned to `81a5d257c8e410db227a6665ed08f64fea08e997`.

Previous commit `30bcfb0` passed private Linux runs `34823034995` and `34823034336`; this snapshot's
Linux result is pending at commit time. No faithful Palomar dry run, NanoDa
replay, independent human review or novelty certification has been completed.
TeX and PDF are unchanged. Sprints 0–2 are mathematically complete at their
stated scope; the complete paper and Palomar readiness are not.
