# Complete Lean port and private Palomar readiness

Agreed roadmap, 2026-09-06. Local folder: `curve_symmetry`; private GitHub
repository: `carlok/curve-symmetry-lean`; license: Apache-2.0.

The objective is the complete mathematical paper, not a submission limited to
Theorem 1. A missing foundation remains an explicit obligation; it is never
replaced by an axiom, convenient surrogate definition, or concealed hypothesis.
The TeX remains unchanged until the private dry run passes. Nothing authorizes
public visibility, Palomar intake, registration, or external expert outreach.

## Status ledger

| Sprint | Status | Completion evidence / commit |
|---|---|---|
| 0: relocation and private Git | Complete | `74e0e1228dc01aa1c8965b6818cf05f4e13750e7`; 81 migrated file hashes match, 33 modules / 85 axiom reports pass; remote verified private and pushed |
| 1: reproducible package and statement inventory | Complete | `459e644bb4919c2e71841e7ba62a8d6418c24d38`; [Linux run 34046925427](https://github.com/carlok/curve-symmetry-lean/actions/runs/34046925427) passed; 34 files / 532 declarations audited; [report](verification/SPRINT-1.md) and [coverage ledger](COVERAGE.md) |
| 2: global geometry and Möbius completeness | In progress — completeness gate proved | Both ambient completeness theorems and affine Zariski closure checked; G01's projective boundary-closure identification remains outstanding; [checkpoint evidence](verification/SPRINT-2.md) |
| 3: complete ambient symmetry theorem | Not started | Four-form coefficient tests already checked; completeness is not assumed |
| 4: genus and remaining mathematical claims | Not started | Foundational interface still missing |
| 5: Palomar contract and editorial preparation | Not started | Requires complete mathematical coverage |
| 6: private contract-faithful Linux dry run | Not started | Requires frozen contract and full proofs |
| 7: TeX integration and final snapshot | Not started | Requires successful dry run |

Starting checkpoint: 33 Lean modules and 85 axiom reports. Every clause of
Theorem 1 is checked, using real Cartesian polynomials and actual isometry
groups. Theorem 2 is incomplete. See `lean/README.md` for the precise boundary.

## Sprint 0 — relocation and private version control

Record a successful baseline build and content hashes; move the whole folder
from `transcendental/curve_symmetry` to the sibling Lean workspace without
overwriting a destination. Verify hashes and reproduce the build. Initialize
independent Git history, add Apache-2.0 and artifact exclusions, then create and
verify a private remote before pushing. Preserve unrelated source-repository
state. Work on `codex/sprint-*` branches and record scoped completion commits.

Gate: identical migrated contents, successful relocated build, private pushed
source snapshot, and no bundled library/toolchain copies.

## Sprint 1 — reproducible package and statement inventory

Use one root TOML Lakefile, a committed toolchain and exact manifest, retaining
the existing Lean source directory and declaration names. Pin Lean 4.32.0 and
Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`. Preserve the local command
that reads an existing compiled dependency installation; add private Linux
build CI for portable clean-checkout testing.

Inventory theorems, supporting lemmas, substantive mathematical remarks, and
proof claims needed to explain their scope. Map each to declarations or an
explicit obligation. Use ordinary Cartesian curves, genuine ambient actions,
spherical closure, geometric irreducibility, and genuine geometric genus.

Gate: portable configuration, full coverage ledger, and no runtime dependence
on the former project location.

## Sprint 2 — global geometry and Möbius completeness

Use standard projective-line coordinates and invertible-linear-map actions,
with a proved finite-chart/infinity interface. Construct the bihomogeneous
family in `P¹ × P¹`; connect the checked Jacobian and tangent-cone data to that
curve. Lift equivalences of spherical real loci to the complexification and
derive singular-pair preservation and the four possible map forms.

Gate: completeness for arbitrary Möbius/anti-Möbius equivalences, with neither
pair preservation nor the four-form reduction assumed.

The mixed corner now belongs to the Zariski closure of actual complex points
with nonzero first coordinate in its affine chart (`MixedCornerClosure`).
This is a chart-level theorem, not yet a projective closure identification.
The reciprocal chart at `(∞,∞)` now has the corresponding density theorem
with both axes deleted (`ReciprocalCornerClosure`). `OtherMixedCornerClosure`
transfers original affine points by `(X,Y) ↦ (1/Y,X)` and proves their chart
closure contains the corner `(0,∞)`. `AffineChartImages` supplies the matching
original-affine-point image and closure identities for the first mixed and
reciprocal charts. `ProjectiveChartMaps` constructs the four standard homogeneous
chart maps, their affine-overlap identities, curve-equation interfaces, and
boundary-origin identities. All four maps are now proved injective, and their
ranges cover the product of projective lines. Their ranges are now identified
exactly as complements of the relevant zero/infinity coordinate divisors.
`AffineZariskiTopology` now provides the induced complex-point topology, its
embedding into the prime spectrum, polynomial nonvanishing opens, and the
usual algebraic closure formula. It does not install a global instance on
coordinate vectors. `InversionDenominators` now clears a power of the inverted
coordinate in any polynomial and identifies the inverse images of polynomial
zero sets on the nonzero domain. `InversionContinuity` now proves that either
coordinate inversion is a Zariski homeomorphism of its nonzero-coordinate
domain. Next bounded target: coordinate exchange and simultaneous inversion
on the two-coordinate nonzero domain, completing the transition primitives.
Projective topology and gluing remain obligations; G01 is not complete.

## Sprint 3 — complete the ambient symmetry theorem

Combine completeness with the exact coefficient filters. Prove the sphere
actions at zero and infinity, the dihedral group of order `4m`, exactly `2m`
Euclidean rotations, no anti-Möbius self-equivalence, and both complete
parameter-equivalence criteria. Include the algebraic-coefficient consequence,
the `m=2` case, and the stated exclusions.

Gate: all clauses of Theorem 2 on actual ambient transformations, not just
denominator-cleared polynomial identities.

## Sprint 4 — genus and remaining paper claims

Construct normalization and the double cover with its ramification data.
Prove the required Riemann–Hurwitz machinery and actual genus `m`. Complete
bidegree, ordinary-point assertions, the quartic genus comparison, and all
remaining substantive claims in the coverage ledger.

Gate: the entire mathematical port is hole-free. A numerical branch-count
identity is not a geometric-genus theorem. This is the highest-risk sprint:
the installed Mathlib search did not locate a ready-made interface. Missing
foundations must be proved. No calendar estimate is promised.

## Sprint 5 — Palomar contract and editorial preparation

Create one compact Challenge/Solution pair and Comparator configuration for
the principal claims. Challenge imports only the permitted Mathlib closure;
statement definitions have explicit ordinary meanings and no definition holes.
Only the isolated statement-only Challenge may contain deliberate theorem
placeholders. The proof library and Solution must never depend on them.

Prepare valid metadata for sources, license, authorship, AI assistance, scope,
fidelity, and actual review status. Audit research positioning and preserve the
arXiv-versus-uninspected-journal qualification. Pin verifier, Comparator,
exporter, and independent checker revisions. No fabricated model provenance,
human review, novelty certificate, or Palomar ID.

Gate: accurate independently readable statements and passing static contract
checks. Policy: https://palomar-registry.org/how-to-submit and
https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md .

## Sprint 6 — private contract-faithful dry run

Use an immutable commit and clean private Linux GitHub Actions checkout.
Validate dependencies; compile Challenge in isolation; protect the comparison
configuration; run real sandboxed Comparator and NanoDa replay without network
access or credentials in the proof sandbox. Require disposable negative
controls for a changed theorem type, forbidden axiom, and forbidden Challenge
import to fail. Record exact revisions and distinguish mechanical evidence
from editorial self-review and anything not tested.

Gate: positive case passes and negative controls fail. No fake sandbox or
skipped checker qualifies. This is private CI, not Palomar intake. Ordinary
GitHub Actions usage was approved; repository publication was not.

## Sprint 7 — TeX integration and final snapshot

Only after Sprint 6, refactor the existing note without bloating its mathematical
exposition. Add a short formalization section/appendix with theorem-to-Lean
links, reproduction instructions, dependencies, exact scope, AI disclosure,
and the distinction between kernel checks, dry runs, novelty, and human review.
Do not imply registration. Rebuild, run ChkTeX, inspect the PDF, and rerun
verification against the final committed snapshot.

Gate: paper, formal statements, metadata, and verification evidence agree at
one private release-candidate commit.

## Completion discipline

Record each sprint's checks and completion commit here. The permitted proof
axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`. No proof
holes, `native_decide`, custom axioms, or hidden theorem assumptions may be
used to close a sprint. Palomar-ready is a reproducible, honestly described
candidate—not guaranteed editorial approval or registry acceptance.
