# Sprint 3 — actual sphere-action checkpoint

Branch: `codex/sprint-3`. Sprint remains incomplete.

## Completed subtask results

- `FamilySphereDilation`: inclusion on spherical loci implies nonzero scalar
  proportionality, normalized parameter equality and unit scale. Self-inclusion
  is equivalent to `c^(2*m)=1`, and the root test preserves membership in both
  directions, including infinity.
- `FamilySphereInversion`: corresponding results for the denominator-cleared
  inversion polynomial and `c^(2*m)=conj(alpha)^2`, with explicit zero/infinity
  cases. Involution gives the bidirectional membership theorem.
- `FamilySphereClassification`: integration with arbitrary ambient completeness
  gives the exact self-map test, both parameter-necessity results and exclusion
  of every anti-Möbius self-inclusion. These prove T2.3 and T2.4, not the group
  isomorphism or all of T2.7.

Both original subagents were interrupted by an account usage limit. On user
continuation, root implemented dilation; one resumed agent implemented and
compiled inversion, and the other performed a read-only mathematical scope
review. Root integrated the arbitrary-matrix wrappers and re-audited the
aggregate. The review found no mathematical flaw and specifically warned not
to call inclusion equality without an inverse argument; membership-iff
wrappers now discharge that distinction.

## Verification

New modules compiled with warnings as errors using installed Lean 4.32.0 and
the existing nine exact dependency pins. The full namespace audit passed 990
declarations with only `propext`, `Classical.choice`, and `Quot.sound`.
Preflight passed for 68 Lean files and all six package tests passed.
`git diff --check` passed; TeX/PDF hashes are unchanged. Checks were incremental,
not a new full clean build. Sprint 2 completion `d29fd22` passed private Linux
run `34749984410`; this new checkpoint's Linux result is pending at commit.

## Remaining boundary

Construct the full ambient group, its dihedral isomorphism and order `4m`;
finish the `m=2` Euclidean interface, package identity/conjugation sufficiency
for parameter equivalence, and prove the algebraic-coefficient corollary.
Normalization/genus and the faithful Palomar dry run remain untouched.
No independent human review, registry acceptance or novelty certification is
implied by the agent review or kernel checks.

## Package 1 — paper-facing basic family geometry

`CurveSymmetry.paper_family_geometry` in `PaperFamilyGeometry.lean` packages T2.1:
for every m>=2 and nonreal alpha there exists a real Cartesian equation f,
geometrically irreducible over C, of total degree m+2, whose actual locus is
the displayed family and is infinite. No modulus-one assumption or stronger
m>=3 cutoff is introduced. The witness comes from the existing Cartesian
descent theorem. This is endpoint packaging, not a new mathematical result.

The module and aggregate compiled with warnings as errors; all 993 namespace
declarations passed the three-axiom audit. Preflight passed for 69 files and
nine pins, and all six tests passed. `git diff --check` passed. TeX/PDF hashes
remain unchanged. These are incremental local checks. Prior commit `0fced06`
passed private Linux runs `34762684748` (sprint branch) and `34762846686` (main);
the new checkpoint's Linux check is pending at commit time. T2.1 is complete;
no further group, genus or Palomar obligation is claimed complete.

## Package 2 — complete parameter equivalences

Added `family_mobius_equivalence_iff` and
`family_anti_mobius_equivalence_iff` to `FamilySphereClassification.lean`.
For fixed m>=2 and normalized nonreal parameters, they assert existence of an
ambient matrix carrying the entire source spherical locus exactly onto the
target iff beta=alpha or beta=conj(alpha), respectively. Existing necessity
uses only inclusion. Sufficiency explicitly chooses the identity matrix,
with conjugation in the antiholomorphic action; its sphere involution proves
both set inclusions, including infinity. T2.7 is complete.

The changed module and aggregate compiled with warnings as errors, and all
996 namespace declarations passed the three-axiom audit. Preflight passed for
69 files and nine dependency pins; all six tests passed. `git diff --check`
passed; TeX/PDF hashes are unchanged. This was an incremental local check.
Prior commit `9993b04` passed private Linux runs `34819328710` and `34819389215`;
this checkpoint's Linux result is pending at commit. No group-order, genus or
Palomar completion is claimed.
