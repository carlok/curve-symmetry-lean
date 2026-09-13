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
