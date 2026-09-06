# Sprint 1 verification

Verified source commit: `459e644bb4919c2e71841e7ba62a8d6418c24d38`.
Private repository: `carlok/curve-symmetry-lean`.
Date: 2026-09-06.

## Local verification

- Built 33 mathematical modules and `CurveSymmetry.lean`, treating warnings as errors.
- Reused `/Users/carlo/Documents/varie/hacks/lean4/diaz-modulus-lean` read-only;
  the toolchain and all nine dependency checkout revisions match the root pins.
  This validates pins and uses existing compiled artifacts; it is not a fresh
  local build of Mathlib or a byte-level attestation of its artifact provenance.
- The 85 selected endpoint reports list only the permitted axioms.
- The new complete-namespace audit passed for **532 declarations**, including
  private names, with allowlist `propext`, `Classical.choice`, `Quot.sound`.
- All six package-preflight regression tests passed; source/manifest preflight
  passed; `git diff --check` passed.

## Clean private Linux verification

[GitHub Actions run 34046925427](https://github.com/carlok/curve-symmetry-lean/actions/runs/34046925427)
completed successfully on `ubuntu-24.04`, 16:54:25–17:00:21 UTC.
The workflow checked out the immutable source commit above with checkout
credentials not persisted, installed the committed toolchain, and retrieved
the pinned upstream Mathlib dependencies and their Linux cache artifacts.
Project build caching was disabled for this run.

Observed log results:

```text
Ran 6 tests in 0.000s
Package preflight passed: 34 modules, 9 exact dependency revisions
Build completed successfully (3445 jobs).
Axiom audit passed: 532 declarations; allowlist propext, Classical.choice, Quot.sound
```

The final dependency-lock diff check passed. The workflow uses
`actions/checkout` at `11d5960a326750d5838078e36cf38b85af677262` and
`leanprover/lean-action` at `50fcf42d2e460296f1a34b402e990d1b24f8b596`.
This pins the top-level actions, not every tool fetched inside those actions;
the more stringent verifier-tool pins belong to Sprints 5–6.

## Scope

This proves reproducibility of the current **partial port** on Linux. It is not
an independent checker replay, a sandboxed adversarial proof test, a Palomar
submission, or a verification of Theorem 2/genus. Those gates remain open in
`SPRINTS.md` and `COVERAGE.md`. Source scans are regression guards, not the
security boundary required for the eventual dry run.

The existing TeX and PDF retain their pre-sprint hashes:

```text
3aff1c6edf6f189de6fa56c690631c266364a3b129408eb0fd5a200ceb186925  sharp_symmetry_bounds.tex
8b1f71e7a4f5dbce7fce3de383b675411e3fbba21bea4939609991f47a10ffd1  sharp_symmetry_bounds.pdf
```
