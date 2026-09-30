# Sprint 0 migration evidence

Date: 2026-09-06.

- Source: the `curve_symmetry/` directory of the author's previous workspace.
- Destination: this repository's location on the author's machine.
- The destination did not exist; the source had no nested Git repository and
  none of its files was tracked by the parent repository.
- The complete directory was moved with overwrite protection. No compatibility
  symlink or second project copy was left at the old location.
- All 81 regular files had identical SHA-256 hashes immediately before and
  after the move, including the existing ignored build artifacts. The inventory
  is `migration-before.sha256`; it is an event record, not a checksum assertion
  about files intentionally edited after the migration.
- The pre-move build compiled 33 modules with warnings as errors and returned
  exit 0. All 85 endpoint axiom reports used only `propext`, `Classical.choice`,
  and `Quot.sound`.
- Lean 4.32.0 and the compiled dependencies of an existing local Lake
  installation were reused. No library checkout or toolchain was copied.
- The TeX SHA-256 at migration was
  `3aff1c6edf6f189de6fa56c690631c266364a3b129408eb0fd5a200ceb186925`.
- The existing PDF SHA-256 was
  `8b1f71e7a4f5dbce7fce3de383b675411e3fbba21bea4939609991f47a10ffd1`.

The post-move build also returned exit 0: 33 modules, warnings as errors, and
85 reports containing only the permitted axioms. Its complete axiom output is
`sprint-0-axioms.txt`. The private-remote checkpoint is recorded in `SPRINTS.md`
when it passes. This record does not claim a Palomar run.
