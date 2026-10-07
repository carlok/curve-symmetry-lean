# The formalization on Prove2Me (2026-10-06 to 2026-10-07)

The whole formalization is published on Prove2Me as the mission
[Sharp symmetry bounds for real algebraic curves](https://prove2.me/missions/Sharp_symmetry_bounds_for_real_algebraic_curves)
(account `carlok`), so that others can import its definitions and theorems and build
on them. It was uploaded privately, checked, and made public on 2026-10-07. Admission
of the mission to the platform's public catalog is a moderator's decision; the
theorems and definitions are public either way. The scripts are in
`scripts/prove2me/`.

## What is there

- 12 definition files `Def_CurveSymmetry_NN_<topic>`: the 86 source modules that
  contain definitions, in dependency order, each module in its own section.
- 208 theorems `CurveSymmetry.<name>`, all Proved. These are 142 of the 161 target
  results (every theorem cited in COVERAGE.md plus the public theorems nothing else
  uses), and 66 lemmas over 40 proof lines, or over 10 lines and used twice. The
  other 19 targets, and the 193 theorems that definitions need, are proved inside the
  definition files. Shorter helpers are pasted into the proofs that use them.
- Every theorem has a title, a natural-language statement, a source (the note's
  statement and page, the PDF and the Lean file at commit `d99bc17`), tags
  `curve-symmetry-lean` plus two topic tags, and an explanation of its proof.
- The mission: goal `paper_sharp_bounds` (Theorem 1, the bounds) and 41 milestones,
  the note's statements in its order, each linked to its theorem.

## The port

Prove2Me verifies in Lean v4.33.1 with Mathlib `0df444a`; this repository is on Lean
v4.34.0 with Mathlib `5ed2965`. The port changed 56 lines in 22 files, all inside
proofs or imports, and no statement. Examples are a renamed import
(`Mathlib.Data.Complex.Basic`), older lemma names (`MvPolynomial.coeff_add`,
`if_pos`/`if_neg`, `Ideal.eq_bot_of_comap_eq_bot`), and the pre-bump form of a few
proofs. On v4.33.1 the library builds with warnings as errors, and its audit (2,053
declarations) uses only `propext`, `Classical.choice` and `Quot.sound`.

## How the files were made and checked

The generator follows the platform's `upload_full_project` playbook. Lean extraction
scripts give the declaration graph and exact source spans, and each file is the source
minus the unselected declarations. Rules added to the playbook:
- local instances, and theorems occurring inside statements, go into the definition
  files;
- `@[simp]` lemmas proved by `rfl` go next to their definitions, since `simp` uses them
  by unfolding and no proof term mentions them;
- local notations are spelled out in statement stubs;
- the platform allows at most 100 queued jobs per account.

Checks before upload, all on the platform's exact environment:
- **Build.** Definitions, statements and solutions build with no error.
- **Statements.** Every theorem's elaborated statement equals the original's.
  205 are identical. 3 differ by the instance path `NonUnitalNonAssocSemiring.toDistribSMul`
  against Mathlib's `instDistribSMul`: a merged definition file imports more Mathlib.
  The two instances are equal by `with_reducible_and_instances rfl`.
- **Definitions.** Every constant of the definition files equals the original in kind,
  type and value, up to that equality and to shared auxiliary proofs.
- **Solutions.** Every solution's type equals its statement: 176 are identical, 32
  differ only in hygienic names of anonymous instance binders. The axioms are the
  standard three.
- **Texts.** All titles, statements and explanations pass a rule check (no novelty
  wording, no labels or line numbers, KaTeX-safe math). All 16,676 formulas render in
  KaTeX. An independent audit of 72 statements against the elaborated Lean types (the
  40 theorems the coverage ledger names as the note's statements, plus 32 at random)
  found them all faithful.

## Upload

- **Definition files:** 12 published.
- **Statements:** 208 published, then read back to confirm they match what was sent.
- **Proofs:** 208 verified with leaves first, all accepted directly.
- **Explanations:** 208 patched and read back.
- **Mission:** created as a private proposal with 54 reference items, submitted, then
  made public. The goal, milestones and their dependencies covered 164 theorems; the
  remaining 44, under 39 standalone results, were made public one call each.
- **Final read-back:** 208 theorems public and Proved, 12 definition files public.

## Who wrote what

The Lean code, the generated files, the titles, statements and explanations were
written by AI agents under C. Perassi's direction. The Lean kernel and the Prove2Me
verifier check the proofs. The texts were checked by scripts and by an audit of
independent agents; no independent human has reviewed them, and nothing here certifies
novelty.
