# Sprint 7 — TeX integration, 2026-09-30

`sharp_symmetry_bounds.tex` gains Appendix A, "Formal verification". The
mathematical text is unchanged.

## What the appendix states

- Where each statement is checked: Theorems 1 and 2, Lemmas 3 and 4, equation
  (5), the quintic (2) and Remark 5, each with its Lean declarations
  (`paper_*` endpoints and the Theorem 2 declarations); COVERAGE.md for the
  supporting claims.
- Versions: Lean 4.34.0, Mathlib `5ed2965` (tag `v4.34.0`), nine exact pins;
  108 modules and about 900 theorems and lemmas; only `propext`,
  `Classical.choice` and `Quot.sound`, no `sorry`, no `native_decide`, audited
  for every declaration of the project.
- Readings: the normalization as the function field; genus as the dimension of
  the holomorphic differentials, defined without a model, hence preserved by
  the isomorphism of function fields that a similarity induces (Remark 5, for
  both orientations and every nonreal parameter); branch points by fibres,
  ramification indices not formalized; singular points, multiplicities and
  tangent cones in the four standard charts, without chart-change invariance.
- Different routes: the genus from explicit bases (`tⁱ·dt/w`, `i < m`; for the
  quartic `dX/Y³`, `X·dX/Y³`, `dX/Y²`) instead of Riemann–Hurwitz; the
  irreducibility of (7) by Eisenstein at `t = 0` after reversing the quadratic
  variable, instead of the nonsquare argument.
- Who checked what: the Lean kernel and GitHub Actions; the Palomar
  registration of Theorem 1 alone (`PALOMAR-2026-09-18-000007`, automated
  editorial review); no human review; no novelty certified; the Lean code
  written with AI coding agents under the author's direction; how to rebuild.

Around it: one sentence at the end of the abstract pointing to the appendix; a
label on Remark 5; references for Lean 4 and Mathlib, whose DOIs and pages were
checked against the publishers' pages; PDF title and author metadata; the date
line "September 5, 2026 — revised September 30, 2026".

## Checks

- `latexmk -pdf -interaction=nonstopmode -halt-on-error`: exit 0; six A4 pages;
  the log has no LaTeX warning, undefined reference, overfull or underfull
  box. The declaration list is set ragged right, so long Lean names move to the
  next line instead of overflowing.
- `chktex -q`: exit 0. Five local suppressions: the three earlier ones, the
  Riemann–Hurwitz en dash in the appendix, and the hyphens of the registry
  identifier.
- `pdfinfo`: Title "Sharp symmetry bounds for real algebraic curves", Author
  "Carlo Perassi".
- All six pages rendered and inspected: equations, overbars, the list of
  declarations, references and page flow. No defect found.
- `uv run verify.py`: exit 0, 2,082 exact checks.
- Lean sources are unchanged since `b8c207e`; the full clean `lean/check.sh`
  last passed on that tree at the Sprint 4 gate, and CI reruns it on this
  commit.

Gate (SPRINTS.md): paper, formal statements, metadata and verification
evidence agree at one commit, this one. A tag `sprint-7-complete` needs the
user's word.
