# Writing titles and natural-language statements (package 4)

You write the human-readable metadata of Lean theorems that will be published on the
Prove2Me platform, from the formalization of C. Perassi's note *Sharp symmetry bounds
for real algebraic curves*. Readers are mathematicians browsing a catalogue. You write
only two fields per theorem: `theorem_title` and `natural_language_statement`. The
`source` and `tags` fields are computed elsewhere; do not write them.

## Inputs

- Your batch file `p2m/meta/batch_NN.json` (paths below are relative to
  `<port>/`). For each theorem:
  - `formal_statement` is the exact Lean statement; `preamble_context` holds the
    `open`/`variable` lines in force. This is what you describe, nothing else.
  - `original_docstring` is the author's comment, often a good start; when it says
    more or less than the Lean statement, the Lean statement wins.
  - `definitions_used`, with each definition's Lean text and docstring in the batch
    file's `definitions` list: read them to know what every symbol means.
  - `note_statements` (where the note states this, with page) and `supports` (the
    note's statements it is used for), plus `used_by_nodes`: material for the role
    paragraph.
- The note itself: `<repo>/sharp_symmetry_bounds.tex`
  (read-only). Use its notation whenever the Lean object is the note's object:
  $C$, $\mathrm{Sym}(C)$, $\mathrm{Sym}^+(C)$, $C_{m,\alpha}$, $\widehat C_{m,\alpha}$,
  $P_\alpha$, $V_\alpha$, the double cover, and so on.
- The original Lean sources, read-only, if you need more context:
  `<repo>/lean/<Module>.lean`.

## The natural-language statement

Markdown with KaTeX: `$...$` inline, `$$...$$` display. Write it like a paper or
lecture note, not a Lean dump.

1. First paragraph(s): the setting. Introduce every object and variable with its
   meaning and type in conventional notation (for example: "Let $m\ge 1$ be an
   integer and $\alpha\in\mathbb C$ with $\alpha\ne\bar\alpha$ …"). Replace Lean
   names (`realLocus P`, `familyH m α`) by notation you define (the real zero set
   $\{z\in\mathbb C : P(\operatorname{Re} z,\operatorname{Im} z)=0\}$, the polynomial
   $H_{m,\alpha}(t)$ …).
2. The statement, with the main formula in a display block `$$ … $$`. Use a numbered
   list when the theorem has several parts (conjunctions).
3. One short paragraph on its role: what it is for in the note or in the
   formalization ("This is the genus clause of Lemma 4 of the note"; "Used to show
   that the two charts glue …"). Cite the note by statement number only (Theorem 1,
   Lemma 4, Remark 5, equation (5)).
4. Optional, last: a paragraph beginning `**Formalization Note**` for Lean-specific
   encodings a reader needs (hypotheses passed as `Fact` instances, a curve given as
   a subset of $\mathbb C$, isometries as `ℂ ≃ᵢ ℂ`, the Riemann sphere as
   `OnePoint ℂ`, a genus defined through places and holomorphic differentials of the
   function field, …). Keep it short.

Faithfulness is the main requirement:
- State exactly what the Lean statement asserts: every hypothesis (including those
  hidden in `variable`, `Fact` or instance arguments), every quantifier, the exact
  conclusion. Do not strengthen, weaken or "improve" it. An iff stays an iff; an
  existence statement stays one; a statement about a subset of $\mathbb C$ is not
  silently a statement about a projective curve.
- If the Lean statement is a technical step (a chart identity, a membership, an
  equation between explicit polynomials), describe that step precisely; do not
  replace it with the theorem of the note it serves.
- No proof details or proof sketches.

Wording rules (the account owner's, non-negotiable):
- Never "new", "novel", "first", "for the first time", "original", "breakthrough" or
  similar claims about the mathematics.
- No line numbers, no LaTeX labels (`thm:…`, `eq:…`), no file names, no internal
  ledger identifiers (`T1.1`, `S04`, `G09`, `R01` …), no mention of AI or of how the
  Lean was written.
- No Lean identifiers in the title; in the statement only inside the Formalization
  Note, in backticks, when unavoidable.

## The title

Plain, specific, at most 120 characters, inline KaTeX allowed. When
`note_statements` names a statement of the note *and* this theorem is that statement
(its name starts with `paper_`, or the docstring says so), start with the index:
"Theorem 1 (sharp bounds): …", "Lemma 4: …", "Remark 5: …". Otherwise a descriptive
title ("Uniformizer of the quadratic local ring at a ramified point").

## Output

Write `p2m/meta/out/batch_NN.json` (create `p2m/meta/out/` if missing): a JSON array
with one object per theorem of your batch, in batch order:

```json
[{"theorem_name": "CurveSymmetry.…", "theorem_title": "…", "natural_language_statement": "…"}]
```

For the definition files (`batch_defs.json`) the objects are
`{"definition_name": "CurveSymmetry_NN_…", "definition_title": "…", "natural_language_statement": "…"}`:
the statement describes the main objects the file defines (setting, notation,
the key definitions as displayed formulas or a numbered list, then their role),
under the same rules.

Write the file with a short Python script (`json.dump(..., ensure_ascii=False,
indent=1)`) holding your texts in raw strings, so LaTeX backslashes are escaped
correctly. Then reload it with `json.load` and check: every name of the batch appears
exactly once, every statement has a display block (`$$`), and dollar signs balance.

Do not change any other file. Do not access the network or any API.
