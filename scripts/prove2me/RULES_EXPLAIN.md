# Writing proof explanations (package 5b)

Each theorem of the formalization of C. Perassi's note *Sharp symmetry bounds for real
algebraic curves* is published on Prove2Me with a Lean proof that the platform has
accepted. You write the `explanation` attached to each proof: the text a mathematician
reads to follow the argument and see how it maps onto the Lean code.

## Inputs

`p2m/meta/expl_batch_NN.json` (paths relative to
`<port>/`). For each theorem:

- `theorem_title`, `natural_language_statement`: what is proved (already written and
  audited; reuse its notation).
- `solution_file`: the exact Lean proof that was accepted, with the helper lemmas it
  proves inline above `theorem solution`. Read it. This is the argument you explain.
- `imported_nodes`: other theorems of the mission that this proof imports (each is
  itself proved on the platform), with their titles.
- `original_docstring`, `note_place`: context; the note itself is at
  `<repo>/sharp_symmetry_bounds.tex`
  (read-only), and the original Lean sources at
  `<repo>/lean/` (read-only).

## The explanation (the platform's rules)

Markdown with KaTeX (`$...$`, `$$...$$`), written like a section of a paper, not a
tactic-by-tactic transcript.

1. Open with what is proved: the statement in a display block, and the hypotheses the
   argument actually uses.
2. The proof idea in a short paragraph: the observation that makes the argument work
   and the technique it belongs to.
3. The argument in steps, each saying what is shown and why it follows. Put every
   formula longer than a symbol or two in display math. When the proof uses an imported
   theorem of the mission, say what that theorem asserts (by its title, with the Lean
   name in backticks) and how it is used. When it uses helper lemmas proved inline,
   say what each one establishes.
4. Optional, last: a paragraph beginning `**Formalization Note**` naming the main Lean
   or Mathlib facts the proof rests on (in backticks), when that helps a reader map the
   prose onto the code.

Rules:
- Explain the argument the Lean proof actually makes. If it follows the note's proof,
  you may say which step of the note it formalizes (by statement number only); if it
  argues differently, describe the Lean route.
- No commentary about the writer, the platform, how the proof was obtained or how many
  attempts it took. No "elegant", "clever", "beautiful", "trick".
- No "new", "novel", "first", "original"; no line numbers, LaTeX labels, file names or
  internal ledger identifiers (`T1.1`, `G09`, `R01` …); no mention of AI.
- KaTeX only: no `\C`, `\R`, `\PP`, `\Sym`, `\Rea` (write `\mathbb C`, `\mathbb R`,
  `\mathbb P`, `\operatorname{Sym}`, `\operatorname{Re}`); no `\\` row breaks inside
  inline math (use display math for matrices and multi-line formulas); display blocks in
  their own paragraphs; separate paragraphs with a blank line.
- Length follows the proof: about 120 words for a short computation, up to 700-900 for
  the longest proofs, which you summarise by their structure rather than line by line.

## Output

Write `p2m/meta/expl_out/batch_NN.json`: a JSON array, in batch order,
`[{"theorem_name": "CurveSymmetry.…", "explanation": "…"}]`, with a short Python script
(`json.dump(..., ensure_ascii=False, indent=1)`, texts in raw strings). Reload it and
check: every name once, each explanation has a display block, dollar signs balance.

Do not change any other file. No network, no API, no Lean builds, nothing under
`<Prove2Me workspace>`.
