# Auditing natural-language statements against the elaborated Lean types

You check, independently, whether each natural-language statement says exactly what the
Lean theorem says. You did not write these texts; assume nothing about their quality.

## Input

`p2m/meta/audit_NN.json` (paths relative to
`<port>/`). For each item:

- `elaborated_type`: the theorem's type as Lean elaborated it, pretty-printed with full
  names. This is the ground truth: every binder (explicit, implicit `{}`, instance `[]`),
  every hypothesis, the exact conclusion.
- `formal_statement` and `preamble_context`: the source text (for readability).
- `definitions_used`, with their Lean text in the file's `definitions` list. For a
  definition not listed there, read the original source, read-only:
  `<repo>/lean/<Module>.lean`.
- `theorem_title` and `natural_language_statement`: the text under audit.

## What to check, per item

1. Hypotheses: every hypothesis of the elaborated type appears in the text (instance
   arguments such as `[Fact (0 < m)]` are hypotheses too), and the text adds none that
   the type lacks. A text may say a hypothesis is absent compared with the note; that is
   fine.
2. Quantifiers and conclusion: same quantifier structure, same direction of
   implications, iff stays iff, existence stays existence, the exact objects (a subset of
   ℂ is not a projective curve; "into" is not "onto"; `Nat.card`/`finrank` conventions).
3. Definitions: each symbol the text defines matches the Lean definition (formula,
   conventions, which root or which representative is chosen).
4. The title does not claim more than the statement.

Only report real mismatches of meaning. Style, notation choices and the role paragraph's
wording are not your concern unless they misstate the theorem. Do not suggest proofs.

## Output

Write `p2m/meta/audit_out/audit_NN.json`, a JSON array in input order:

```json
[{"theorem_name": "CurveSymmetry.…", "verdict": "faithful" | "mismatch",
  "issues": ["one sentence per mismatch: what the text says vs what Lean says"]}]
```

Use `json.dump` from a short Python script. Write nothing else, no network, no API, no
Lean builds, nothing under `<Prove2Me workspace>`.
