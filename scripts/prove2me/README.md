# Scripts of the Prove2Me upload

These scripts turned this repository into the Prove2Me mission
[Sharp symmetry bounds for real algebraic curves](https://prove2.me/missions/Sharp_symmetry_bounds_for_real_algebraic_curves).
The record of what was uploaded and checked is `verification/PROVE2ME.md`.

They ran in a separate port project, not in this repository. That project held the
same `lean/` sources ported to the platform's environment (Lean v4.33.1, Mathlib
`0df444a`). Paths are relative to that layout: sources in `lean/`, the scripts in
`p2m/`, generated files in `p2m/platform/`. The briefs refer to it as `<port>/` and to
this repository as `<repo>/`. The scripts follow Prove2Me's `upload_full_project`
playbook and use its extraction scripts (`extract_decl_graph.lean`,
`extract_sketch_info.lean`), which are not copied here.

| file | role |
|---|---|
| `extract_cmd_facts.lean` | exact span and kind of every top-level command (namespaces, sections, opens, variables, local attributes) |
| `generate.py` | the platform tree: definition files, statement stubs, solutions |
| `type_diff.py` | node statements against the original library |
| `def_diff.py` | constants of the definition files against the original library |
| `check_solutions.py`, `check_solutions.lean` | each `solution` has its statement's type; axioms |
| `instance_equivalences.lean`, `norm_expr.lean.txt` | the instance equality both comparisons rely on, and the shared normalization |
| `meta_context.py`, `meta_check.py`, `RULES.md`, `AUDIT.md` | titles, statements, sources, tags: inputs, writing rules, checks, audit brief |
| `expl_check.py`, `RULES_EXPLAIN.md` | proof explanations: writing rules and checks |
| `upload.py` | the uploader: definitions, statements, proofs, explanations, proposal |

`upload.py` calls the platform only through the workspace wrapper `p2m.sh`, which
holds the account key. Nothing here contains credentials.

The titles, statements and explanations were written by AI agents from these briefs,
then checked by the scripts and by independent audit agents.
