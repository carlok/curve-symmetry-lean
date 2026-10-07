#!/usr/bin/env python3
"""Package 4 check and merge. Reads the writers' p2m/meta/out/batch_*.json, checks
every entry against the rules (completeness, display math, balanced dollars and
braces, KaTeX-safe macros, the account owner's wording rules), and merges the
passing ones with p2m/meta/fixed.json (source, tags) and the exact upload text
(preamble, formal statement, definition file) into p2m/meta/final_nodes.json and
p2m/meta/final_defs.json, plus p2m/meta/PREVIEW.md for reading.
Exit 1 when an error remains; warnings are listed for a human look."""
import glob, json, os, re, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
META = os.path.join(ROOT, 'p2m', 'meta')
PLAT = os.path.join(ROOT, 'p2m', 'platform')
g = json.load(open(os.path.join(ROOT, 'p2m', 'generated.json'), encoding='utf-8'))
fixed = json.load(open(os.path.join(META, 'fixed.json'), encoding='utf-8'))
want_nodes = [n['name'] for n in g['nodes']]
want_defs = [b[len('Def_'):] for b in g['bundles']]

BAD_MACROS = re.compile(r'\\(C|R|PP|Sym|Rea|N|Z|Q)(?![A-Za-z])|\\(ref|eqref|label|cite|newcommand|DeclareMathOperator)\b')
NOVELTY = re.compile(r'\b(new|novel|first|original|breakthrough|unprecedented)\b', re.I)
LEDGER = re.compile(r'\b(T[12]\.\d|S\d\d|G\d\d|R0\d)\b')
LABELS = re.compile(r'\b(thm|lem|eq|rem|sec|app):[a-z]|\bline \d|\.lean\b|COVERAGE|\bledger\b', re.I)
AI = re.compile(r'\b(AI|LLM|Claude|GPT|language model|agents?)\b')

def math_segments(s):
    """($$…$$ and $…$ segments, leftover text) with escaped dollars ignored."""
    s2 = s.replace(r'\$', '')
    disp = re.findall(r'\$\$(.+?)\$\$', s2, re.S)
    rest = re.sub(r'\$\$(.+?)\$\$', ' ', s2, flags=re.S)
    inl = re.findall(r'\$(.+?)\$', rest, re.S)
    left = re.sub(r'\$(.+?)\$', ' ', rest, flags=re.S)
    return disp, inl, left

def braces_ok(t):
    depth = 0
    t = re.sub(r'\\[{}]', '', t)
    for ch in t:
        depth += (ch == '{') - (ch == '}')
        if depth < 0:
            return False
    return depth == 0

def check(title, nl, kind):
    errs, warns = [], []
    if not title or not nl:
        return ['empty title or statement'], warns
    if len(title) > 200:
        errs.append(f'title longer than 200 characters ({len(title)})')
    elif len(title) > 120:
        warns.append(f'title of {len(title)} characters')
    if '`' in title or 'CurveSymmetry' in title:
        errs.append('Lean identifier in the title')
    disp, inl, left = math_segments(nl)
    if not disp:
        errs.append('no display block ($$ … $$)')
    if '$' in left:
        errs.append('unbalanced dollar signs')
    for seg in inl + math_segments(title)[1]:
        if '\\\\' in seg:
            errs.append(f'row break inside inline math (Markdown may eat it): ${seg[:60]}$')
            break
    for seg in disp + inl + math_segments(title)[1]:
        if not braces_ok(seg):
            errs.append(f'unbalanced braces in ${seg[:60]}$')
            break
    for field, text in (('title', title), ('statement', nl)):
        m = BAD_MACROS.search(text)
        if m:
            errs.append(f'macro {m.group(0)} in the {field} (not KaTeX)')
        for rx, what in ((LEDGER, 'ledger identifier'), (LABELS, 'label, line, file or ledger reference'),
                         (AI, 'mention of AI or agents')):
            m = rx.search(text)
            if m:
                errs.append(f'{what} in the {field}: {m.group(0)!r}')
        for m in NOVELTY.finditer(text):
            ctx = text[max(0, m.start() - 30):m.end() + 30].replace('\n', ' ')
            warns.append(f'"{m.group(0)}" in the {field}: …{ctx}…')
    if 'CurveSymmetry.' in nl.split('**Formalization Note**')[0]:
        warns.append('Lean name outside the Formalization Note')
    return errs, warns

out = {}
for f in sorted(glob.glob(os.path.join(META, 'out', 'batch_*.json'))):
    try:
        for e in json.load(open(f, encoding='utf-8')):
            key = e.get('theorem_name') or e.get('definition_name')
            if key in out:
                print('DUPLICATE', key, os.path.basename(f))
            out[key] = e
    except Exception as ex:
        print('UNREADABLE', os.path.basename(f), ex)

n_err = 0
final_nodes, final_defs, report = [], [], []
nodes_by = {n['name']: n for n in g['nodes']}
for n in want_nodes:
    e = out.get(n)
    if e is None:
        report.append((n, ['missing'], []))
        n_err += 1
        continue
    errs, warns = check(e.get('theorem_title', ''), e.get('natural_language_statement', ''), 'thm')
    report.append((n, errs, warns))
    n_err += bool(errs)
    t = open(os.path.join(PLAT, 'Theorems', nodes_by[n]['stub'] + '.lean'), encoding='utf-8').read()
    m = re.search(r'^theorem\s', t, re.M)
    preamble = '\n'.join(l for l in t[:m.start()].rstrip().split('\n') if not l.startswith('--')).strip()
    final_nodes.append(dict(theorem_name=n, theorem_title=e['theorem_title'],
                            formal_statement=t[m.start():].rstrip(),
                            natural_language_statement=e['natural_language_statement'],
                            preamble=preamble, source=fixed[n]['source'], tags=fixed[n]['tags']))
for d in want_defs:
    e = out.get(d)
    if e is None:
        report.append((d, ['missing'], []))
        n_err += 1
        continue
    errs, warns = check(e.get('definition_title', ''), e.get('natural_language_statement', ''), 'def')
    report.append((d, errs, warns))
    n_err += bool(errs)
    body = open(os.path.join(PLAT, 'Definitions', 'Def_' + d + '.lean'), encoding='utf-8').read()
    final_defs.append(dict(definition_name=d, definition_title=e['definition_title'], definition=body,
                           natural_language_statement=e['natural_language_statement'],
                           source=fixed['Def_' + d]['source'], tags=fixed['Def_' + d]['tags']))

json.dump(final_nodes, open(os.path.join(META, 'final_nodes.json'), 'w', encoding='utf-8'), indent=1, ensure_ascii=False)
json.dump(final_defs, open(os.path.join(META, 'final_defs.json'), 'w', encoding='utf-8'), indent=1, ensure_ascii=False)
with open(os.path.join(META, 'PREVIEW.md'), 'w', encoding='utf-8') as fp:
    fp.write('# Metadata preview (package 4)\n\nDefinition files first, then the theorems in source order.\n\n')
    for d in final_defs:
        fp.write(f"## {d['definition_title']}\n\n`{d['definition_name']}` · tags: {', '.join(d['tags'])}\n\n"
                 f"{d['natural_language_statement']}\n\n*Source:* {d['source']}\n\n---\n\n")
    for x in final_nodes:
        fp.write(f"## {x['theorem_title']}\n\n`{x['theorem_name']}` · tags: {', '.join(x['tags'])}\n\n"
                 f"{x['natural_language_statement']}\n\n*Source:* {x['source']}\n\n---\n\n")

errs = [(k, e) for k, e, w in report if e]
warns = [(k, w) for k, e, w in report if w]
print(f'entries {len(out)}: theorems {len(final_nodes)}/{len(want_nodes)}, definition files {len(final_defs)}/{len(want_defs)}; '
      f'with errors {len(errs)}, with warnings {len(warns)}')
for k, e in errs[:40]:
    print('ERROR', k, '|', '; '.join(e))
for k, w in warns[:40]:
    print('warn ', k, '|', '; '.join(w)[:300])
sys.exit(1 if n_err else 0)
