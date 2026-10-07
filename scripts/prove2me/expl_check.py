#!/usr/bin/env python3
"""Package 5b check: the writers' proof explanations (p2m/meta/expl_out/batch_*.json)
against the platform's rules and Carlo's wording rules; writes
p2m/meta/final_explanations.json ({theorem name: explanation}) when nothing fails."""
import glob, json, os, re, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
META = os.path.join(ROOT, 'p2m', 'meta')
g = json.load(open(os.path.join(ROOT, 'p2m', 'generated.json'), encoding='utf-8'))
want = [n['name'] for n in g['nodes']]

BAD_MACROS = re.compile(r'\\(C|R|PP|Sym|Rea|N|Z|Q)(?![A-Za-z])|\\(ref|eqref|label|cite|newcommand|DeclareMathOperator)\b')
NOVELTY = re.compile(r'\b(new|novel|first|original|breakthrough|unprecedented)\b', re.I)
PRAISE = re.compile(r'\b(elegant|clever|beautiful|trick|neat|nice)\b', re.I)
LEDGER = re.compile(r'\b(T[12]\.\d|S\d\d|G\d\d|R0\d)\b')
LABELS = re.compile(r'\b(thm|lem|eq|rem|sec|app):[a-z]|\bline \d|\.lean\b|COVERAGE|\bledger\b', re.I)
AI = re.compile(r'\b(AI|LLM|Claude|GPT|language model|agents?)\b')
META_TALK = re.compile(r'\b(I|we tried|attempt(s|ed)?|the platform|Prove2Me)\b')

def segments(s):
    s2 = s.replace(r'\$', '')
    disp = re.findall(r'\$\$(.+?)\$\$', s2, re.S)
    rest = re.sub(r'\$\$(.+?)\$\$', ' ', s2, flags=re.S)
    inl = re.findall(r'\$(.+?)\$', rest, re.S)
    return disp, inl, re.sub(r'\$(.+?)\$', ' ', rest, flags=re.S)

def braces_ok(t):
    depth = 0
    for ch in re.sub(r'\\[{}]', '', t):
        depth += (ch == '{') - (ch == '}')
        if depth < 0:
            return False
    return depth == 0

out = {}
for f in sorted(glob.glob(os.path.join(META, 'expl_out', 'batch_*.json'))):
    for e in json.load(open(f, encoding='utf-8')):
        out[e['theorem_name']] = e['explanation']

errors, warns = {}, {}
for n in want:
    t = out.get(n)
    if not t:
        errors[n] = ['missing']
        continue
    er, wa = [], []
    disp, inl, left = segments(t)
    if not disp:
        er.append('no display block')
    if '$' in left:
        er.append('unbalanced dollar signs')
    if any('\\\\' in x for x in inl):
        er.append('row break inside inline math')
    if not all(braces_ok(x) for x in disp + inl):
        er.append('unbalanced braces in math')
    if len(t) > 50000:
        er.append('longer than 50,000 characters')
    for rx, what in ((BAD_MACROS, 'non-KaTeX macro'), (LEDGER, 'ledger id'), (LABELS, 'label/line/file'),
                     (AI, 'AI mention'), (PRAISE, 'praise word'), (META_TALK, 'commentary')):
        m = rx.search(re.sub(r'`[^`]*`', '', t) if rx is not BAD_MACROS else t)
        if m:
            (er if rx in (BAD_MACROS, LEDGER, LABELS, AI) else wa).append(f'{what}: {m.group(0)!r}')
    for m in NOVELTY.finditer(re.sub(r'`[^`]*`', '', t)):
        wa.append('"' + t[max(0, m.start() - 25):m.end() + 25].replace('\n', ' ') + '"')
    if er:
        errors[n] = er
    if wa:
        warns[n] = wa

lens = sorted(len(out[n].split()) for n in out)
print(f'explanations {len(out)}/{len(want)}; errors {len(errors)}; warnings {len(warns)}; '
      f'words: median {lens[len(lens) // 2] if lens else 0}, max {lens[-1] if lens else 0}')
for n, e in list(errors.items())[:30]:
    print('ERROR', n, '|', '; '.join(e))
for n, w in list(warns.items())[:30]:
    print('warn ', n, '|', '; '.join(w)[:240])
if not errors:
    json.dump({n: out[n] for n in want}, open(os.path.join(META, 'final_explanations.json'), 'w', encoding='utf-8'),
              indent=1, ensure_ascii=False)
sys.exit(1 if errors else 0)
