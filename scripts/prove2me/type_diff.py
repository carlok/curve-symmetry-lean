#!/usr/bin/env python3
"""Phase 5 type diff: pretty-print the elaborated type of every node from the
original library and from the generated stubs, then diff. Universe-name
differences are the only acceptable ones."""
import json, os, subprocess, sys
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
g = json.load(open(os.path.join(ROOT, 'p2m', 'generated.json'), encoding='utf-8'))
names = [n['name'] for n in g['nodes']]
NORMTXT = open(os.path.join(ROOT, 'p2m', 'norm_expr.lean.txt'), encoding='utf-8').read()
chk = subprocess.run(['lake', 'env', 'lean', 'p2m/instance_equivalences.lean'], cwd=ROOT, capture_output=True, text=True)
if chk.returncode != 0:
    raise SystemExit('instance_equivalences.lean does not compile: ' + chk.stdout[-800:])
body = (NORMTXT + '\nopen Lean Meta in\nrun_meta do\n  for n in [' + ', '.join('`' + x for x in names) + '] do\n'
        '    let ci ← getConstInfo n\n'
        '    let t ← ppExpr ci.type\n'
        '    let t2 ← withOptions (fun o => o.setBool `pp.all true) (ppExpr ci.type)\n'
        '    IO.println s!"{n} ::: {ci.levelParams} ::: {hash (toString t2)} ::: {(normE ci.type).hash} ::: {t.pretty 1000000}"\n')
orig = 'import CurveSymmetry\n' + body
staged = ''.join(f"import Theorems.{n['stub']}\n" for n in g['nodes']) + body
out = {}
for tag, src in (('orig', orig), ('staged', staged)):
    path = os.path.join(ROOT, 'p2m', f'typedump_{tag}.lean')
    open(path, 'w', encoding='utf-8').write(src)
    r = subprocess.run(['lake', 'env', 'lean', path], cwd=ROOT, capture_output=True, text=True)
    lines = [l for l in r.stdout.splitlines() if not l.startswith('p2m/') and ':' in l]
    out[tag] = lines
    open(os.path.join(ROOT, 'p2m', f'typedump_{tag}.txt'), 'w', encoding='utf-8').write('\n'.join(lines) + '\n')
    if r.returncode != 0:
        print(tag, 'exit', r.returncode, r.stdout[-2000:], r.stderr[-1000:])
def parse(lines):
    d = {}
    for l in lines:
        parts = l.split(' ::: ', 4)
        if len(parts) == 5:
            d[parts[0]] = parts[1:]
    return d
a, b = parse(out['orig']), parse(out['staged'])
missing = sorted(set(a) ^ set(b))
pp_diff = [n for n in a if n in b and a[n][3] != b[n][3]]
norm_diff = [n for n in a if n in b and a[n][2] != b[n][2]]
all_diff = [n for n in a if n in b and a[n][1] != b[n][1]]
lvl_diff = [n for n in a if n in b and a[n][0] != b[n][0]]
print(f'nodes {len(names)}; types printed: orig {len(a)}, staged {len(b)}; missing {len(missing)}')
print(f'differing: pretty {len(pp_diff)}, pp.all {len(all_diff)}, universe params {len(lvl_diff)}; '
      f'after the normalization (auxiliary proofs, proved instance equalities): {len(norm_diff)}')
for n in (pp_diff + norm_diff + lvl_diff)[:10]:
    print('ORIG  :', n, a[n][0], a[n][3][:300]); print('STAGED:', n, b[n][0], b[n][3][:300])
