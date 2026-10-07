#!/usr/bin/env python3
"""Phase 5 checks on the built Solutions library:
1. `solution` has exactly the statement's elaborated type (p2m/check_solutions.lean);
2. axioms: only propext, Classical.choice, Quot.sound, plus sorryAx when, and only
   when, the solution imports statement stubs (Open nodes on the platform);
3. no `sorry` written in any solution file.
Reads the given lake build log for the `#print axioms` output."""
import json, os, re, subprocess, sys
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LOG = sys.argv[1] if len(sys.argv) > 1 else os.path.join(ROOT, 'p2m', 'build_all.log')
g = json.load(open(os.path.join(ROOT, 'p2m', 'generated.json'), encoding='utf-8'))
LIB = os.path.join(ROOT, '.lake', 'build', 'lib', 'lean')
pairs = []
for n in g['nodes']:
    sol = n['stub'].replace('Thm_', 'Sol_', 1)
    pairs.append(f"{LIB}/Solutions/{sol}.olean {LIB}/Theorems/{n['stub']}.olean {n['name']}")
open(os.path.join(ROOT, 'p2m', 'sol_pairs.txt'), 'w', encoding='utf-8').write('\n'.join(pairs) + '\n')
r = subprocess.run(['lake', 'env', 'lean', '--run', 'p2m/check_solutions.lean', 'p2m/sol_pairs.txt'],
                   cwd=ROOT, capture_output=True, text=True)
print(r.stdout.strip(), r.stderr.strip()[-1000:])
ok = r.returncode == 0

log = open(LOG, encoding='utf-8').read()
STD = {'propext', 'Classical.choice', 'Quot.sound'}
ax = {}
for m in re.finditer(r'Solutions/(Sol_\w+)\.lean:\d+:\d+: .solution. depends on axioms: \[([^\]]*)\]', log):
    ax[m.group(1)] = {a.strip() for a in m.group(2).split(',') if a.strip()}
sol_dir = os.path.join(ROOT, 'p2m', 'platform', 'Solutions')
files = sorted(f[:-5] for f in os.listdir(sol_dir) if f.endswith('.lean'))
missing_ax, extra, sorry_mismatch, written_sorry, with_stubs = [], [], [], [], 0
for f in files:
    text = open(os.path.join(sol_dir, f + '.lean'), encoding='utf-8').read()
    imports_stubs = bool(re.search(r'^import Theorems\.', text, re.M))
    with_stubs += imports_stubs
    if re.search(r'\bsorry\b', re.sub(r'--.*', '', text)):
        written_sorry.append(f)
    if f not in ax:
        missing_ax.append(f)
        continue
    if ax[f] - STD - {'sorryAx'}:
        extra.append((f, ax[f] - STD))
    if ('sorryAx' in ax[f]) != imports_stubs:
        sorry_mismatch.append(f)
print(f'solutions {len(files)}: axiom reports {len(ax)}, missing {len(missing_ax)}; '
      f'non-standard axioms {len(extra)}; sorryAx without stub imports or the reverse {len(sorry_mismatch)}; '
      f'`sorry` written in a solution {len(written_sorry)}')
print(f'closed solutions (no stub imports, standard axioms only): {len(files) - with_stubs}; '
      f'solutions importing Open stubs: {with_stubs}')
for x in (missing_ax + extra + sorry_mismatch + written_sorry)[:10]:
    print('  ', x)
ok = ok and not (missing_ax or extra or sorry_mismatch or written_sorry)
sys.exit(0 if ok else 1)
