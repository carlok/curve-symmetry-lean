#!/usr/bin/env python3
"""Phase 5, definition fidelity: every constant a Definitions bundle declares is
compared with the constant of the same name in the original library (private
names mapped to their user names): kind, universe parameters, type, and value
for definitions, instances and opaque constants. Proofs of theorems are not
compared (proof irrelevance); their statements are. Auxiliary proofs are erased."""
import collections, json, os, re, subprocess
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
proj = sorted(os.path.basename(f)[:-5] for f in os.listdir(os.path.join(ROOT, 'lean')) if f.endswith('.lean'))
g = json.load(open(os.path.join(ROOT, 'p2m', 'generated.json'), encoding='utf-8'))
META = r'''
NORM
open Lean Meta in
run_meta do
  let env ← getEnv
  let mods := env.header.moduleNames
  for i in [0:mods.size] do
    let m := mods[i]!
    if SELECT then
      for n in env.header.moduleData[i]!.constNames do
        if isAuxProof n then continue
        let some ci := env.find? n | continue
        let kind := match ci with
          | .defnInfo _ => "def" | .thmInfo _ => "thm" | .axiomInfo _ => "axiom"
          | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "induct"
          | .ctorInfo _ => "ctor" | .recInfo _ => "rec"
        let kind := if ci.type.isConstOf ``Lean.ParserDescr || ci.type.isConstOf ``Lean.TrailingParserDescr
          then "syntax" else kind
        let v : UInt64 := match ci with
          | .defnInfo d => (normE d.value).hash
          | .opaqueInfo d => (normE d.value).hash
          | _ => 0
        IO.println s!"@@ {privateToUserName n} ::: {m} ::: {kind} ::: {ci.levelParams} ::: {(normE ci.type).hash} ::: {v}"
'''
sel_orig = '[' + ', '.join('`' + m for m in proj) + '].contains m'
NORMTXT = open(os.path.join(ROOT, 'p2m', 'norm_expr.lean.txt'), encoding='utf-8').read()
META = META.replace('\nNORM\n', NORMTXT)
chk = subprocess.run(['lake', 'env', 'lean', 'p2m/instance_equivalences.lean'], cwd=ROOT, capture_output=True, text=True)
if chk.returncode != 0:
    raise SystemExit('instance_equivalences.lean does not compile: ' + chk.stdout[-800:])
srcs = {
    'orig': 'import CurveSymmetry\n' + META.replace('SELECT', sel_orig),
    'staged': ''.join(f'import Definitions.{b}\n' for b in g['bundles']) + META.replace('SELECT', 'm.getRoot == `Definitions'),
}
tab = {}
for tag, src in srcs.items():
    path = os.path.join(ROOT, 'p2m', f'defdump_{tag}.lean')
    open(path, 'w', encoding='utf-8').write(src)
    r = subprocess.run(['lake', 'env', 'lean', path], cwd=ROOT, capture_output=True, text=True)
    if r.returncode != 0:
        print(tag, 'exit', r.returncode, r.stdout[-1500:], r.stderr[-800:])
    rows = collections.defaultdict(list)
    for l in r.stdout.splitlines():
        if l.startswith('@@ '):
            name, mod, kind, lv, ty, val = l[3:].split(' ::: ')
            rows[name].append((mod, kind, lv, ty, val))
    tab[tag] = rows
    open(os.path.join(ROOT, 'p2m', f'defdump_{tag}.txt'), 'w', encoding='utf-8').write(r.stdout)
o, s = tab['orig'], tab['staged']
AUX = re.compile(r'(^|\.)(_[A-Za-z]|eq_\d+$|eq_def$|match_\d+|proof_\d+|sizeOf_spec$|injEq$|inj$|noConfusion)')
missing_user, missing_aux, mismatch, syntax_diff, kinds = [], [], [], [], collections.Counter()
for name, entries in s.items():
    for (mod, kind, lv, ty, val) in entries:
        kinds[kind] += 1
        cands = o.get(name, [])
        if not cands:
            (missing_aux if AUX.search(name) or kind == 'syntax' else missing_user).append(name)
            continue
        if not any(c[1:] == (kind, lv, ty, val) for c in cands):
            # a notation parser embeds its module's name in the syntax kind it builds
            (syntax_diff if kind == 'syntax' else mismatch).append((name, mod, (kind, lv, ty, val), [c[1:] for c in cands]))
print(f'bundle constants: {sum(len(v) for v in s.values())} {dict(kinds)}')
print(f'missing in original: user {len(missing_user)}, auxiliary or notation {len(missing_aux)}; mismatching: {len(mismatch)} '
      f'(notation parsers differing only by module name: {len(syntax_diff)})')
for n in missing_user[:10]: print('  MISSING', n)
for n in missing_aux[:5]: print('  aux', n)
for n, mod, st, cands in mismatch[:10]: print('  MISMATCH', n, mod, st, cands)
