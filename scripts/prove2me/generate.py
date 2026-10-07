#!/usr/bin/env python3
"""Package 3 generator for the Prove2Me upload of curve-symmetry-lean.

Inputs (all produced by Lean, never by pattern matching on declarations):
  decl_graph.jsonl          Stage 1 (platform script, project filter adapted)
  p2m/sketch/<M>.jsonl      Stage 2 (platform script): decl spans, proof cut, docstring, refs
  p2m/cmds/<M>.jsonl        Stage 2b: every top-level command with its kind and span
Output: p2m/platform/{Definitions,Theorems,Solutions}/*.lean and p2m/generated.json.

Plan (user decisions 2026-10-06): variant C targets, grain rule R1, definition
bundles named Def_CurveSymmetry_<Module>. Theorems referenced by definitions are
proved inside the bundles (closure). Nothing here talks to the platform.
"""
import collections
import glob
import json
import os
import re
import shutil
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(ROOT, 'p2m', 'platform')
COVERAGE = os.path.join(ROOT, '..', 'curve_symmetry', 'COVERAGE.md')
NS = 'CurveSymmetry'
BUNDLE_PREFIX = 'CurveSymmetry_'

# ---------------------------------------------------------------- inputs
rows = [json.loads(l) for l in open(os.path.join(ROOT, 'decl_graph.jsonl'), encoding='utf-8') if l.strip()]
by_name = {r['name']: r for r in rows}
mods_order = re.findall(r'^import (\w+)$', open(os.path.join(ROOT, 'lean', 'CurveSymmetry.lean'), encoding='utf-8').read(), re.M)
project_mods = set(mods_order)

M = {}
for mod in mods_order:
    path = os.path.join(ROOT, 'lean', mod + '.lean')
    text = open(path, 'rb').read()
    decls, refs, cmds = [], [], []
    for l in open(os.path.join(ROOT, 'p2m', 'sketch', mod + '.jsonl'), encoding='utf-8'):
        if l.startswith('{'):
            d = json.loads(l)
            (decls if d['kind'] == 'decl' else refs).append(d)
    for l in open(os.path.join(ROOT, 'p2m', 'cmds', mod + '.jsonl'), encoding='utf-8'):
        if l.startswith('{'):
            cmds.append(json.loads(l))
    cmds.sort(key=lambda c: c['start']['offset'])
    header = next(c for c in cmds if c['syntaxKind'] == 'header')
    imports = re.findall(rb'^import\s+([\w.]+)', text[header['start']['offset']:header['end']['offset']], re.M)
    M[mod] = dict(text=text, decls=decls, refs=refs, cmds=cmds,
                  imports=[i.decode() for i in imports])

def seg(mod, a, b):
    return M[mod]['text'][a:b].decode('utf-8')

# transitive project-import closure and non-project import union
closure = {}
for mod in mods_order:
    acc = set()
    for i in M[mod]['imports']:
        if i in project_mods:
            acc |= {i} | closure[i]
    closure[mod] = acc
nonproject = {mod: sorted({i for m2 in closure[mod] | {mod} for i in M[m2]['imports'] if i not in project_mods})
              for mod in mods_order}
pos_in_order = {m: k for k, m in enumerate(mods_order)}

# join Stage 1 rows to Stage 2 decl facts (containment) and decl facts to commands
def decl_of(r):
    for d in M[r['module']]['decls']:
        if d['declStart']['line'] <= r['startLine'] <= d['declEnd']['line']:
            return d
    return None

for r in rows:
    r['_decl'] = decl_of(r) if r['startLine'] and r['module'] in M else None

def proof_len(r):
    d = r['_decl']
    if d is None or not d.get('valStart'):
        return 0
    return d['declEnd']['line'] - d['valStart']['line']

# ---------------------------------------------------------------- classification (variant C)
cited = set(re.findall(r'`([A-Za-z_][A-Za-z0-9_\'.]*)`', open(COVERAGE, encoding='utf-8').read()))
targets = {r['name'] for r in rows if r['kind'] == 'theorem' and not r['isPrivate']
           and r['userName'].startswith(NS + '.') and r['userName'][len(NS) + 1:] in cited}
cov_text = open(COVERAGE, encoding='utf-8').read()
linked = set(re.findall(r'\(lean/([A-Za-z]+)\.lean\)', cov_text))
used_anywhere = {d for r in rows for d in r['valueDeps'] + r['typeDeps'] if d != r['name']}
for r in rows:
    if r['kind'] == 'theorem' and not r['isPrivate'] and r['startLine'] and r['name'] not in used_anywhere:
        L = proof_len(r)
        if (r['module'] in linked and L > 10) or L >= 3:
            targets.add(r['name'])

roots = set(targets) | {r['name'] for r in rows if r['isInstance']}
reach, work = set(), list(roots)
while work:
    n = work.pop()
    if n in reach or n not in by_name:
        continue
    reach.add(n)
    work.extend(by_name[n]['typeDeps'] + by_name[n]['valueDeps'])
reach = {n for n in reach if by_name[n]['startLine'] and by_name[n]['_decl'] is not None}

def is_local_instance(r):
    d = r['_decl']
    if d is None or r['module'] not in M:
        return False
    head = M[r['module']]['text'][d['declStart']['offset']:(d['valStart'] or d['declEnd'])['offset']]
    return b'local instance' in head or b'@[local instance' in head
local_inst = {r['name'] for r in rows if r['startLine'] and is_local_instance(r)}
reach |= {n for n in local_inst if by_name[n]['_decl'] is not None}

# `@[simp]` lemmas proved by `rfl` are used by unfolding and leave no trace in proof
# terms, so no dependency edge finds them. They go into the bundle of their module,
# next to the definitions they describe, whenever those definitions are reachable.
def is_rfl_simp(r):
    d = r['_decl']
    if d is None or r['kind'] != 'theorem' or r['module'] not in M or d['valStart'] is None:
        return False
    text = M[r['module']]['text']
    head = text[d['declStart']['offset']:d['valStart']['offset']]
    attrs = re.findall(rb'@\[([^\]]*)\]', head)
    if not any(re.search(rb'(^|[ ,])simp($|[ ,])', a.strip()) for a in attrs):
        return False
    body = text[d['valStart']['offset']:d['declEnd']['offset']].strip()
    return re.fullmatch(rb'(:=\s*)?(by\s+rfl|rfl|Iff\.rfl)', body) is not None
rfl_simp = {r['name'] for r in rows if r['startLine'] and is_rfl_simp(r)
            and all(d in reach for d in r['typeDeps'] if d in by_name and by_name[d]['startLine'])}
reach |= rfl_simp
inst = {n for n in reach if by_name[n]['isInstance']} | local_inst
reach_thms = {n for n in reach if by_name[n]['kind'] == 'theorem'}
# Bundle material: definitions that occur in the type of some reachable theorem, and
# every instance (instances vanish from terms but consumers need them), closed under
# their definition/instance dependencies.
seed = {d for n in reach_thms for d in by_name[n]['typeDeps']
        if d in reach and by_name[d]['kind'] != 'theorem'} | inst
defmat, work = set(), list(seed)
while work:
    u = work.pop()
    if u in defmat or u not in reach:
        continue
    if by_name[u]['kind'] == 'theorem' and u not in inst:
        continue
    defmat.add(u)
    work.extend(d for d in by_name[u]['typeDeps'] + by_name[u]['valueDeps']
                if d in reach and (by_name[d]['kind'] != 'theorem' or d in inst))
# Theorems used by bundle material are proved inside the bundles (playbook rule).
stmt_thms = {d for n in reach_thms for d in by_name[n]['typeDeps']
             if d in reach and by_name[d]['kind'] == 'theorem' and d not in inst}
embedded, work = set(), [d for u in defmat for d in by_name[u]['valueDeps'] + by_name[u]['typeDeps']] + list(stmt_thms) + list(rfl_simp)
while work:
    u = work.pop()
    if u in embedded or u not in reach or by_name[u]['kind'] != 'theorem' or u in inst:
        continue
    embedded.add(u)
    work.extend(by_name[u]['valueDeps'] + by_name[u]['typeDeps'])
# Definitions used only inside proofs are pasted into the solutions that use them.
proof_only_defs = {n for n in reach if by_name[n]['kind'] != 'theorem' and n not in defmat}

thms = reach_thms - embedded - inst
users = collections.Counter()
for n in reach:
    for d in set(by_name[n]['valueDeps']):
        if d in reach and d != n:
            users[d] += 1
nodes = {n for n in thms if n in targets or (not by_name[n]['isPrivate'] and (
         proof_len(by_name[n]) > 40 or (proof_len(by_name[n]) > 10 and users[n] >= 2)))}
inline = (thms - nodes) | proof_only_defs

# Declaration commands, keyed by (module, declStart offset).
def key(n):
    d = by_name[n]['_decl']
    return (by_name[n]['module'], d['declStart']['offset'])

bundle_keys = collections.defaultdict(set)
for n in defmat | embedded:
    k = key(n)
    bundle_keys[k[0]].add(k[1])
for n in list(thms | proof_only_defs):
    k = key(n)
    if k[1] in bundle_keys.get(k[0], set()):
        thms.discard(n)
        nodes.discard(n)
        inline.discard(n)
        if by_name[n]['kind'] == 'theorem':
            embedded.add(n)
bundle_mods = [m for m in mods_order if bundle_keys.get(m)]

# Definition files: contiguous runs of source modules in dependency order (a file
# publishes only after the files it imports, so fewer files mean fewer sequential
# rounds; each stays under the platform's ~500-line advisory). Given by the first
# module of each part; the boundaries were chosen to balance sizes.
PARTS = [('01_RealLoci', 'RotationSupport'), ('02_FamilyBasics', 'Blowup'),
         ('03_IsometriesAndCharts', 'DirectIsometries'), ('04_ProjectiveClosure', 'CoordinateExchange'),
         ('05_FamilyFunctionField', 'OrdinaryMultiplePoints'), ('06_QuadraticRing', 'QuadraticIntegralClosure'),
         ('07_Places', 'DedekindPlaces'), ('08_Differentials', 'QuadraticDifferentials'),
         ('09_Genus', 'PlaceUniformizers'), ('10_KummerField', 'FamilyGenus'),
         ('11_KummerLocal', 'KummerLocal'), ('12_FermatGenus', 'KummerPlaces')]
_starts = [bundle_mods.index(first) for _, first in PARTS] + [len(bundle_mods)]
assert _starts[0] == 0 and _starts == sorted(_starts), 'part boundaries out of order'
part_mods = {p: bundle_mods[_starts[i]:_starts[i + 1]] for i, (p, _) in enumerate(PARTS)}
part_of = {m: p for p, ms in part_mods.items() for m in ms}

def part_file(p):
    return f'Def_{BUNDLE_PREFIX}{p}'

def thm_slug(n):
    return 'Thm_' + by_name[n]['userName'].replace('.', '_')

# ---------------------------------------------------------------- command kinds
CONTEXT = {
    'Lean.Parser.Command.open', 'Lean.Parser.Command.variable', 'Lean.Parser.Command.include',
    'Lean.Parser.Command.omit', 'Lean.Parser.Command.set_option', 'Lean.Parser.Command.universe',
    'Lean.Parser.Command.attribute', 'Lean.Parser.Command.notation', 'Lean.Parser.Command.mixfix',
    'Lean.Parser.Command.macro', 'Lean.Parser.Command.macro_rules', 'Lean.Parser.Command.syntax',
    'Lean.Parser.Command.elab', 'Lean.Parser.Command.elab_rules', 'Lean.Parser.Command.notation3',
    'Mathlib.Notation3.notation3', 'Lean.Parser.Command.noncomputable',
}
DROP = {'Lean.Parser.Command.printAxioms', 'Lean.Parser.Command.print', 'Lean.Parser.Command.check',
        'Lean.Parser.Command.eval', 'Lean.Parser.Command.reduce', 'Lean.Parser.Command.synth',
        'Lean.Parser.Command.moduleDoc', 'Lean.Parser.Command.eoi', 'header',
        'Lean.Parser.Command.example', 'Lean.Parser.Command.exit', 'Lean.Parser.Command.check_failure'}
SCOPE_OPEN = {'Lean.Parser.Command.namespace', 'Lean.Parser.Command.section',
              'Lean.Parser.Command.noncomputableSection'}
SCOPE_END = {'Lean.Parser.Command.end'}

decl_starts = {mod: {d['declStart']['offset']: d for d in M[mod]['decls']} for mod in mods_order}
unknown_kinds = collections.Counter()

def cmd_text(mod, c):
    return seg(mod, c['start']['offset'], c['end']['offset'])

def local_instance_name(mod, d):
    """Full name if the declaration at d is a `local instance` (its attribute does not
    survive in a bundle, so consumers re-add it with `attribute [local instance]`)."""
    head = seg(mod, d['declStart']['offset'], d['valStart']['offset'] if d.get('valStart') else d['declEnd']['offset'])
    if re.search(r'\blocal instance\b', head) or re.search(r'@\[local instance', head):
        for r in rows:
            if r['module'] == mod and r['_decl'] is d:
                return r['userName']
    return None

def scopes_at(mod, offset):
    """Scope stack active just before `offset`: [{'kind','name','cmds'}] from outermost."""
    stack = [dict(kind='file', name=None, cmds=[])]
    for c in M[mod]['cmds']:
        if c['start']['offset'] >= offset:
            break
        k = c['syntaxKind']
        t = cmd_text(mod, c)
        if k in SCOPE_OPEN:
            if k == 'Lean.Parser.Command.namespace':
                stack.append(dict(kind='ns', name=t.split()[1], cmds=[], text=t))
            else:
                stack.append(dict(kind='sec', name=None, cmds=[], text=t))
        elif k in SCOPE_END:
            if len(stack) > 1:
                stack.pop()
        elif k in CONTEXT:
            stack[-1]['cmds'].append(t)
        elif c['start']['offset'] in decl_starts[mod]:
            li = local_instance_name(mod, decl_starts[mod][c['start']['offset']])
            if li:
                stack[-1]['cmds'].append(f'attribute [local instance] {li}')
        elif k not in DROP:
            unknown_kinds[k] += 1
    return stack

def flat_context(stack):
    """Context lines for a top-level declaration: namespaces become `open`."""
    out, path = [], []
    for s in stack:
        if s['kind'] == 'ns':
            path.append(s['name'])
            out.append('open ' + '.'.join(path))
        out.extend(s['cmds'])
    return out

def nested_open(stack):
    out = []
    for s in stack:
        if s['kind'] == 'ns':
            out.append(s['text'])
        elif s['kind'] == 'sec':
            out.append(s['text'])
        out.extend(s['cmds'])
    return out

def nested_close(stack):
    out = []
    for s in reversed(stack):
        if s['kind'] == 'ns':
            out.append('end ' + s['name'])
        elif s['kind'] == 'sec':
            parts = s['text'].split()
            out.append('end' + ((' ' + parts[-1]) if len(parts) > (2 if parts[0] == 'noncomputable' else 1) else ''))
    return out

WRAP = re.compile(r'^(omit|include|open|set_option|variable)\b(.*)\bin[ \t]*\n', re.M)
NOTATION = re.compile(r'(?:local |scoped )?notation "([^"]+)" => (.+)')

def split_decl(n):
    """(hoisted wrapper commands, head text, proof text) of a theorem, with the
    docstring removed from the head. Positions come from Stage 2."""
    r = by_name[n]
    mod, d = r['module'], r['_decl']
    start, val, end = d['declStart']['offset'], d['valStart']['offset'], d['declEnd']['offset']
    text = M[mod]['text']
    hoisted = []
    while True:
        m = WRAP.match(text[start:val].decode('utf-8'))
        if not m:
            break
        hoisted.append(m.group(0).rstrip()[:-len('in')].rstrip())
        start += len(m.group(0).encode('utf-8'))
    head_b = bytearray(text[start:val])
    ds = d.get('docstring')
    if ds and ds['start']['offset'] >= start:
        a, b = ds['start']['offset'] - start, ds['end']['offset'] - start
        del head_b[a:b]
        doc_cut = b - a
    else:
        doc_cut, a = 0, None
    head = head_b.decode('utf-8').lstrip('\n')
    # binding occurrence of the declared name, from Stage 2 ref facts
    bind = None
    for rf in M[mod]['refs']:
        if rf['const'] == n and start <= rf['start']['offset'] < val:
            bind = rf
            break
    return hoisted, head, text[val:end].decode('utf-8'), bind, start, doc_cut, a

def rename_head(n, head_info, new_name):
    hoisted, head, proof, bind, start, doc_cut, doc_at = head_info
    r = by_name[n]
    short = r['_decl']['nameText']
    text = head
    # the declId follows the keyword; rewrite the first occurrence after `theorem`/`lemma`
    m = re.search(r'\b(theorem|lemma)\s+' + re.escape(short) + r'(?![\w.\'])', text)
    if not m:
        raise SystemExit(f'cannot locate declId of {n}')
    text = text[:m.start()] + 'theorem ' + new_name + text[m.end():]
    return text

# ---------------------------------------------------------------- emit
if os.path.isdir(OUT):
    shutil.rmtree(OUT)
for sub in ('Definitions', 'Theorems', 'Solutions'):
    os.makedirs(os.path.join(OUT, sub))

def bundles_for(mods):
    acc = set()
    for m in mods:
        acc |= closure[m] | {m}
    return [part_file(p) for p, _ in PARTS if any(part_of.get(m) == p for m in acc)]

def nonproject_for(mods):
    acc = set()
    for m in mods:
        acc |= set(nonproject[m])
    return sorted(acc)

generated = dict(bundles=[], nodes=[], unknown_kinds={})

# Definition files: each source module of a part in its own section, so its opens,
# variables, notations and local attributes end with it, as at the end of its file.
for pname, _ in PARTS:
    parts_text, nonproj = [], set()
    for mod in part_mods[pname]:
        keep = bundle_keys[mod]
        body = []
        for c in M[mod]['cmds']:
            k = c['syntaxKind']
            o = c['start']['offset']
            if k in DROP:
                continue
            if o in decl_starts[mod]:
                if o in keep:
                    t = M[mod]['text'][c['start']['offset']:c['end']['offset']]
                    df = decl_starts[mod][o]
                    if df.get('nameText') is None:
                        # anonymous instance: declare it under its original automatic name,
                        # which bundles (all under `Definitions.`) would otherwise not keep unique
                        auto = [r['userName'] for r in rows if r['module'] == mod and r['_decl'] is df]
                        if len(auto) == 1:
                            short = auto[0][len(NS) + 1:] if auto[0].startswith(NS + '.') else auto[0]
                            head_end = (df['valStart'] or df['declEnd'])['offset'] - o
                            i = t[:head_end].find(b'instance')
                            if i >= 0:
                                j = i + len(b'instance')
                                t = t[:j] + b' ' + short.encode('utf-8') + t[j:]
                                generated.setdefault('named_instances', []).append(f'{mod}:{short}')
                    pt = decl_starts[mod][o].get('privateTok')
                    if pt:  # importable bundle: de-privatize (exact token range from Stage 2)
                        a, b = pt['start']['offset'] - o, pt['end']['offset'] - o
                        t = t[:a] + t[b:].lstrip(b' ')
                        generated.setdefault('deprivatized', []).append(f'{mod}:{decl_starts[mod][o].get("nameText")}')
                    body.append(t.decode('utf-8'))
                continue
            body.append(cmd_text(mod, c))
        close = nested_close(scopes_at(mod, len(M[mod]['text']) + 1))
        parts_text.append(f'-- lean/{mod}.lean\nsection\n\n' + '\n\n'.join(body)
                          + ('\n\n' + '\n'.join(close) if close else '') + '\n\nend')
        nonproj |= set(nonproject[mod])
    imports = [f'import Definitions.{b}' for b in bundles_for(part_mods[pname]) if b != part_file(pname)]
    imports += [f'import {i}' for i in sorted(nonproj)]
    src = (f'-- Definitions, part {pname[:2]} of {len(PARTS)}, generated from curve-symmetry-lean by skeleton\n'
           f'-- subtraction: the source modules below, in dependency order, each in its own\n'
           f'-- section; only definitions, instances and the theorems they need are kept.\n'
           + '\n'.join(imports) + '\n\n' + '\n\n'.join(parts_text) + '\n')
    open(os.path.join(OUT, 'Definitions', part_file(pname) + '.lean'), 'w', encoding='utf-8').write(src)
    generated['bundles'].append(part_file(pname))
    generated.setdefault('parts', {})[part_file(pname)] = part_mods[pname]

def inline_closure(n):
    seen, order = set(), []
    def visit(u):
        for d in by_name[u]['valueDeps'] + by_name[u]['typeDeps']:
            if d in inline and d not in seen:
                seen.add(d)
                visit(d)
                order.append(d)
    visit(n)
    order.sort(key=lambda u: (pos_in_order[by_name[u]['module']], by_name[u]['_decl']['declStart']['offset']))
    # one block per declaration command
    out, keys = [], set()
    for u in order:
        k = key(u)
        if k not in keys:
            keys.add(k)
            out.append(u)
    return out

def node_deps(n, helpers):
    acc = set()
    for u in [n] + helpers:
        for d in by_name[u]['valueDeps'] + by_name[u]['typeDeps']:
            if d in nodes and d != n:
                acc.add(d)
    return sorted(acc, key=lambda u: by_name[u]['userName'])

for n in sorted(nodes, key=lambda u: by_name[u]['userName']):
    r = by_name[n]
    mod, d = r['module'], r['_decl']
    info = split_decl(n)
    hoisted, head, proof = info[0], info[1], info[2]
    ctx = flat_context(scopes_at(mod, d['declStart']['offset']))
    full = r['userName']
    stmt_head = rename_head(n, info, full)
    # stub
    stub_imports = [f'import Definitions.{b}' for b in bundles_for([mod])] + [f'import {i}' for i in nonproject[mod]]
    # A preamble takes imports, variables and opens; local notations of the source are
    # spelled out in the stub instead (the type diff checks the statement is unchanged).
    stub_ctx, notations = [], []
    for line in ctx + hoisted:
        if re.match(r'(local |scoped )?notation\b', line):
            m = NOTATION.fullmatch(line)
            if not m:
                raise SystemExit(f'notation with arguments in the context of {n}: {line}')
            notations.append((m.group(1), m.group(2)))
        else:
            stub_ctx.append(line)
    def expand(s):
        for sym, rhs in sorted(notations, key=lambda x: -len(x[0])):
            s = re.sub(r'(?<![\w.\'])' + re.escape(sym) + r'(?![\w\'])', lambda _: '(' + rhs + ')', s)
        return s
    stub_ctx = [expand(l) for l in stub_ctx]
    preamble = '\n'.join(stub_imports) + '\n\n' + '\n'.join(stub_ctx) + ('\n' if stub_ctx else '')
    formal = expand(stmt_head.rstrip()) + ' := by sorry'
    stub = (f'-- Statement stub generated from lean/{mod}.lean (curve-symmetry-lean).\n'
            + preamble + '\n' + formal + '\n')
    open(os.path.join(OUT, 'Theorems', thm_slug(n) + '.lean'), 'w', encoding='utf-8').write(stub)
    # solution
    helpers = inline_closure(n)
    deps = node_deps(n, helpers)
    sol_mods = [mod] + [by_name[h]['module'] for h in helpers]
    sol_imports = ([f'import Definitions.{b}' for b in bundles_for(sol_mods)]
                   + [f'import Theorems.{thm_slug(u)}' for u in deps]
                   + [f'import {i}' for i in nonproject_for(sol_mods)])
    blocks = []
    for h in helpers:
        hm, hd = by_name[h]['module'], by_name[h]['_decl']
        st = scopes_at(hm, hd['declStart']['offset'])
        blocks.append('\n'.join(nested_open(st) + [seg(hm, hd['declStart']['offset'], hd['declEnd']['offset'])]
                                + nested_close(st)))
    sol_head = rename_head(n, info, 'solution')
    short = d['nameText']
    dotted = ['open ' + NS + '.' + short.rsplit('.', 1)[0]] if '.' in short else []
    node_block = '\n'.join(ctx + hoisted + dotted + [sol_head.rstrip() + ' ' + proof.lstrip()])
    sol = (f'-- Solution generated from lean/{mod}.lean (curve-symmetry-lean): inlined helpers in\n'
           f'-- their own scopes, then the node renamed to `solution` in its own context.\n'
           + '\n'.join(sol_imports) + '\n\n' + '\n\n'.join(blocks + ['section\n' + node_block + '\nend'])
           + '\n\n#print axioms solution\n')
    open(os.path.join(OUT, 'Solutions', 'Sol_' + thm_slug(n)[4:] + '.lean'), 'w', encoding='utf-8').write(sol)
    generated['nodes'].append(dict(name=full, module=mod, stub=thm_slug(n), helpers=len(helpers),
                                   deps=[by_name[u]['userName'] for u in deps],
                                   target=n in targets))

generated['unknown_kinds'] = dict(unknown_kinds)
generated['embedded_targets'] = sorted(by_name[n]['userName'] for n in embedded & targets)
generated["counts"] = dict(rfl_simp=len(rfl_simp), targets=len(targets), nodes=len(nodes), inline=len(inline),
                           embedded=len(embedded), bundles=len(PARTS), bundle_modules=len(bundle_mods), defmat=len(defmat),
                           instances=len(inst), proof_only_defs=len(proof_only_defs))
json.dump(generated, open(os.path.join(ROOT, 'p2m', 'generated.json'), 'w', encoding='utf-8'), indent=1, ensure_ascii=False)
print(json.dumps(generated['counts']))
print('targets provided by bundles (not nodes):', len(generated['embedded_targets']), generated['embedded_targets'][:8])
print('unclassified command kinds:', dict(unknown_kinds))
