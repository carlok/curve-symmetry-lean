#!/usr/bin/env python3
"""Package 4 inputs. For every node and definition file: the exact Lean text, the
original docstrings, the definitions a statement uses, and the note's statements it
proves or supports (from COVERAGE.md). Writes p2m/meta/batch_NN.json for the
statement writers, plus p2m/meta/fixed.json with the fields computed here: `source`
(note statement and page, PDF and Lean file at a fixed commit, no line anchors) and
`tags`."""
import collections, json, os, re

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
REPO_DIR = os.path.join(ROOT, '..', 'curve_symmetry')
SHA = 'd99bc17a1c397956c05d7417de50f9beed56580f'
BLOB = f'https://github.com/carlok/curve-symmetry-lean/blob/{SHA}'
TREE = f'https://github.com/carlok/curve-symmetry-lean/tree/{SHA}'
PDF = f'{BLOB}/sharp_symmetry_bounds.pdf'
NOTE = 'C. Perassi, Sharp symmetry bounds for real algebraic curves (note)'
PROJECT_TAG = 'curve-symmetry-lean'
NS = 'CurveSymmetry'
BATCH = 24

# Where each COVERAGE row sits in the note: (detailed place, page, statement).
ROW_REF = {
    **{f'T1.{i}': ('Theorem 1', 'p. 1', 'Theorem 1') for i in range(1, 5)},
    **{f'T2.{i}': ('Theorem 2', 'p. 2', 'Theorem 2') for i in range(1, 8)},
    'T2.5': ('Theorem 2 and equation (3)', 'p. 2', 'Theorem 2'),
    'S01': ('proof of Lemma 3', 'p. 2', 'Lemma 3'),
    'S02': ('proof of Lemma 3', 'p. 2', 'Lemma 3'),
    'S03': ('proof of Lemma 3', 'p. 2', 'Lemma 3'),
    'S04': ('Lemma 3', 'p. 2', 'Lemma 3'),
    'S05': ('Section 2, equation (4)', 'p. 2', 'Theorem 1'),
    'S06': ('proof of Theorem 1', 'p. 3', 'Theorem 1'),
    'S07': ('proof of Theorem 1, equation (5)', 'p. 3', 'Theorem 1'),
    'S08': ('proof of Theorem 1, equality case', 'p. 3', 'Theorem 1'),
    'S09': ('proof of Theorem 1, sharpness examples', 'p. 3', 'Theorem 1'),
    'S10': ('equation (2)', 'p. 1', 'Theorem 1'),
    'G01': ('Section 3, closure of equation (6)', 'p. 3', 'Lemma 4'),
    'G02': ('proof of Lemma 4', 'p. 3', 'Lemma 4'),
    'G03': ('proof of Lemma 4', 'p. 3', 'Lemma 4'),
    'G04': ('proof of Lemma 4', 'p. 3', 'Lemma 4'),
    'G05': ('Lemma 4', 'p. 3', 'Lemma 4'),
    'G06': ('Lemma 4', 'p. 3', 'Lemma 4'),
    'G07': ('proof of Lemma 4, equation (7)', 'p. 3', 'Lemma 4'),
    'G08': ('proof of Lemma 4', 'p. 4', 'Lemma 4'),
    'G09': ('Lemma 4', 'pp. 3-4', 'Lemma 4'),
    'G10': ('proof of Lemma 4', 'p. 4', 'Lemma 4'),
    'G11': ('proof of Theorem 2', 'p. 4', 'Theorem 2'),
    'G12': ('proof of Theorem 2, equation (8)', 'p. 4', 'Theorem 2'),
    'G13': ('proof of Theorem 2', 'p. 4', 'Theorem 2'),
    'R01': ('Remark 5', 'p. 4', 'Remark 5'),
    'R02': ('Remark 5', 'p. 4', 'Remark 5'),
    'R03': ('Remark 5', 'p. 4', 'Remark 5'),
    'R04': ('Remark 5', 'p. 4', 'Remark 5'),
    'R05': ('Remark 5', 'p. 4', 'Remark 5'),
}
# Modules that COVERAGE describes in prose rather than in a row (the closure of G01),
# and two family lemmas placed by their statements.
EXTRA_MOD_ROWS = {m: 'G01' for m in ('MixedCornerClosure', 'OtherMixedCornerClosure', 'ReciprocalCornerClosure',
                                     'AffineChartImages', 'AffineClosure', 'ProjectiveChartMaps',
                                     'ProjectiveAtlasOpenCover')}
# Rows whose status column names its endpoint after the first sentence, and an
# endpoint the Remark 5 row cites although it is the genus clause of Lemma 4.
EXTRA_ENDS = {'G09': ('family_genus', 'paper_family_genus'), 'G01': ('family_degreeOf',),
              'S07': ('paper_high_order_radial_form',),
              'G13': ('family_isometry_iff_rotation',)}
DROP_ENDS = {'R01': ('paper_family_genus',)}
EXTRA_NODE_ROWS = {'CurveSymmetry.family_no_opposite': 'T2.6',
                   'CurveSymmetry.family_anti_mobius_projective_critical_transport': 'G11'}
STMT_PAGE = {'Theorem 1': 'p. 1', 'Theorem 2': 'p. 2', 'Lemma 3': 'p. 2', 'Lemma 4': 'p. 3', 'Remark 5': 'p. 4'}
STMT_ORDER = ['Theorem 1', 'Theorem 2', 'Lemma 3', 'Lemma 4', 'Remark 5']
PART_TAGS = {
    '01_RealLoci': ['real-algebraic-geometry', 'euclidean-geometry'],
    '02_FamilyBasics': ['real-algebraic-geometry', 'polynomials'],
    '03_IsometriesAndCharts': ['euclidean-geometry', 'algebraic-geometry'],
    '04_ProjectiveClosure': ['algebraic-geometry', 'zariski-topology'],
    '05_FamilyFunctionField': ['algebraic-geometry', 'function-fields'],
    '06_QuadraticRing': ['commutative-algebra', 'dedekind-domains'],
    '07_Places': ['function-fields', 'valuation-theory'],
    '08_Differentials': ['kahler-differentials', 'function-fields'],
    '09_Genus': ['function-fields', 'genus'],
    '10_KummerField': ['function-fields', 'kummer-theory'],
    '11_KummerLocal': ['commutative-algebra', 'kummer-theory'],
    '12_FermatGenus': ['function-fields', 'genus'],
}

rows = [json.loads(l) for l in open(os.path.join(ROOT, 'decl_graph.jsonl'), encoding='utf-8') if l.strip()]
by_name = {r['name']: r for r in rows}
g = json.load(open(os.path.join(ROOT, 'p2m', 'generated.json'), encoding='utf-8'))
nodes = {n['name']: n for n in g['nodes']}
parts = {k[len('Def_CurveSymmetry_'):]: v for k, v in g['parts'].items()}

# module order (the root file's imports) and the part of every module
order = [l.split()[1] for l in open(os.path.join(ROOT, 'lean', 'CurveSymmetry.lean'), encoding='utf-8')
         if l.startswith('import ')]
part_of, cur = {}, None
for m in order:
    for p, ms in parts.items():
        if m in ms:
            cur = p
    part_of[m] = cur or '01_RealLoci'

# Stage 2 declaration facts, joined to Stage 1 rows by containment of the start line
facts = collections.defaultdict(list)
for mod in order:
    path = os.path.join(ROOT, 'p2m', 'sketch', mod + '.jsonl')
    if os.path.exists(path):
        for l in open(path, encoding='utf-8'):
            if l.startswith('{'):
                d = json.loads(l)
                if d.get('kind') == 'decl':
                    facts[mod].append(d)
TEXT = {mod: open(os.path.join(ROOT, 'lean', mod + '.lean'), 'rb').read() for mod in order}

def decl_of(r):
    for d in facts.get(r['module'], []):
        if d['declStart']['line'] <= r['startLine'] <= d['declEnd']['line']:
            return d
    return None

def docstring(r):
    d = decl_of(r)
    if not d or not d.get('docstring'):
        return None
    t = TEXT[r['module']][d['docstring']['start']['offset']:d['docstring']['end']['offset']].decode('utf-8')
    return re.sub(r'^/--\s*|\s*-/$', '', t.strip())

def decl_text(r, max_lines=30):
    d = decl_of(r)
    if not d:
        return None
    end = d['declEnd']['offset']
    t = TEXT[r['module']][d['declStart']['offset']:end].decode('utf-8')
    if d.get('docstring'):
        t = t.replace(TEXT[r['module']][d['docstring']['start']['offset']:d['docstring']['end']['offset']].decode('utf-8'), '').lstrip()
    lines = t.split('\n')
    return '\n'.join(lines[:max_lines]) + ('\n  …' if len(lines) > max_lines else '')

# COVERAGE rows: cited names and linked modules
cov = open(os.path.join(REPO_DIR, 'COVERAGE.md'), encoding='utf-8').read()
cov_rows = []
for line in cov.split('\n'):
    m = re.match(r'^\| ([TSGR]\d+(?:\.\d+)?) \| (.*?) \|', line)
    if m and m.group(1) in ROW_REF:
        names = {f'{NS}.{x}' for x in re.findall(r'`([A-Za-z_][A-Za-z0-9_\'.]*)`', line)} & set(by_name)
        mods = set(re.findall(r'\(lean/([A-Za-z]+)\.lean\)', line))
        # the checked endpoints: names in the first sentence of the status column
        cols = line.split(' | ')
        status = cols[2] if len(cols) > 2 else ''
        first = re.split(r'\.\s|;', status, maxsplit=1)[0]
        ends = {f'{NS}.{x}' for x in re.findall(r'`([A-Za-z_][A-Za-z0-9_\'.]*)`', first)} & names
        ends = (ends | {f'{NS}.{x}' for x in EXTRA_ENDS.get(m.group(1), ())}) - {f'{NS}.{x}' for x in DROP_ENDS.get(m.group(1), ())}
        cov_rows.append(dict(id=m.group(1), claim=m.group(2), names=names, ends=ends, mods=mods))

def closure(roots):
    seen, work = set(), list(roots)
    while work:
        u = work.pop()
        if u in seen or u not in by_name:
            continue
        seen.add(u)
        work.extend(by_name[u]['valueDeps'] + by_name[u]['typeDeps'])
    return seen

for row in cov_rows:
    mod_decls = {r['name'] for r in rows if r['module'] in row['mods'] and r['kind'] == 'theorem'
                 and not r['isPrivate'] and r['startLine']}
    row['reach'] = closure(row['names'] | mod_decls)

users = collections.defaultdict(set)
for r in rows:
    for d in set(r['valueDeps']):
        if d in nodes and r['name'] in nodes and d != r['name']:
            users[d].add(r['name'])

def place(n, mod):
    direct = [row for row in cov_rows if n in row['ends']]
    linked = [row for row in cov_rows if row not in direct and (
        n in row['names'] or mod in row['mods'] or row['id'] == EXTRA_MOD_ROWS.get(mod)
        or row['id'] == EXTRA_NODE_ROWS.get(n))]
    support = [row for row in cov_rows if n in row['reach'] and row not in direct and row not in linked]
    return direct, linked, support

def stmts_of(rws):
    s = {ROW_REF[row['id']][2] for row in rws}
    return [x for x in STMT_ORDER if x in s]

def source_for(n, mod):
    direct, linked, support = place(n, mod)
    lean = f'Lean: {BLOB}/lean/{mod}.lean (C. Perassi)'
    def places(rws):
        seen, out = set(), []
        for row in rws:
            p = '{}, {}'.format(*ROW_REF[row['id']][:2])
            if p not in seen:
                seen.add(p)
                out.append(p)
        return '; '.join(out[:3])
    if direct:
        return f'{NOTE}, {places(direct)}, {PDF}. {lean}', direct, linked, support
    if linked:
        return f'{NOTE}: lemma of the formalization, for {places(linked)}, {PDF}. {lean}', direct, linked, support
    if support:
        st = stmts_of(support)
        what = ', '.join(f'{s} ({STMT_PAGE[s]})' for s in st[:3])
        return f'{NOTE}: lemma of the formalization, used for {what}, {PDF}. {lean}', direct, linked, support
    return f'{NOTE}: lemma of the formalization, {PDF}. {lean}', direct, linked, support

# statement stubs as generated (the exact upload text)
def stub_parts(stub):
    t = open(os.path.join(ROOT, 'p2m', 'platform', 'Theorems', stub + '.lean'), encoding='utf-8').read()
    m = re.search(r'^theorem\s', t, re.M)
    pre = [l for l in t[:m.start()].split('\n') if l and not l.startswith('import ') and not l.startswith('--')]
    return '\n'.join(pre), t[m.start():].rstrip()

out_dir = os.path.join(ROOT, 'p2m', 'meta')
os.makedirs(out_dir, exist_ok=True)
fixed, entries = {}, []
for n in sorted(nodes, key=lambda u: (order.index(nodes[u]['module']), by_name[u]['startLine'])):
    mod = nodes[n]['module']
    r = by_name[n]
    src, direct, linked, support = source_for(n, mod)
    pre, stmt = stub_parts(nodes[n]['stub'])
    defs = sorted(d for d in r['typeDeps'] if d in by_name and by_name[d]['kind'] != 'theorem'
                  and by_name[d]['startLine'] and d.startswith(NS + '.'))
    tags = [PROJECT_TAG] + PART_TAGS[part_of[mod]]
    fixed[n] = dict(source=src, tags=tags)
    entries.append(dict(
        theorem_name=n, module=mod, lean_file=f'lean/{mod}.lean',
        preamble_context=pre, formal_statement=stmt, original_docstring=docstring(r),
        definitions_used=defs,
        note_statements=[dict(place=ROW_REF[row['id']][0], page=ROW_REF[row['id']][1],
                              ledger_claim=row['claim']) for row in direct + linked],
        supports=stmts_of(support), used_by_nodes=sorted(users[n])[:8],
        is_mission_target=nodes[n]['target']))

# definitions referenced by the batch's statements, with docstrings and text
def def_entry(d):
    r = by_name[d]
    return dict(name=d, module=r['module'], docstring=docstring(r), lean=decl_text(r))

batches = [entries[i:i + BATCH] for i in range(0, len(entries), BATCH)]
for i, b in enumerate(batches if '--fixed-only' not in os.sys.argv else [], 1):
    need = sorted({d for e in b for d in e['definitions_used']})
    json.dump(dict(nodes=b, definitions=[def_entry(d) for d in need]),
              open(os.path.join(out_dir, f'batch_{i:02d}.json'), 'w', encoding='utf-8'), indent=1, ensure_ascii=False)

# definition files
def_files = []
for p, ms in parts.items():
    decls = [r for r in rows if r['module'] in ms and r['kind'] != 'theorem' and r['startLine']
             and not r['isPrivate'] and decl_of(r)]
    fixed['Def_CurveSymmetry_' + p] = dict(
        source=f'{NOTE}, definitions of the formalization, {PDF}. Lean modules '
               + ', '.join(ms) + f' in {TREE}/lean (C. Perassi)',
        tags=[PROJECT_TAG] + PART_TAGS[p])
    def_files.append(dict(definition_name='CurveSymmetry_' + p, modules=ms,
                          declarations=[dict(name=r['name'], docstring=docstring(r), lean=decl_text(r, 12))
                                        for r in decls]))
if '--fixed-only' not in os.sys.argv:
    json.dump(dict(definition_files=def_files), open(os.path.join(out_dir, 'batch_defs.json'), 'w', encoding='utf-8'),
              indent=1, ensure_ascii=False)
json.dump(fixed, open(os.path.join(out_dir, 'fixed.json'), 'w', encoding='utf-8'), indent=1, ensure_ascii=False)

kinds = collections.Counter('direct' if place(n, nodes[n]['module'])[0] else
                            'module-linked' if place(n, nodes[n]['module'])[1] else
                            'supports' if place(n, nodes[n]['module'])[2] else 'none' for n in nodes)
print(f'nodes {len(entries)} in {len(batches)} batches; definition files {len(def_files)}; source kinds {dict(kinds)}')
