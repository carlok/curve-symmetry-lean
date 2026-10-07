#!/usr/bin/env python3
"""Package 5 uploader (private). One phase per run, each started only on Carlo's go:

    python3 p2m/upload.py dry           build and check every request body, no API call
    python3 p2m/upload.py definitions   12 definition files, in order, each after the previous publishes
    python3 p2m/upload.py statements    208 statement stubs (submit-problem, batches of 25)
    python3 p2m/upload.py solutions     208 solutions (VERIFY), leaves first, at most 90 pending
    python3 p2m/upload.py explanations  PATCH the 208 proof explanations and corrected sources
    python3 p2m/upload.py proposal      create the private mission proposal (goal, definitions, milestones)
    python3 p2m/upload.py status        summary of the state file

Calls go through the workspace wrapper `p2m.sh` (it holds the key; this script never
reads credentials). Every raw response is saved under p2m/api/log/ and parsed from
that file. p2m/upload_state.json records each action before and after its call, so
an interrupted run resumes without duplicates: an item with a job or submission id is
polled, never resubmitted. Everything is created with "private": true."""
import json, os, subprocess, sys, time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
WS = os.path.normpath(os.path.join(ROOT, '..', 'prove2me', 'envs', 'prove2me_workspace'))
META = os.path.join(ROOT, 'p2m', 'meta')
PLAT = os.path.join(ROOT, 'p2m', 'platform')
LOG = os.path.join(ROOT, 'p2m', 'api', 'log')
BODIES = os.path.join(ROOT, 'p2m', 'api', 'bodies')
STATE = os.path.join(ROOT, 'p2m', 'upload_state.json')
POLL = 60          # seconds between poll rounds
MAX_PENDING = 90   # the platform allows 100 pending verifications

g = json.load(open(os.path.join(ROOT, 'p2m', 'generated.json'), encoding='utf-8'))
order_parts = [b[len('Def_'):] for b in g['bundles']]
node_deps = {n['name']: n['deps'] for n in g['nodes']}
stub_of = {n['name']: n['stub'] for n in g['nodes']}

def load_state():
    if os.path.exists(STATE):
        return json.load(open(STATE, encoding='utf-8'))
    return dict(definitions={}, statements={}, solutions={})

def save_state(st):
    tmp = STATE + '.tmp'
    json.dump(st, open(tmp, 'w', encoding='utf-8'), indent=1, ensure_ascii=False)
    os.replace(tmp, STATE)

def call(tag, *args):
    """Run p2m.sh from inside the workspace; save the raw response; parse the file."""
    os.makedirs(LOG, exist_ok=True)
    path = os.path.join(LOG, f'{time.strftime("%Y%m%d-%H%M%S")}_{tag}.json')
    with open(path, 'w', encoding='utf-8') as fp:
        subprocess.run(['./p2m.sh', *args], cwd=WS, stdout=fp, stderr=subprocess.STDOUT, check=False)
    text = open(path, encoding='utf-8').read().strip()
    try:
        return json.loads(text)
    except json.JSONDecodeError:
        return {'_raw': text[:2000]}

def write_body(name, obj):
    os.makedirs(BODIES, exist_ok=True)
    path = os.path.join(BODIES, name + '.json')
    json.dump(obj, open(path, 'w', encoding='utf-8'), ensure_ascii=False)
    return path

def def_body(d):
    return dict(definition_name=d['definition_name'], definition_title=d['definition_title'],
                definition=d['definition'], natural_language_statement=d['natural_language_statement'],
                source=d['source'], tags=d['tags'], private=True)

def thm_problem(x):
    return {k: x[k] for k in ('theorem_name', 'theorem_title', 'formal_statement', 'natural_language_statement',
                              'preamble', 'source', 'tags')}

def poll_job(job_id, tag):
    while True:
        r = call(f'job_{tag}', 'GET', f'/publish-jobs/{job_id}')
        s = r.get('status')
        if s in ('PUBLISHED', 'FAILED', 'ERROR'):
            return r
        time.sleep(POLL)

def phase_dry():
    defs = json.load(open(os.path.join(META, 'final_defs.json'), encoding='utf-8'))
    nodes = json.load(open(os.path.join(META, 'final_nodes.json'), encoding='utf-8'))
    assert [d['definition_name'] for d in defs] == order_parts, 'definition files out of order'
    assert sorted(x['theorem_name'] for x in nodes) == sorted(node_deps), 'statements incomplete'
    sizes = [len(json.dumps(def_body(d), ensure_ascii=False).encode()) for d in defs]
    batch = [thm_problem(x) for x in nodes[:25]]
    bsize = len(json.dumps(dict(problems=batch, private=True), ensure_ascii=False).encode())
    for x in nodes:
        assert x['formal_statement'].startswith('theorem ' + x['theorem_name'] + ' ') or \
            x['formal_statement'].startswith('theorem ' + x['theorem_name'] + '\n'), x['theorem_name']
        assert x['formal_statement'].endswith(':= by sorry'), x['theorem_name']
        assert 'import ' not in x['formal_statement'], x['theorem_name']
    for n in node_deps:
        assert os.path.exists(os.path.join(PLAT, 'Solutions', 'Sol_' + stub_of[n][4:] + '.lean')), n
    print(f'dry run: {len(defs)} definition bodies (largest {max(sizes)} bytes), {len(nodes)} statements '
          f'(a batch of 25 is {bsize} bytes), {len(node_deps)} solutions; nothing sent')

def phase_definitions(st):
    defs = {d['definition_name']: d for d in json.load(open(os.path.join(META, 'final_defs.json'), encoding='utf-8'))}
    unsure = [n for n, rec in st['definitions'].items() if 'sent_at' in rec and not rec.get('job_id')
              and rec.get('status') not in ('REJECTED',)]
    if unsure:
        sys.exit(f'interrupted while sending, look the names up before resending: {unsure}')
    for name in order_parts:
        rec = st['definitions'].get(name, {})
        if rec.get('status') == 'PUBLISHED':
            continue
        if not rec.get('job_id') or rec.get('status') == 'ERROR':
            rec = dict(sent_at=time.time())
            st['definitions'][name] = rec
            save_state(st)
            r = call(f'def_{name}', 'POST', '/submit-definition', '@' + write_body('def_' + name, def_body(defs[name])))
            if not r.get('job_id'):
                rec.update(status='REJECTED', response=r)
                save_state(st)
                sys.exit(f'{name}: rejected before queueing: {r}')
            rec['job_id'] = r['job_id']
            save_state(st)
        r = poll_job(rec['job_id'], name)
        rec.update(status=r.get('status'), theorem_id=r.get('theorem_id') or r.get('definition_id'),
                   error=r.get('error_message'))
        save_state(st)
        print(name, rec['status'], flush=True)
        if rec['status'] != 'PUBLISHED':
            sys.exit(f'{name}: {rec["status"]} {rec.get("error")}')

def phase_statements(st):
    """Keeps at most QUEUE_LIMIT of this account's publish jobs waiting (the platform
    refuses a batch beyond 100 and creates nothing for it), sending the next batch of up
    to 25 as room frees up."""
    if not all(st['definitions'].get(p, {}).get('status') == 'PUBLISHED' for p in order_parts):
        sys.exit('definition files not all published')
    nodes = json.load(open(os.path.join(META, 'final_nodes.json'), encoding='utf-8'))
    unsure = [n for n, rec in st['statements'].items() if 'sent_at' in rec and not rec.get('job_id')
              and rec.get('status') != 'REJECTED']
    if unsure:
        sys.exit(f'interrupted while sending, look the names up before resending: {unsure}')
    QUEUE_LIMIT = 95
    while True:
        pending = [n for n, rec in st['statements'].items() if rec.get('job_id') and
                   rec.get('status') not in ('PUBLISHED', 'FAILED', 'ERROR')]
        todo = [x for x in nodes if not st['statements'].get(x['theorem_name'], {}).get('job_id')
                and st['statements'].get(x['theorem_name'], {}).get('status') != 'REJECTED'
                or st['statements'].get(x['theorem_name'], {}).get('status') == 'ERROR']
        if not pending and not todo:
            break
        room = QUEUE_LIMIT - len(pending)
        while todo and room > 0:
            chunk, todo = todo[:min(25, room)], todo[min(25, room):]
            for x in chunk:
                st['statements'][x['theorem_name']] = dict(sent_at=time.time())
            save_state(st)
            tag = 'stmts_' + time.strftime('%H%M%S')
            r = call(tag, 'POST', '/submit-problem',
                     '@' + write_body(tag, dict(problems=[thm_problem(x) for x in chunk], private=True)))
            if not r.get('jobs'):
                # refused before queueing (e.g. the queue limit): nothing was created
                for x in chunk:
                    st['statements'].pop(x['theorem_name'], None)
                save_state(st)
                print(time.strftime('%H:%M'), f'batch refused, will retry: {str(r)[:200]}', flush=True)
                break
            for j in r['jobs']:
                st['statements'].setdefault(j['name'], {})['job_id'] = j['job_id']
            for e in r.get('errors', []):
                st['statements'].setdefault(e.get('name', '?'), {}).update(status='REJECTED', response=e)
            save_state(st)
            room -= len(r['jobs'])
        pending = [n for n, rec in st['statements'].items() if rec.get('job_id') and
                   rec.get('status') not in ('PUBLISHED', 'FAILED', 'ERROR')]
        for n in pending:
            r = call('job_' + n.split('.')[-1], 'GET', f'/publish-jobs/{st["statements"][n]["job_id"]}')
            if r.get('status') in ('PUBLISHED', 'FAILED', 'ERROR'):
                st['statements'][n].update(status=r['status'], theorem_id=r.get('theorem_id'),
                                           error=r.get('error_message'))
                save_state(st)
        done = sum(1 for rec in st['statements'].values() if rec.get('status') == 'PUBLISHED')
        bad = sum(1 for rec in st['statements'].values() if rec.get('status') in ('FAILED', 'REJECTED'))
        print(time.strftime('%H:%M'), f'published {done}, failed or rejected {bad}, pending {len(pending)}, '
              f'not sent yet {len(todo)}', flush=True)
        time.sleep(max(POLL, len(pending)))
    bad = {n: rec.get('status') for n, rec in st['statements'].items() if rec.get('status') != 'PUBLISHED'}
    print(f'statements published: {len(st["statements"]) - len(bad)}; not published: {bad}')

def phase_solutions(st):
    """Leaves first: a proof is sent once every node it imports is accepted. At most
    MAX_PENDING verifications wait at once (the platform's cap is 100 per account,
    shared with any other run on the account). Independent branches go on when one
    proof fails; the run ends when nothing else can move, listing the failures."""
    ids = {n: rec.get('theorem_id') for n, rec in st['statements'].items() if rec.get('status') == 'PUBLISHED'}
    if set(ids) != set(node_deps):
        sys.exit('statements not all published')
    unsure = [n for n, rec in st['solutions'].items() if rec.get('status') == 'SENDING']
    if unsure:
        sys.exit(f'interrupted while sending, check GET /submissions before resending: {unsure}')
    OK = ('ACCEPTED', 'SKETCH_ACCEPTED')
    done = lambda n: st['solutions'].get(n, {}).get('status') in OK
    while True:
        pending = [n for n, rec in st['solutions'].items() if rec.get('status') == 'PENDING']
        for n in pending:
            r = call('sub_' + n.split('.')[-1], 'GET', f'/verify?submission_id={st["solutions"][n]["submission_id"]}')
            s_ = r.get('status')
            if s_ and s_ != 'PENDING':
                rec = st['solutions'][n]
                if s_ == 'ERROR' and rec.get('retries', 0) < 2:
                    st['solutions'][n] = dict(retries=rec.get('retries', 0) + 1)   # transient: resend unchanged
                else:
                    rec.update(status=s_, verdict=str(r)[:1500])
                save_state(st)
        pending = [n for n, rec in st['solutions'].items() if rec.get('status') == 'PENDING']
        ready = [n for n in node_deps if not st['solutions'].get(n, {}).get('status')
                 and all(done(d) for d in node_deps[n])]
        for n in ready[:max(0, MAX_PENDING - len(pending))]:
            retries = st['solutions'].get(n, {}).get('retries', 0)
            st['solutions'][n] = dict(sent_at=time.time(), status='SENDING', retries=retries)
            save_state(st)
            sol = os.path.join(PLAT, 'Solutions', 'Sol_' + stub_of[n][4:] + '.lean')
            r = call('verify_' + n.split('.')[-1], 'VERIFY', ids[n], sol)
            if not r.get('submission_id'):
                st['solutions'][n] = dict(retries=retries)       # refused before queueing: not sent
                save_state(st)
                print(time.strftime('%H:%M'), f'verify refused, will retry: {str(r)[:200]}', flush=True)
                break
            st['solutions'][n].update(submission_id=r['submission_id'], status='PENDING')
            save_state(st)
            pending.append(n)
        failed = {n: rec['status'] for n, rec in st['solutions'].items()
                  if rec.get('status') and rec['status'] not in OK + ('PENDING', 'SENDING')}
        acc = sum(1 for n in node_deps if done(n))
        print(time.strftime('%H:%M'), f'accepted {acc}/{len(node_deps)}, pending {len(pending)}, failed {len(failed)}',
              flush=True)
        if acc == len(node_deps):
            print('all solutions accepted')
            return
        if not pending and not ready:
            sys.exit(f'stopped: nothing else can move; failed: {failed}')
        time.sleep(max(POLL, len(pending)))

def phase_explanations(st):
    """PATCH the explanation of every accepted proof, and the corrected sources."""
    expl = json.load(open(os.path.join(META, 'final_explanations.json'), encoding='utf-8'))
    patches = json.load(open(os.path.join(META, 'source_patches.json'), encoding='utf-8'))
    st.setdefault('explanations', {})
    st.setdefault('source_patches', {})
    for n, text in expl.items():
        if st['explanations'].get(n) == 'OK':
            continue
        sid = st['solutions'][n]['submission_id']
        r = call('expl_' + n.split('.')[-1], 'PATCH', f'/submissions/{sid}',
                 '@' + write_body('expl_' + n.split('.')[-1], {'explanation': text}))
        ok = isinstance(r, dict) and not r.get('error') and '_raw' not in r
        st['explanations'][n] = 'OK' if ok else ('FAILED: ' + str(r)[:300])
        save_state(st)
    for n, src in patches.items():
        if st['source_patches'].get(n) == 'OK':
            continue
        tid = st['statements'][n]['theorem_id']
        r = call('src_' + n.split('.')[-1], 'PATCH', f'/theorems/{tid}',
                 '@' + write_body('src_' + n.split('.')[-1], {'source': src}))
        ok = isinstance(r, dict) and not r.get('error') and '_raw' not in r
        st['source_patches'][n] = 'OK' if ok else ('FAILED: ' + str(r)[:300])
        save_state(st)
    bad = {k: v for k, v in list(st['explanations'].items()) + list(st['source_patches'].items()) if v != 'OK'}
    print(f"explanations patched: {sum(v == 'OK' for v in st['explanations'].values())}; "
          f"sources patched: {sum(v == 'OK' for v in st['source_patches'].values())}; failures: {bad}")

def phase_proposal(st):
    """Create the private mission proposal from p2m/mission/: reference items for the
    definition files, the goal and the milestones; goal and order; milestone texts."""
    plan = json.load(open(os.path.join(ROOT, 'p2m', 'mission', 'proposal.json'), encoding='utf-8'))
    desc = open(os.path.join(ROOT, 'p2m', 'mission', 'description.md'), encoding='utf-8').read()
    ms = st.setdefault('mission', {'items': {}, 'milestones': {}})
    if not ms.get('proposal_id'):
        r = call('proposal_create', 'POST', '/mission-proposals', '@' + write_body('proposal_create', dict(
            name=plan['name'], description=desc, mission_type=plan['mission_type'],
            field_ids=[f['id'] for f in plan['fields']], visibility=plan['visibility'])))
        if not r.get('id'):
            sys.exit(f'proposal not created: {r}')
        ms['proposal_id'] = r['id']
        save_state(st)
    pid = ms['proposal_id']
    tid = lambda n: (st['statements'].get(n) or {}).get('theorem_id') or st['definitions'][n]['theorem_id']
    order = plan['definitions'] + [plan['goal']] + [m['theorem_name'] for m in plan['milestones']]
    for n in order:
        if n in ms['items']:
            continue
        r = call('item_' + n.split('.')[-1], 'POST', f'/mission-proposals/{pid}/items',
                 '@' + write_body('item_' + n.split('.')[-1], dict(kind='reference', theorem_id=tid(n))))
        iid = r.get('id') or r.get('item_id')
        if not iid:
            sys.exit(f'{n}: reference item not added: {r}')
        ms['items'][n] = iid
        save_state(st)
    r = call('proposal_order', 'PATCH', f'/mission-proposals/{pid}', '@' + write_body('proposal_order', dict(
        main_item_id=ms['items'][plan['goal']], item_order=[ms['items'][n] for n in order])))
    if r.get('error'):
        sys.exit(f'order not set: {r}')
    for m in plan['milestones']:
        n = m['theorem_name']
        if ms['milestones'].get(n) == 'OK':
            continue
        r = call('ms_' + n.split('.')[-1], 'POST', f'/mission-proposals/{pid}/milestones',
                 '@' + write_body('ms_' + n.split('.')[-1], dict(item_id=ms['items'][n],
                     milestone_title=m['milestone_title'], milestone_description=m['milestone_description'])))
        ms['milestones'][n] = 'OK' if not r.get('error') and '_raw' not in r else 'FAILED: ' + str(r)[:300]
        save_state(st)
    back = call('proposal_readback', 'GET', f'/mission-proposals/{pid}')
    print(f"proposal {pid}: items {len(ms['items'])}, milestones OK "
          f"{sum(v == 'OK' for v in ms['milestones'].values())}/{len(plan['milestones'])}, "
          f"status {back.get('status')}, visibility {back.get('visibility')}")

if __name__ == '__main__':
    phase = sys.argv[1] if len(sys.argv) > 1 else 'status'
    st = load_state()
    if phase == 'dry':
        phase_dry()
    elif phase == 'definitions':
        phase_definitions(st)
    elif phase == 'statements':
        phase_statements(st)
    elif phase == 'solutions':
        phase_solutions(st)
    elif phase == 'explanations':
        phase_explanations(st)
    elif phase == 'proposal':
        phase_proposal(st)
    else:
        for k in ('definitions', 'statements', 'solutions'):
            c = {}
            for rec in st[k].values():
                c[rec.get('status')] = c.get(rec.get('status'), 0) + 1
            print(k, c)
