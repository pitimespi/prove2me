#!/usr/bin/env python3
"""Mission pipeline: stubs / split / stage / propose / attach / submit.
usage: pipeline.py <cmd> <Namespace> [args]
  stubs   NS SOLFILE...          generate Theorems/Thm_<NS>_<name>.lean stubs from public theorems, build them
  split   NS SOLFILE...          per-theorem Solutions/Sol_<NS>_<name>.lean with theorem solution + Thm imports
  stage   NS AUDITDIR            copy Def + stubs + auditor doc into AUDITDIR
  propose NS ITEMS DESC NAME GOAL OUT   create proposal (Textbook, public), items, order, goal, milestones
  attach  NS PROPJSON AUDITDIR   PATCH read-backs
  submit  NS PROPJSON OUTFILE    submit all solutions (in dependency order) and poll
"""
import json, os, re, sys, subprocess, pathlib, time, urllib.request, urllib.error
WS = pathlib.Path(os.path.expanduser('~/prove2me_workspace'))
SCR = pathlib.Path(__file__).resolve().parent
BASE = "https://prove2.me/api/v1"
ENV = dict(os.environ, PATH=os.path.expanduser('~/lean-dl/lean-4.33.1-linux/bin') + ':' + os.environ['PATH'])

def call(m, p, b, t, raw=False):
    data = None if b is None else json.dumps(b).encode()
    r = urllib.request.Request(BASE + p, method=m, data=data,
        headers={"Authorization": f"Bearer {t}", "Content-Type": "application/json"})
    try:
        with urllib.request.urlopen(r) as x:
            body = x.read()
            return x.status, (json.loads(body or b'null') if not raw else body)
    except urllib.error.HTTPError as e:
        return e.code, e.read().decode()[:500]

def token():
    key = os.environ["PROVE2ME_API_KEY"]
    st, r = call("POST", "/agent/refresh", {"api_key": key}, key)
    assert st == 200, r
    return r["access_token"]

def lake(*mods):
    return subprocess.run(['lake', 'build', *mods], cwd=WS, env=ENV, capture_output=True, text=True)

def blocks(path):
    lines = pathlib.Path(path).read_text().split('\n'); i = 0
    while i < len(lines) and (lines[i].startswith('import') or lines[i].startswith('open') or lines[i].strip() == ''):
        i += 1
    body = lines[i:]
    starts = [j for j, l in enumerate(body) if re.match(r'^(theorem|private theorem|/--|/-!|def|private def|set_option|instance|private instance|abbrev)', l)] + [len(body)]
    bl = ['\n'.join(body[a:b]).rstrip() + '\n' for a, b in zip(starts, starts[1:])]
    merged = []; pend = ''
    for x in bl:
        if x.startswith('/--') and not re.search(r'^(theorem|private theorem|def|private def|instance|abbrev)', x, re.M):
            pend += x; continue
        merged.append(pend + x); pend = ''
    return merged

def classify(b, ns):
    m = re.search(r'^theorem (' + re.escape(ns) + r'\.\w+)', b, re.M)
    if m: return ('pub', m.group(1))
    if re.search(r'^(private theorem|private def|set_option|private instance)', b, re.M): return ('priv', None)
    if re.search(r'^(def|instance|abbrev)', b, re.M): return ('def', None)
    return ('other', None)

def public_stmts(ns, solfiles):
    stmts = {}
    for f in solfiles:
        txt = pathlib.Path(f).read_text()
        for m in re.finditer(r'^theorem (' + re.escape(ns) + r'\.\w+)(.*?):=(?: by)?\n', txt, re.S | re.M):
            stmts[m.group(1)] = m.group(2)
    return stmts

def cmd_stubs(ns, solfiles):
    stmts = public_stmts(ns, solfiles)
    pre = f'import Definitions.Def_{ns}'
    out = {}
    for name, body in stmts.items():
        fs = ('theorem ' + name + body).rstrip() + ' := by sorry'
        out[name] = {'formal_statement': fs, 'preamble': pre}
        (WS / 'Theorems' / f"Thm_{name.replace('.', '_')}.lean").write_text(pre + '\n\n' + fs + '\n')
    json.dump(out, open(SCR / f'{ns}_stmts.json', 'w'), indent=1)
    mods = [f"Theorems.Thm_{n.replace('.', '_')}" for n in out]
    r = lake(*mods)
    errs = [l for l in r.stdout.split('\n') if l.startswith('error')]
    print(f"{len(out)} stubs; build errors: {len(errs)}"); print('\n'.join(errs[:10]))
    return out

def cmd_split(ns, solfiles):
    pre = f'import Definitions.Def_{ns}'
    written = []
    for f in solfiles:
        bl = blocks(f)
        names = [classify(b, ns)[1] for b in bl if classify(b, ns)[0] == 'pub']
        for idx, b in enumerate(bl):
            kind, name = classify(b, ns)
            if kind != 'pub': continue
            privs = [x for x in bl[:idx] if classify(x, ns)[0] in ('priv', 'def')]
            content = ''.join(privs) + b
            deps = sorted({n for n in names if n != name and (re.search(re.escape(n) + r'\b', content) or re.search(r'(?<![\w.])' + re.escape(n.split('.')[-1]) + r'\b', content))})
            imports = [pre] + [f"import Theorems.Thm_{d.replace('.', '_')}" for d in deps]
            sol = re.sub(r'^theorem ' + re.escape(ns) + r'\.\w+', 'theorem solution', b, count=1, flags=re.M)
            text = '\n'.join(imports) + f'\n\nopen {ns}\n\n' + ''.join(p + '\n' for p in privs) + sol
            fn = WS / 'Solutions' / f"Sol_{name.replace('.', '_')}.lean"
            fn.write_text(text); written.append((name, deps))
    for name, deps in written:
        mod = f"Solutions.Sol_{name.replace('.', '_')}"
        r = lake(mod)
        errs = [l for l in r.stdout.split('\n') if l.startswith('error')]
        ax = subprocess.run(['lake', 'env', 'lean', '--stdin'], cwd=WS, env=ENV, capture_output=True, text=True,
                            input=f"import {mod}\n#print axioms solution\n").stdout.strip().split('\n')[-1]
        print(f"{name:45s} deps={len(deps)} errors={len(errs)} {ax[ax.find('['):]}")
        for e in errs[:3]: print('   ', e[:200])

def cmd_stage(ns, auditdir):
    d = SCR / auditdir; d.mkdir(exist_ok=True)
    for old in d.glob('readback_*.md'): old.unlink()
    import shutil
    shutil.copy(WS / 'Definitions' / f'Def_{ns}.lean', d)
    for f in (WS / 'Theorems').glob(f'Thm_{ns}_*.lean'): shutil.copy(f, d)
    shutil.copy(SCR / 'refs' / 'mission_auditor.md', d)
    print('staged', len(list(d.iterdir())), 'files in', d)

def cmd_propose(ns, items_mod, descfile, name, goal, outjson):
    sys.path.insert(0, str(SCR))
    M = __import__(items_mod)
    S = json.load(open(SCR / f'{ns}_stmts.json'))
    assert set(S) == set(M.ORDER), set(S) ^ set(M.ORDER)
    tok = token()
    old = json.load(open(SCR / 'proposal.json'))
    defcode = (WS / 'Definitions' / f'Def_{ns}.lean').read_text()
    st, r = call("POST", "/mission-proposals", {"name": name, "mission_type": "Textbook",
        "description": open(SCR / descfile).read(), "field_ids": [f['id'] for f in old['fields']],
        "env": old['env'], "visibility": "public"}, tok)
    print("create", st, r if st != 201 else r['id']); assert st == 201; pid = r['id']
    ids = {}
    st, r = call("POST", f"/mission-proposals/{pid}/items", {"kind": "definition",
        "definition_name": M.DEFINITION["definition_name"], "definition_title": M.DEFINITION["definition_title"],
        "definition": defcode, "natural_language_statement": M.DEFINITION["natural_language_statement"],
        "source": M.SRC, "tags": M.TAGS}, tok)
    print("def", st, r if st not in (200, 201) else ""); ids[ns] = r['id']
    for n in M.ORDER:
        t = M.THEOREMS[n]
        st, r = call("POST", f"/mission-proposals/{pid}/items", {"kind": "theorem", "theorem_name": n,
            "theorem_title": t["title"], "formal_statement": S[n]["formal_statement"], "preamble": S[n]["preamble"],
            "natural_language_statement": t["nl"], "source": M.SRC, "tags": M.TAGS}, tok)
        print("thm", n, st, r if st not in (200, 201) else ""); ids[n] = r['id']
    st, r = call("PATCH", f"/mission-proposals/{pid}", {"item_order": [ids[ns]] + [ids[n] for n in M.ORDER],
        "main_item_id": ids[goal]}, tok)
    print("order/main", st, r if st != 200 else "")
    for n in M.ORDER:
        ms = M.THEOREMS[n]["ms"]
        if ms:
            st, r = call("POST", f"/mission-proposals/{pid}/milestones", {"item_id": ids[n],
                "milestone_title": ms[0], "milestone_description": ms[1]}, tok)
            if st not in (200, 201): print("ms", n, st, r)
    json.dump({"proposal_id": pid, "items": ids}, open(SCR / outjson, 'w'), indent=1)
    st, p = call("GET", f"/mission-proposals/{pid}", None, tok)
    print("STATUS", p['status'], "items", len(p['items']), "main", p['main_item_id'] == ids[goal])

def cmd_attach(ns, propjson, auditdir):
    tok = token()
    MODEL = "claude-fable-5-1 (independent sub-agent, blind: Lean code + auditor instructions only)"
    P = json.load(open(SCR / propjson)); pid = P["proposal_id"]
    for name, iid in P["items"].items():
        f = SCR / auditdir / (f"readback_Def_{ns}.md" if name == ns else f"readback_{name.replace('.', '_')}.md")
        rb = f.read_text()
        st, r = call("PATCH", f"/mission-proposals/{pid}/items/{iid}", {"readback": rb, "readback_model": MODEL}, tok)
        print(f"{name:45s} {st} rb={len(rb)}")
    st, p = call("GET", f"/mission-proposals/{pid}", None, tok)
    print("STATUS", p['status'], "all readbacks", all(i['readback'] for i in p['items']))

def cmd_submit(ns, propjson, outfile):
    tok = token()
    P = json.load(open(SCR / propjson)); pid = P["proposal_id"]
    st, p = call("GET", f"/mission-proposals/{pid}", None, tok)
    targets = {i['theorem_name']: i['theorem_id'] for i in p['items'] if i['theorem_name'] != ns and i.get('theorem_id')}
    # dependency order from the split solution imports
    deps = {}
    for n in targets:
        txt = (WS / 'Solutions' / f"Sol_{n.replace('.', '_')}.lean").read_text()
        deps[n] = [f"{ns}." + m for m in re.findall(r'^import Theorems\.Thm_' + re.escape(ns) + r'_(\w+)', txt, re.M)]
    done = {}; results = {}
    rounds = 0
    while len(done) < len(targets) and rounds < 10:
        rounds += 1
        batch = [n for n in targets if n not in done and all(d in done and done[d] for d in deps[n])]
        if not batch: break
        subs = {}
        for n in batch:
            slug = n.replace('.', '_')
            f = WS / 'Solutions' / f"Sol_{slug}.lean"; e = SCR / 'expl' / f"expl_{slug}.md"
            r = subprocess.run(['curl', '-sS', '-X', 'POST', f'{BASE}/verify', '-H', f'Authorization: Bearer {tok}',
                                '-F', f'theorem_id={targets[n]}', '-F', f'file=@{f}', '-F', f'explanation=<{e}'],
                               capture_output=True, text=True).stdout
            try: subs[n] = json.loads(r)['submission_id']
            except Exception: print("FAIL", n, r[:300]); done[n] = False
        for _ in range(120):
            for n, sid in subs.items():
                if n in done: continue
                st, d = call("GET", f"/verify?submission_id={sid}", None, tok)
                if d['status'] != 'PENDING':
                    done[n] = d['status'] in ('ACCEPTED', 'SKETCH_ACCEPTED'); results[n] = d
                    print(f"{d['status']:16s} {n}  {(d.get('error_message') or '')[:300]}")
            if all(n in done for n in subs): break
            time.sleep(6)
    json.dump({n: results.get(n, {}).get('status', 'NOT SUBMITTED') for n in targets}, open(SCR / outfile, 'w'), indent=1)
    print("accepted", sum(1 for v in done.values() if v), "of", len(targets))

if __name__ == '__main__':
    cmd, ns, *args = sys.argv[1:]
    {'stubs': lambda: cmd_stubs(ns, args), 'split': lambda: cmd_split(ns, args),
     'stage': lambda: cmd_stage(ns, args[0]), 'propose': lambda: cmd_propose(ns, *args),
     'attach': lambda: cmd_attach(ns, args[0], args[1]), 'submit': lambda: cmd_submit(ns, args[0], args[1])}[cmd]()
