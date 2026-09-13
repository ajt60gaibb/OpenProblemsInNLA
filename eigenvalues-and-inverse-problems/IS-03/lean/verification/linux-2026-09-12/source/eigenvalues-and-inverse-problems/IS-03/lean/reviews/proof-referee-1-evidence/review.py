"""IS-03 independent final referee 1 fresh-source and compiled trust audit.
Adapts this reviewer's IV-06 driver; no author object or prior project object
is used. Exact pinned MI-22 dependency objects are read-only.
"""
from pathlib import Path
import datetime
import hashlib
import json
import os
import platform
import re
import subprocess
import tempfile
import time

OUT = Path(__file__).resolve().parent
P = OUT.parents[1]
REPO = P.parents[2]
D = Path('/tmp/nla-lean-mi22-worktree/matrix-inequalities-and-norms/MI-22/lean/.lake/packages')
B = Path('/Users/georgestepaniants/.elan/toolchains/leanprover--lean4---v4.33.1/bin')
C = json.loads((OUT / 'context.json').read_text())
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
save = lambda n, d: (OUT / n).write_text(json.dumps(d, indent=2) + '\n')
git = lambda path, *a: subprocess.check_output(['git', '-C', str(path), *a])
assert sha(P / 'verification/proof-freeze.json') == C['freeze_sha256']
assert sha(P / 'reviews/proof-completion.md') == C['completion_sha256']
F = json.loads((P / 'verification/proof-freeze.json').read_text())

def integrity():
    for r, h in F['files'].items():
        assert sha(P / r) == h, r
    sources = {}
    for r, h in F['source_files'].items():
        raw = git(REPO, 'show', F['base'] + ':' + r)
        assert hashlib.sha256(raw).hexdigest() == h and (REPO / r).read_bytes() == raw, r
        sources[r] = {'sha256': h, 'git_blob': git(REPO, 'rev-parse', F['base'] + ':' + r).decode().strip()}
    assert sha(P / 'reviews/statement-freeze.json') == C['statement_freeze_sha256']
    s = json.loads((P / 'reviews/statement-freeze.json').read_text())
    for r, h in s['files'].items():
        if isinstance(h, dict): h = h['sha256']
        assert sha(P / r) == h, r
    assert len(s['files']) == C['statement_input_count'] == 34
    assert len(F['files']) == C['project_input_count'] == 203
    assert len(sources) == C['original_source_count'] == 10
    for r, h in C['statement_reports'].items():
        assert sha(P / r) == h
    return {'result': 'PASS', 'proof_freeze_sha256': C['freeze_sha256'],
        'proof_completion_sha256': C['completion_sha256'], 'files': F['files'],
        'original_sources': sources, 'statement_inputs': 34,
        'statement_approvals': C['statement_reports']}

before = integrity()
save('integrity-before.json', before)

def signatures(text):
    return {n: ' '.join(s.split()) for n, s in re.findall(r'^theorem\s+(\w+)\s+(.*?)\s*:=\s*by', text, re.S | re.M)}
ch = signatures((P / 'Challenge.lean').read_text())
sol = signatures((P / 'Solution.lean').read_text())
cfg = json.loads((P / 'comparator.json').read_text())
assert len(ch) == len(sol) == 7 and ch == sol
assert cfg['theorem_names'] == ['NLA.IS03.' + n for n in sol]
assert cfg['definition_names'] == []
assert cfg['permitted_axioms'] == ['propext', 'Classical.choice', 'Quot.sound']
save('source-signatures.json', {'result': 'PASS', 'headers': sol,
    'comparator': cfg, 'scope': 'Fresh elaboration plus normalized source headers; not an actual Linux Comparator run.'})

modules = ['NLA/IS03/Definitions.lean', 'NLA/IS03/Algebra.lean',
    'NLA/IS03/Spectral.lean', 'NLA/IS03/Witness.lean', 'NLA/IS03/Newton.lean',
    'NLA/IS03/Numerical.lean', 'NLA/IS03/Proof.lean', 'Solution.lean']
scan = {}
for r in modules:
    raw = (P / r).read_text()
    code = re.sub(r'/\-.*?\-/', '', raw, flags=re.S)
    code = re.sub(r'--[^\n]*', '', code)
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|partial)\b', code), r
    assert not re.search(r'^import\s+Challenge\b', code, re.M), r
    assert 'debug.skipKernelTC' not in code and 'trustCompiler' not in code
    scan[r] = {'sha256': sha(P / r), 'safe_source_scan': True}
save('source-safety.json', scan)

def check_pins():
    pins = []
    for d in json.loads((P / 'lake-manifest.json').read_text())['packages']:
        path = D / d['name']
        revision = git(path, 'rev-parse', 'HEAD').decode().strip()
        dirty = git(path, 'status', '--porcelain').decode()
        assert revision == d['rev'] and not dirty, d['name']
        pins.append({'name': d['name'], 'path': str(path), 'revision': revision, 'clean': True})
    assert len(pins) == 10
    return pins

pins = check_pins()
save('dependency-pins.json', pins)
prefix_root = Path('/tmp/nla-lean-formalization/independent-prefixes')
prefix_root.mkdir(exist_ok=True)
prefix = Path(tempfile.mkdtemp(prefix='is03-final-referee1-', dir=prefix_root))
assert not any(prefix.iterdir())
paths = [str(prefix)] + [str(D / d['name'] / '.lake/build/lib/lean') for d in reversed(pins)] + [str(B.parent / 'lib/lean')]
env = dict(os.environ, LEAN_PATH=os.pathsep.join(paths))
record = {'result': 'RUNNING', 'reviewer_role': C['role'],
    'date_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'platform': platform.platform(),
    'lean_version': subprocess.check_output([str(B / 'lean'), '--version'], text=True).strip(),
    'fresh_prefix': str(prefix), 'LEAN_PATH': env['LEAN_PATH'],
    'old_project_objects_excluded': True, 'dependency_objects_read_only': True,
    'dependency_copy_or_rebuild': False, 'local_Lake_invocation': False,
    'Linux_Comparator_run': False, 'commands': []}
for r in modules + ['Challenge.lean', 'reviews/proof-referee-1-evidence/Inspect.lean']:
    cmd = [str(B / 'lean')]
    objects = []
    if not r.endswith('/Inspect.lean'):
        for flag, suffix in [('-o', '.olean'), ('-i', '.ilean')]:
            path = prefix / Path(r).with_suffix(suffix)
            path.parent.mkdir(parents=True, exist_ok=True)
            cmd.extend([flag, str(path)])
            objects.append(path)
    cmd.append(r)
    print('Fresh independent check:', r, flush=True)
    start = time.monotonic()
    cp = subprocess.run(cmd, cwd=P, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log = OUT / (r.removesuffix('.lean').replace('/', '-') + '.log')
    log.write_bytes(cp.stdout)
    record['commands'].append({'source': r, 'source_sha256': sha(P / r),
        'command': cmd, 'exit_code': cp.returncode, 'seconds': time.monotonic() - start,
        'log': log.name, 'log_sha256': sha(log),
        'fresh_objects': {str(x.relative_to(prefix)): sha(x) for x in objects if x.exists()}})
    save('fresh-checks.json', record)
    print('Exit:', cp.returncode, flush=True)
    assert cp.returncode == 0, cp.stdout.decode()
    holes = 7 if r == 'Challenge.lean' else 0
    assert cp.stdout.count(b'warning:') == holes, cp.stdout.decode()
    assert cp.stdout.count(b'declaration uses `sorry`') == holes, cp.stdout.decode()
    assert b'error:' not in cp.stdout

axioms = []
for r in modules:
    log = OUT / (r.removesuffix('.lean').replace('/', '-') + '.log')
    for name, ax in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log.read_text()):
        found = [a.strip() for a in ax.split(',') if a.strip()]
        assert found == cfg['permitted_axioms'], (name, found)
        axioms.append({'declaration': name, 'axioms': found, 'log': log.name})
assert len(axioms) == 18
save('candidate-axioms.json', {'count': 18, 'standard_three_only': True, 'reports': axioms})
inspection = (OUT / 'reviews-proof-referee-1-evidence-Inspect.log').read_text()
required = re.findall(r'^REFEREE_RETAINED: (\S+)', inspection, re.M)
count = int(re.search(r'^REFEREE_PROJECT_DECLARATIONS: (\d+)', inspection, re.M).group(1))
assert len(required) == 33 and count >= 55
save('actual-dependencies.json', {'project_declarations': count,
    'required_dependencies': required, 'actual_type_and_value_traversal': True,
    'every_project_declaration_safe_total_and_standard_three_only': True})
after = integrity()
save('integrity-after.json', after)
assert before == after and check_pins() == pins
record.update(result='PASS', completed_fresh_commands=10)
save('fresh-checks.json', record)
print(json.dumps({'result': 'PASS', 'commands': 10, 'candidate_standard_three_checks': 18,
    'project_declarations': count, 'retained_dependencies': len(required), 'clean_pins': 10}))
