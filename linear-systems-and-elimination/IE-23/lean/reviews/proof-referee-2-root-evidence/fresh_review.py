"""Independent root final review; adapted generic campaign orchestration.

Fresh IE23 objects only. Pinned MI22 dependency artifacts are reused read-only.
This is direct macOS Lean elaboration, not Lake, dependency rebuilding or Linux.
"""
from pathlib import Path
import datetime, hashlib, json, os, platform, re, subprocess, tempfile, time

PROJECT = Path(__file__).resolve().parents[2]
REPO = PROJECT.parents[2]
OUT = Path(__file__).resolve().parent
BIN = Path('/Users/georgestepaniants/.elan/toolchains/leanprover--lean4---v4.33.1/bin')
PACKAGES = Path('/tmp/nla-lean-mi22-worktree/matrix-inequalities-and-norms/MI-22/lean/.lake/packages').resolve()
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()

def integrity():
    freezes = {}
    for rel, count in [('reviews/proof-freeze.json', 104), ('reviews/statement-freeze.json', 32)]:
        d = json.loads((PROJECT / rel).read_text())
        assert len(d['files']) == count
        for name, item in d['files'].items():
            f = PROJECT / name
            assert f.is_file() and not f.is_symlink()
            digest = item if isinstance(item, str) else item['sha256']
            assert sha(f) == digest, name
            if isinstance(item, dict):
                assert f.stat().st_size == item['bytes'], name
        base = d.get('source_commit', d.get('base'))
        assert len(d['source_files']) == 8
        for name, digest in d['source_files'].items():
            blob = subprocess.check_output(['git', 'show', base + ':' + name], cwd=REPO)
            assert hashlib.sha256(blob).hexdigest() == digest == sha(REPO / name), name
        freezes[rel] = {'sha256': sha(PROJECT / rel), 'project_inputs': count, 'source_blobs': 8}
    s = json.loads((PROJECT / 'reviews/statement-config-supplement.json').read_text())
    for name, item in s['added_files'].items():
        assert sha(PROJECT / name) == item['sha256']
    freezes['config_supplement'] = sha(PROJECT / 'reviews/statement-config-supplement.json')
    return freezes

def pins():
    result = []
    for item in json.loads((PROJECT / 'lake-manifest.json').read_text())['packages']:
        d = PACKAGES / item['name']
        rev = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=d, text=True).strip()
        dirty = subprocess.check_output(['git', 'status', '--porcelain'], cwd=d, text=True)
        assert rev == item['rev'] and not dirty, (item['name'], rev, dirty)
        result.append({'name': item['name'], 'path': str(d), 'revision': rev, 'clean': True})
    assert len(result) == 10
    return result

before, before_pins = integrity(), pins()
(PROJECT / '.verification').mkdir(exist_ok=True)
prefix = Path(tempfile.mkdtemp(prefix='ie23-root-final-ref2-', dir=PROJECT / '.verification'))
paths = [str(prefix)] + [str(PACKAGES / p['name'] / '.lake/build/lib/lean') for p in reversed(before_pins)]
paths.append(str(BIN.parent / 'lib/lean'))
env = dict(os.environ, LEAN_PATH=os.pathsep.join(paths))
record = {'status': 'RUNNING', 'reviewer': '/root', 'independent_of_implementation_author': True,
          'date_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
          'platform': platform.platform(), 'local_Lake_invocation': False, 'Linux_Comparator_run': False,
          'lean_version': subprocess.check_output([str(BIN / 'lean'), '--version'], text=True).strip(),
          'fresh_prefix': str(prefix), 'LEAN_PATH': env['LEAN_PATH'], 'old_project_objects_excluded': True,
          'dependency_artifacts_reused_read_only': True, 'pins_before': before_pins,
          'integrity_before': before, 'commands': []}
sources = ['NLA/IE23/' + name + '.lean' for name in
           ['Definitions', 'Norms', 'Matrices', 'FourthPower', 'Actions', 'Minimizers', 'Proof']]
sources += ['Solution.lean', 'reviews/proof-referee-2-root-evidence/Inspect.lean', 'Challenge.lean']
for relative in sources:
    argv = [str(BIN / 'lean')]
    if relative.startswith('NLA/') or relative == 'Solution.lean':
        target = prefix / Path(relative).with_suffix('.olean')
        target.parent.mkdir(parents=True, exist_ok=True)
        argv += ['-o', str(target), '-i', str(target.with_suffix('.ilean'))]
    argv.append(relative)
    print('Checking', relative, flush=True)
    start = time.monotonic()
    cp = subprocess.run(argv, cwd=PROJECT, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log = OUT / (relative.replace('/', '-').removesuffix('.lean') + '.log')
    log.write_bytes(cp.stdout)
    record['commands'].append({'source': relative, 'source_sha256': sha(PROJECT / relative),
        'command': argv, 'exit_code': cp.returncode, 'seconds': time.monotonic() - start,
        'log': log.name, 'log_sha256': sha(log)})
    (OUT / 'fresh-checks.json').write_text(json.dumps(record, indent=2) + '\n')
    assert cp.returncode == 0, cp.stdout.decode()
    holes = 8 if relative == 'Challenge.lean' else 0
    assert cp.stdout.count(b'warning:') == cp.stdout.count(b'declaration uses `sorry`') == holes, cp.stdout.decode()
    assert b'error:' not in cp.stdout
    print('PASS', flush=True)

record['integrity_after'], record['pins_after'] = integrity(), pins()
assert record['integrity_after'] == before and record['pins_after'] == before_pins
record['status'] = 'PASS'
record['fresh_commands'] = len(sources)
record['intentional_Challenge_placeholders'] = 8
(OUT / 'fresh-checks.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'fresh_commands': len(sources), 'frozen_proof_inputs': 104,
                  'original_statement_inputs': 32, 'original_source_blobs': 8, 'clean_pins': 10}), flush=True)
