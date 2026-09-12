"""Independent MI-22 statement-only re-elaboration; no proof implementation.
Adapts this reviewer's prior separate-prefix drivers. Exact pinned dependency
object caches are reused, and no Linux Comparator execution is claimed.
"""
from pathlib import Path
import datetime, hashlib, json, os, platform, re, subprocess, tempfile, time

OUT = Path(__file__).resolve().parent
PROJECT = OUT.parents[1]
REPO = PROJECT.parents[2]


def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def save(name, value): (OUT / name).write_text(json.dumps(value, indent=2) + '\n')
def capture(args, cwd=PROJECT): return subprocess.check_output(args, cwd=cwd).decode().strip()


freeze_path = PROJECT / 'reviews/statement-freeze.json'
assert sha(freeze_path) == 'd83d2a2baa1788f6e5ec284c70bb12d7618f4963a9426777a37b2af4135ed756'
assert sha(PROJECT / 'reviews/statement-handoff.md') == 'fc0be477ed453bec390a7002e13e2002f740e0b0d257550bcc9e8cc85385b1cb'
freeze = json.loads(freeze_path.read_text())
assert len(freeze['files']) == 27 and len(freeze['source_files']) == 8
for rel, h in freeze['files'].items(): assert sha(PROJECT / rel) == h, rel
save('inputs-before.json', freeze['files'])
sources = {}
for rel, h in freeze['source_files'].items():
    data = subprocess.check_output(['git', 'show', freeze['base_commit'] + ':' + rel], cwd=REPO)
    assert (REPO / rel).read_bytes() == data and sha(REPO / rel) == h, rel
    sources[rel] = {'sha256': h, 'bytes': len(data), 'matches_immutable_base': True}
save('original-sources.json', sources)
for rel in ['Solution.lean', 'NLA/MI22/Proof.lean']:
    assert not (PROJECT / rel).exists(), rel
assert not re.search(r'\b(?:sorry|admit|axiom)\b', (PROJECT / 'NLA/MI22/Definitions.lean').read_text())
pins = []
for pkg in json.loads((PROJECT / 'lake-manifest.json').read_text())['packages']:
    folder = PROJECT / '.lake/packages' / pkg['name']
    revision = capture(['git', 'rev-parse', 'HEAD'], folder)
    status = capture(['git', 'status', '--porcelain'], folder)
    assert revision == pkg['rev'] and not status, pkg['name']
    pins.append({'name': pkg['name'], 'revision': revision, 'status': status})
assert len(pins) == 10
save('dependencies.json', pins)
parent = Path('/tmp/nla-lean-formalization/independent-prefixes')
parent.mkdir(parents=True, exist_ok=True)
prefix = Path(tempfile.mkdtemp(prefix='mi22-statement-referee1-', dir=parent))
old = (PROJECT / '.lake/build/lib/lean').resolve()
paths = capture(['lake', 'env', 'printenv', 'LEAN_PATH']).split(os.pathsep)
env = dict(os.environ)
env['LEAN_PATH'] = os.pathsep.join([str(prefix)] + [q for q in paths if q and Path(q).resolve() != old])
checks = {'scope': 'Independent local macOS statement-only check; pinned dependency cache reuse, no completed mathematical proof or Linux claim.',
          'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
          'platform': platform.platform(), 'lean_version': capture(['lean', '--version']),
          'base_commit': freeze['base_commit'], 'fresh_prefix': str(prefix),
          'project_cache_excluded': str(old), 'LEAN_PATH': env['LEAN_PATH'], 'commands': []}
modules = ['NLA/MI22/Definitions', 'Challenge']
for mod in modules + ['reviews/statement-referee-1-evidence/Inspect']:
    src = PROJECT / (mod + '.lean')
    cmd = ['lean']; artifacts = []
    if mod in modules:
        for flag, suffix in [('-o', '.olean'), ('-i', '.ilean')]:
            dest = prefix / (mod + suffix)
            dest.parent.mkdir(parents=True, exist_ok=True)
            cmd += [flag, str(dest)]; artifacts.append(dest)
    cmd.append(str(src))
    name = 'inspection.log' if mod not in modules else mod.replace('/', '-') + '.log'
    print('Checking ' + mod, flush=True)
    start = time.monotonic()
    proc = subprocess.run(cmd, cwd=PROJECT, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (OUT / name).write_bytes(proc.stdout)
    checks['commands'].append({'source': str(src.relative_to(PROJECT)), 'source_sha256': sha(src),
                               'command': cmd, 'exit_code': proc.returncode, 'seconds': time.monotonic() - start,
                               'log': name, 'log_sha256': sha(OUT / name),
                               'artifacts': {str(a.relative_to(prefix)): sha(a) for a in artifacts if a.exists()}})
    save('fresh-checks.json', checks)
    print(f'Exit {proc.returncode}: {name}', flush=True)
    if proc.returncode: print(proc.stdout.decode()); raise SystemExit(proc.returncode)
for rel, h in freeze['files'].items(): assert sha(PROJECT / rel) == h, rel
save('inputs-after.json', {'all_27_project_files_unchanged': True,
                           'all_eight_original_sources_unchanged': True,
                           'files': {rel: sha(PROJECT / rel) for rel in freeze['files']}})
assert not (PROJECT / 'Solution.lean').exists() and not (PROJECT / 'NLA/MI22/Proof.lean').exists()
assert len(re.findall(r'declaration uses `sorry`', (OUT / 'Challenge.log').read_text())) == 8
for name in ['NLA-MI22-Definitions.log', 'inspection.log']:
    assert not re.search(r'\b(?:error|warning):', (OUT / name).read_text()), name
text = (OUT / 'inspection.log').read_text()
printed = re.findall(r"'([^'\n]+)' depends on axioms: \[([^\]]*)\]", text)
no_axioms = re.findall(r"'([^'\n]+)' does not depend on any axioms", text)
axioms = {n: [s.strip() for s in a.split(',') if s.strip()] for n, a in printed}
axioms.update({n: [] for n in no_axioms})
assert len(axioms) == 23, (len(axioms), no_axioms)
for n, a in axioms.items(): assert set(a) <= {'propext', 'Classical.choice', 'Quot.sound'}, n
save('definition-axiom-audit.json', {'count': len(axioms), 'definitions': axioms, 'verdict': 'PASS',
                                   'scope': 'Definitions only; no Challenge theorem is represented as proved.'})
checks['finished_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
checks['verdict'] = 'PASS'; save('fresh-checks.json', checks)
print('PASS: independent source/actual-definition elaboration, 23 allowed-axiom audits, eight intentional Challenge placeholders, unchanged 27+8 freeze.', flush=True)
