"""Author's reproducible FR-12 fresh-prefix elaboration and immutable-input audit.
Adapted from the campaign's earlier fresh-prefix verification drivers.
This is not an independent review, Linux sandbox or Comparator run.
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
PROJECT = OUT.parent
REPO = PROJECT.parents[2]
BIN = Path('/Users/georgestepaniants/.elan/toolchains/leanprover--lean4---v4.33.1/bin')


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def save(name, value):
    (OUT / name).write_text(json.dumps(value, indent=2) + '\n')


def capture(argv, cwd=PROJECT):
    return subprocess.run(argv, cwd=cwd, capture_output=True, text=True, check=True).stdout.strip()


freeze = PROJECT / 'reviews/statement-freeze.json'
assert sha(freeze) == '5fbbcbce16da324a186dd765d120c883e4800efe2e491fbf069c9f7c74f5372c'
frozen = json.loads(freeze.read_text())
inputs = {}
for field, base in [('files', PROJECT), ('source_files', REPO)]:
    for name, digest in frozen[field].items():
        path = base / name
        assert sha(path) == digest, name
        inputs[str(path)] = {'statement_sha256': digest, 'current_sha256': sha(path)}
for name in ['NLA/FR12/Semantics.lean', 'NLA/FR12/Doubling.lean', 'NLA/FR12/Growth.lean', 'NLA/FR12/Proof.lean', 'Solution.lean',
             'reviews/statement-referee-1.md', 'reviews/statement-referee-2.md',
             'verification/proof-start.json']:
    inputs[str(PROJECT / name)] = {'current_sha256': sha(PROJECT / name)}
save('inputs-before.json', inputs)

pins = []
for package in json.loads((PROJECT / 'lake-manifest.json').read_text())['packages']:
    folder = PROJECT / '.lake/packages' / package['name']
    actual = capture(['git', 'rev-parse', 'HEAD'], folder)
    dirty = capture(['git', 'status', '--porcelain'], folder)
    assert actual == package['rev'] and not dirty, package['name']
    pins.append({'name': package['name'], 'expected': package['rev'],
                 'actual': actual, 'git_status_porcelain': dirty})
assert len(pins) == 10
save('dependency-pins.json', pins)

# Compare complete source signatures, independently of proof bodies. Actual
# declaration comparison in Linux remains a required later gate.
def signatures(text):
    return {name: ' '.join(statement.split())
            for name, statement in re.findall(
                r'theorem\s+(\w+)\s+(.*?)\s*:=\s*by', text, flags=re.S)}

challenge = signatures((PROJECT / 'Challenge.lean').read_text())
solution = signatures((PROJECT / 'Solution.lean').read_text())
registered = json.loads((PROJECT / 'comparator.json').read_text())['theorem_names']
assert set(challenge) == set(solution) == {name.removeprefix('NLA.FR12.') for name in registered}
# Binder spelling is alpha-equivalent; the frozen Challenge itself is unchanged.
solution['counting_semantics'] = solution['counting_semantics'].replace('_hn', 'hn')
assert challenge == solution and len(solution) == 7
save('source-signatures.json', {'status': 'PASS', 'count': 7,
     'scope': 'Exact normalized source signatures, not Linux Comparator',
     'signatures': solution})
for name in ['NLA/FR12/Semantics.lean', 'NLA/FR12/Doubling.lean', 'NLA/FR12/Growth.lean', 'NLA/FR12/Proof.lean', 'Solution.lean']:
    text = (PROJECT / name).read_text()
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b', text), name
    assert not re.search(r'^import\s+Challenge\b', text, flags=re.M)

(PROJECT / '.verification').mkdir(exist_ok=True)
prefix = Path(tempfile.mkdtemp(prefix='fr12-author-fresh-', dir=PROJECT / '.verification'))
original_path = capture([str(BIN / 'lake'), 'env', 'printenv', 'LEAN_PATH'])
old_target = (PROJECT / '.lake/build/lib/lean').resolve()
parts = [p for p in original_path.split(os.pathsep) if Path(p).resolve() != old_target]
assert len(parts) + 1 == len(original_path.split(os.pathsep))
env = dict(os.environ)
env['LEAN_PATH'] = os.pathsep.join([str(prefix)] + parts)
checks = {'author_verification': True, 'independent_review': False,
          'date_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
          'platform': platform.platform(),
          'lean_version': capture([str(BIN / 'lean'), '--version']),
          'fresh_prefix': str(prefix), 'LEAN_PATH': env['LEAN_PATH'],
          'old_project_build_excluded': str(old_target),
          'scope': 'Fresh macOS proof compilation; pinned dependency artifacts reused; Linux pending',
          'commands': []}
jobs = [('NLA/FR12/Definitions.lean', 'fresh-definitions', 0, True),
        ('NLA/FR12/Semantics.lean', 'fresh-semantics', 0, True),
        ('NLA/FR12/Doubling.lean', 'fresh-doubling', 0, True),
        ('NLA/FR12/Growth.lean', 'fresh-growth', 0, True),
        ('NLA/FR12/Proof.lean', 'fresh-proof', 0, True),
        ('Solution.lean', 'fresh-solution', 0, True),
        ('Challenge.lean', 'fresh-challenge', 7, True),
        ('verification/InspectProof.lean', 'fresh-inspection', 0, False)]
for source, label, holes, produce in jobs:
    argv = [str(BIN / 'lean')]
    artifacts = []
    if produce:
        for ext, flag in [('.olean', '-o'), ('.ilean', '-i')]:
            target = prefix / Path(source).with_suffix(ext)
            target.parent.mkdir(parents=True, exist_ok=True)
            argv.extend([flag, str(target)])
            artifacts.append(target)
    argv.append(source)
    print('Checking', source, flush=True)
    start = time.monotonic()
    process = subprocess.run(argv, cwd=PROJECT, env=env, stdout=subprocess.PIPE,
                             stderr=subprocess.STDOUT)
    log = OUT / (label + '.log')
    log.write_bytes(process.stdout)
    checks['commands'].append({'source': source, 'source_sha256': sha(PROJECT / source),
        'argv': argv, 'exit_code': process.returncode,
        'elapsed_seconds': time.monotonic() - start, 'log': log.name,
        'log_sha256': sha(log),
        'artifacts': {str(a.relative_to(prefix)): sha(a) for a in artifacts if a.exists()}})
    save('fresh-checks.json', checks)
    print('Exit', process.returncode, flush=True)
    assert process.returncode == 0, process.stdout.decode()
    assert process.stdout.count(b'warning:') == holes, process.stdout.decode()
    assert process.stdout.count(b'declaration uses `sorry`') == holes

axioms = []
for label in ['fresh-proof', 'fresh-solution']:
    for name, items in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",
                                 (OUT / (label + '.log')).read_text()):
        names = [a.strip() for a in items.split(',') if a.strip()]
        assert set(names) == {'propext', 'Classical.choice', 'Quot.sound'}, (name, names)
        axioms.append({'declaration': name, 'axioms': names})
assert len(axioms) == 14
save('axioms.json', {'source_kernel_assertions': 14, 'reports': axioms})

graph = (OUT / 'fresh-inspection.log').read_text()
assert graph.count('RETAINED_DEPENDENCY:') == 20
save('retained-dependencies.json', {
    'required_count': 20,
    'required': re.findall(r'RETAINED_DEPENDENCY: ([^\n]+)', graph),
    'project_declarations': int(re.search(r'PROJECT_DECLARATIONS: (\d+)', graph).group(1)),
    'LeanCert_scope': 'Explicit kernel trust audit of exact counting and real-power proof; no interval certificate'})
after = {}
for name, info in inputs.items():
    current = sha(name)
    assert current == info['current_sha256'], name
    after[name] = {'before': info['current_sha256'], 'after': current, 'unchanged': True}
save('inputs-after.json', after)
print('PASS: eight fresh modules/inspection, 14 standard-three kernel audits, seven alpha-matching signatures, ten clean pins and unchanged statement inputs', flush=True)
