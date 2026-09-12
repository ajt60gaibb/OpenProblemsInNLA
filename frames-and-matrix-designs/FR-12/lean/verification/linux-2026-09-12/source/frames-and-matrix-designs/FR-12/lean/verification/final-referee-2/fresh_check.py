"""Independent final referee 2's fresh FR-12 target compilation and evidence.
Shares the campaign's fresh-prefix method, but independently verifies every
proof-freeze entry and executes a separate reviewer-authored declaration audit.
No prior logs or target .olean files are accepted as proof of this run.
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
PROJECT = OUT.parents[1]
REPO = PROJECT.parents[2]
BIN = Path('/Users/georgestepaniants/.elan/toolchains/leanprover--lean4---v4.33.1/bin')


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def save(name, value):
    (OUT / name).write_text(json.dumps(value, indent=2) + '\n')


def capture(argv, cwd=PROJECT):
    return subprocess.run(argv, cwd=cwd, text=True, capture_output=True, check=True).stdout.strip()


freeze_path = PROJECT / 'reviews/proof-freeze.json'
completion_path = PROJECT / 'reviews/proof-completion.md'
assert sha(freeze_path) == 'c65d4deaa3e02af8c20a584dd81b944dbdc72f262e326630e115e5fc9070aa87'
assert sha(completion_path) == '56bf908a87f234581dd2d93e0f975d17b95f1fddce81ba01b5e6821902474666'
freeze = json.loads(freeze_path.read_text())
assert len(freeze['files']) == 74 and len(freeze['source_files']) == 4
before = {}
for group, root in [('files', PROJECT), ('source_files', REPO)]:
    for name, expected in freeze[group].items():
        path = root / name
        actual = sha(path)
        assert actual == expected, (name, expected, actual)
        before[str(path)] = {'group': group, 'expected': expected, 'actual': actual}
for path in [freeze_path, completion_path]:
    before[str(path)] = {'group': 'handoff', 'expected': sha(path), 'actual': sha(path)}
statement_freeze = json.loads((PROJECT / 'reviews/statement-freeze.json').read_text())
assert len(statement_freeze['files']) == 19
for name, digest in statement_freeze['files'].items():
    assert sha(PROJECT / name) == digest
save('inputs-before.json', before)

pins = []
for package in json.loads((PROJECT / 'lake-manifest.json').read_text())['packages']:
    folder = PROJECT / '.lake/packages' / package['name']
    actual = capture(['git', 'rev-parse', 'HEAD'], folder)
    dirty = capture(['git', 'status', '--porcelain'], folder)
    assert actual == package['rev'] and dirty == '', (package['name'], actual, dirty)
    pins.append({'name': package['name'], 'manifest_commit': package['rev'],
                 'actual_commit': actual, 'git_status_porcelain': dirty})
assert len(pins) == 10
save('dependency-pins.json', pins)

def signatures(path):
    return {name: ' '.join(statement.split()) for name, statement in
            re.findall(r'theorem\s+(\w+)\s+(.*?)\s*:=\s*by',
                       path.read_text(), flags=re.S)}

challenge = signatures(PROJECT / 'Challenge.lean')
solution = signatures(PROJECT / 'Solution.lean')
assert len(challenge) == len(solution) == 7
solution['counting_semantics'] = solution['counting_semantics'].replace('_hn', 'hn')
assert challenge == solution
config = json.loads((PROJECT / 'comparator.json').read_text())
assert set(config['theorem_names']) == {'NLA.FR12.' + name for name in challenge}
assert config['definition_names'] == []
assert set(config['permitted_axioms']) == {'propext', 'Classical.choice', 'Quot.sound'}
save('source-signatures.json', {'status': 'PASS', 'count': len(solution),
    'alpha_rename': 'unused forall binder _hn in Solution versus hn in Challenge',
    'limitation': 'Source-level complete signature comparison, not Linux Comparator',
    'statements': solution})

implementation = ['NLA/FR12/Definitions.lean', 'NLA/FR12/Semantics.lean',
    'NLA/FR12/Doubling.lean', 'NLA/FR12/Growth.lean', 'NLA/FR12/Proof.lean', 'Solution.lean']
for name in implementation:
    source = (PROJECT / name).read_text()
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b', source), name
    assert not re.search(r'^import\s+Challenge\b', source, re.M), name

prefix = Path(tempfile.mkdtemp(prefix='fr12-referee-2-', dir=PROJECT / '.verification'))
original_path = capture([str(BIN / 'lake'), 'env', 'printenv', 'LEAN_PATH'])
old_target = (PROJECT / '.lake/build/lib/lean').resolve()
original_parts = original_path.split(os.pathsep)
kept = [p for p in original_parts if Path(p).resolve() != old_target]
assert len(kept) == len(original_parts) - 1
env = dict(os.environ)
env['LEAN_PATH'] = os.pathsep.join([str(prefix)] + kept)
checks = {'independent_review': True, 'reviewer': '/root/leancert_examples',
    'date_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'platform': platform.platform(), 'lean_version': capture([str(BIN / 'lean'), '--version']),
    'fresh_prefix': str(prefix), 'LEAN_PATH': env['LEAN_PATH'],
    'excluded_project_build': str(old_target),
    'scope': 'Fresh target-module elaboration on macOS; matching compiled pinned dependency cache reused; no Linux claim',
    'commands': []}
jobs = [(name, 0, True) for name in implementation] + [
    ('Challenge.lean', 7, True), ('verification/final-referee-2/Inspect.lean', 0, False)]
for index, (source, expected_holes, produce) in enumerate(jobs):
    argv = [str(BIN / 'lean')]
    artifacts = []
    if produce:
        for suffix, flag in [('.olean', '-o'), ('.ilean', '-i')]:
            target = prefix / Path(source).with_suffix(suffix)
            target.parent.mkdir(parents=True, exist_ok=True)
            argv.extend([flag, str(target)])
            artifacts.append(target)
    argv.append(source)
    print('Fresh referee check:', source, flush=True)
    start = time.monotonic()
    result = subprocess.run(argv, cwd=PROJECT, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log = OUT / f'{index + 1:02d}-{Path(source).stem}.log'
    log.write_bytes(result.stdout)
    checks['commands'].append({'source': source, 'source_sha256': sha(PROJECT / source),
        'argv': argv, 'exit_code': result.returncode, 'elapsed_seconds': time.monotonic() - start,
        'log': log.name, 'log_sha256': sha(log),
        'artifacts': {str(p.relative_to(prefix)): sha(p) for p in artifacts if p.exists()}})
    save('fresh-checks.json', checks)
    print('Exit:', result.returncode, flush=True)
    assert result.returncode == 0, result.stdout.decode()
    assert result.stdout.count(b'warning:') == expected_holes, result.stdout.decode()
    assert result.stdout.count(b'declaration uses `sorry`') == expected_holes

axioms = []
for filename in ['05-Proof.log', '06-Solution.log', '08-Inspect.log']:
    for declaration, names in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", (OUT / filename).read_text()):
        values = [n.strip() for n in names.split(',') if n.strip()]
        assert set(values) == {'propext', 'Classical.choice', 'Quot.sound'}, (declaration, values)
        axioms.append({'log': filename, 'declaration': declaration, 'axioms': values})
assert len(axioms) == 21
save('axioms.json', {'status': 'PASS', 'source_assertions': 14, 'independent_assertions': 7,
                     'report_count': len(axioms), 'reports': axioms})
inspection = (OUT / '08-Inspect.log').read_text()
required = re.findall(r'REQUIRED_CONSUMED: ([^\n]+)', inspection)
assert len(required) == 25
save('actual-dependencies.json', {'required_count': 25, 'required': required,
    'project_declarations': int(re.search(r'REVIEWED_PROJECT_DECLARATIONS: (\d+)', inspection).group(1)),
    'LeanCert_scope': 'Explicit kernel audit only; exact counting proof requires no interval certificate'})
after = {}
for path, old in before.items():
    actual = sha(path)
    assert old['actual'] == actual, path
    after[path] = {'before': old['actual'], 'after': actual, 'unchanged': True}
save('inputs-after.json', after)
print('PASS: 8 fresh commands, 21 standard-three kernel audits, 25 retained bridges, 7 complete signatures, 10 clean pins, all 74+4 frozen files unchanged.', flush=True)
