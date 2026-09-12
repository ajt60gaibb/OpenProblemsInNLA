"""MI-22 statement-only fresh elaboration, immutable-source and pin audit.
Adapted from the same author's previous NLA statement-gate drivers.
No mathematical proof is implemented by this script.
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


assert not (PROJECT / 'NLA/MI22/Proof.lean').exists()
assert not (PROJECT / 'Solution.lean').exists()
names = ['NLA/MI22/Definitions.lean', 'Challenge.lean', 'NUMERICAL_TARGETS.md',
         'SOURCE_CORRESPONDENCE.md', 'README.md', 'comparator.json', 'lakefile.toml',
         'lake-manifest.json', 'lean-toolchain', 'LICENSE', '.gitignore',
         'reviews/InspectStatements.lean', 'reviews/check_and_freeze.py',
         'reviews/reconstruct.py', 'reviews/reconstruction.json',
         'reviews/source-hashes.json', 'reviews/duplicate-scope.json',
         'reviews/statement-build.log', 'reviews/statement-build.json']
before = {name: sha(PROJECT / name) for name in names}
source_manifest = json.loads((OUT / 'source-hashes.json').read_text())
for name, digest in source_manifest['source_files'].items():
    assert sha(REPO / name) == digest, name
save('inputs-before.json', {'files': before, 'source_files': source_manifest['source_files']})

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

(PROJECT / '.verification').mkdir(exist_ok=True)
prefix = Path(tempfile.mkdtemp(prefix='mi22-statement-', dir=PROJECT / '.verification'))
old_path = capture([str(BIN / 'lake'), 'env', 'printenv', 'LEAN_PATH'])
old_target = (PROJECT / '.lake/build/lib/lean').resolve()
parts = [p for p in old_path.split(os.pathsep) if Path(p).resolve() != old_target]
assert len(parts) + 1 == len(old_path.split(os.pathsep))
env = dict(os.environ)
env['LEAN_PATH'] = os.pathsep.join([str(prefix)] + parts)
checks = {'stage': 'Statements only; no proof implementation',
          'date_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
          'platform': platform.platform(),
          'lean_version': capture([str(BIN / 'lean'), '--version']),
          'fresh_prefix': str(prefix), 'LEAN_PATH': env['LEAN_PATH'],
          'old_project_build_excluded': str(old_target),
          'scope': 'Fresh macOS statement compilation, pinned dependency artifacts reused',
          'commands': []}
for source, label, holes, produce in [
        ('NLA/MI22/Definitions.lean', 'fresh-definitions', 0, True),
        ('Challenge.lean', 'fresh-challenge', 8, True),
        ('reviews/InspectStatements.lean', 'fresh-inspection', 0, False)]:
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
    started = time.monotonic()
    process = subprocess.run(argv, cwd=PROJECT, env=env, stdout=subprocess.PIPE,
                             stderr=subprocess.STDOUT)
    log = OUT / (label + '.log')
    log.write_bytes(process.stdout)
    checks['commands'].append({'source': source, 'source_sha256': sha(PROJECT / source),
        'argv': argv, 'exit_code': process.returncode,
        'elapsed_seconds': time.monotonic() - started, 'log': log.name,
        'log_sha256': sha(log),
        'artifacts': {str(a.relative_to(prefix)): sha(a) for a in artifacts if a.exists()}})
    save('fresh-checks.json', checks)
    print('Exit', process.returncode, flush=True)
    assert process.returncode == 0, process.stdout.decode()
    assert process.stdout.count(b'warning:') == holes, process.stdout.decode()
    assert process.stdout.count(b'declaration uses `sorry`') == holes

text = (OUT / 'fresh-inspection.log').read_text()
axioms = []
for name, items in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text):
    names_used = [x.strip() for x in items.split(',') if x.strip()]
    assert set(names_used) <= {'propext', 'Classical.choice', 'Quot.sound'}, (name, names_used)
    axioms.append({'declaration': name, 'axioms': names_used})
for name in re.findall(r"'([^']+)' does not depend on any axioms", text):
    axioms.append({'declaration': name, 'axioms': []})
assert len(axioms) == 23
save('definition-axioms.json', {'actual_kernel_checks': 23, 'reports': axioms})
for name, digest in before.items():
    assert sha(PROJECT / name) == digest, name
for name, digest in source_manifest['source_files'].items():
    assert sha(REPO / name) == digest, name
assert not (PROJECT / 'NLA/MI22/Proof.lean').exists()
assert not (PROJECT / 'Solution.lean').exists()
save('inputs-after.json', {'files': before, 'source_files': source_manifest['source_files'],
                          'all_unchanged': True})

bound_names = names + ['reviews/inputs-before.json', 'reviews/inputs-after.json',
    'reviews/dependency-pins.json', 'reviews/fresh-checks.json',
    'reviews/fresh-definitions.log', 'reviews/fresh-challenge.log',
    'reviews/fresh-inspection.log', 'reviews/definition-axioms.json']
save('statement-freeze.json', {
    'stage': 'Statements only; two independent approvals required before proof',
    'base_commit': source_manifest['base_commit'],
    'branch': 'codex/lean-mi22-singular-value-log-majorization',
    'files': {name: sha(PROJECT / name) for name in bound_names},
    'source_files': source_manifest['source_files'],
    'adapted_witness_explicitly_distinguished_from_source': True,
    'proof_files_present': False, 'fresh_statement_modules_passed': 3,
    'intentional_challenge_holes': 8, 'definition_kernel_audits': 23,
    'clean_dependency_pins': 10, 'statement_build_reported_jobs': 2723})
print('PASS: three fresh modules, eight intentional holes, 23 definition audits, ten clean pins, '
      'all original inputs unchanged; no proof implementation.', flush=True)
print('Freeze SHA256:', sha(OUT / 'statement-freeze.json'), flush=True)
