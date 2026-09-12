"""Independent final referee: fresh target compilation, unchanged input receipts."""
from pathlib import Path
import datetime, hashlib, json, os, platform, re, subprocess, tempfile, time

EVIDENCE = Path(__file__).resolve().parent
PROJECT = EVIDENCE.parents[1]
REPO = PROJECT.parents[2]

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def capture(args, cwd=PROJECT):
    result = subprocess.run(args, cwd=cwd, capture_output=True, text=True)
    if result.returncode:
        raise RuntimeError(f'{args}: {result.stderr}')
    return result.stdout.strip()

def save(name, data):
    (EVIDENCE / name).write_text(json.dumps(data, indent=2) + '\n')

freeze = json.loads((PROJECT / 'reviews/proof-freeze.json').read_text())
statement = json.loads((PROJECT / 'reviews/statement-freeze.json').read_text())
receipt = json.loads((PROJECT / 'reviews/proof-build-result.json').read_text())
expected = {}
for category in ('mathematical_and_configuration_sha256', 'statement_approval_sha256',
                 'documentation_sha256'):
    expected.update(freeze[category])
expected['reviews/proof-build-result.json'] = freeze['proof_build_result_sha256']
expected.update(receipt['evidence_sha256'])
sources = statement['source_sha256']
paths = {name: PROJECT / name for name in expected}
paths.update({name: REPO / name for name in sources})
expected.update(sources)
for name in ('reviews/proof-freeze.json', 'reviews/statement-freeze.json'):
    paths[name] = PROJECT / name
    expected[name] = sha(paths[name])
before = {}
for name, path in paths.items():
    value = sha(path)
    assert value == expected[name], name
    before[name] = {'sha256': value, 'bytes': path.stat().st_size,
                    'expected_sha256': expected[name], 'matches_freeze': True}
save('inputs-before.json', before)

deps = []
for package in json.loads((PROJECT / 'lake-manifest.json').read_text())['packages']:
    directory = PROJECT / '.lake/packages' / package['name']
    head = capture(['git', 'rev-parse', 'HEAD'], directory)
    status = capture(['git', 'status', '--porcelain'], directory)
    assert head == package['rev'] and status == '', package['name']
    deps.append({'name': package['name'], 'expected': package['rev'],
                 'actual': head, 'status': status, 'matches_pin': True})
save('dependencies.json', deps)

challenge = (PROJECT / 'Challenge.lean').read_text()
solution = (PROJECT / 'Solution.lean').read_text()
proof = (PROJECT / 'NLA/MI06/Proof.lean').read_text()
definitions = (PROJECT / 'NLA/MI06/Definitions.lean').read_text()
signature_re = re.compile(r'^theorem ([A-Za-z_0-9]+)(.*?):= by', re.M | re.S)
cs = {n: s.strip() for n, s in signature_re.findall(challenge)}
ss = {n: s.strip() for n, s in signature_re.findall(solution)}
assert cs == ss and len(cs) == 6
actual_exports = ['NLA.MI06.' + name for name in cs]
config = json.loads((PROJECT / 'comparator.json').read_text())
assert config['theorem_names'] == actual_exports == freeze['public_exports']
assert config['definition_names'] == []
assert set(config['permitted_axioms']) == {'propext', 'Classical.choice', 'Quot.sound'}
forbidden = re.compile(r'\b(sorry|admit|axiom|native_decide|unsafe)\b')
stripped = {}
for name, content in [('Definitions', definitions), ('Proof', proof), ('Solution', solution)]:
    clean = re.sub(r'/-.*?-/', '', content, flags=re.S)
    clean = re.sub(r'--[^\n]*', '', clean)
    stripped[name] = clean
    assert not forbidden.search(clean), name
assert not re.search(r'^import\s+Challenge\b', proof + '\n' + solution, re.M)
save('source-audit.json', {
    'verbatim_signatures': actual_exports, 'definitions_names': [],
    'challenge_intended_placeholders': len(re.findall(r'\bby sorry\b', challenge)),
    'implementation_forbidden_constructs': [], 'challenge_imported': False,
    'explicit_kernel_assertions_in_Proof_and_Solution': (proof + solution).count('#assert_trust kernel'),
    'explicit_axiom_prints_in_Proof_and_Solution': (proof + solution).count('#print axioms'),
    'permitted_axioms': config['permitted_axioms']})

prefix_parent = PROJECT / '.verification'
prefix_parent.mkdir(exist_ok=True)
prefix = Path(tempfile.mkdtemp(prefix='mi06-proof-referee1-', dir=prefix_parent))
lake_path = capture(['lake', 'env', 'printenv', 'LEAN_PATH'])
old_prefix = (PROJECT / '.lake/build/lib/lean').resolve()
dep_paths = [p for p in lake_path.split(os.pathsep) if Path(p).resolve() != old_prefix]
assert len(dep_paths) + 1 == len(lake_path.split(os.pathsep))
env = dict(os.environ)
env['LEAN_PATH'] = os.pathsep.join([str(prefix)] + dep_paths)
checks = {'date_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
          'platform': platform.platform(), 'lean_version': capture(['lean', '--version']),
          'repository_head': capture(['git', 'rev-parse', 'HEAD']),
          'branch': capture(['git', 'branch', '--show-current']),
          'fresh_prefix': str(prefix), 'LEAN_PATH': env['LEAN_PATH'],
          'old_target_prefix_excluded': True,
          'scope': 'Independent macOS target compilation using reused dependency caches at ten checked clean pins. Not a Linux Comparator or dependency-from-source build.',
          'commands': []}
jobs = [
    ('NLA/MI06/Definitions.lean', 'definitions.log', True),
    ('NLA/MI06/Proof.lean', 'proof.log', True),
    ('Solution.lean', 'solution.log', True),
    ('Challenge.lean', 'challenge.log', True),
    ('reviews/proof-referee-1-evidence/InspectProof.lean', 'inspection.log', False),
    ('reviews/proof-referee-1-evidence/InspectSemantics.lean', 'semantics.log', False),
]
for source, log, produce in jobs:
    command = ['lean']
    artifacts = []
    if produce:
        for suffix, flag in (('.olean', '-o'), ('.ilean', '-i')):
            output = prefix / Path(source).with_suffix(suffix)
            output.parent.mkdir(parents=True, exist_ok=True)
            command.extend([flag, str(output)])
            artifacts.append(output)
    command.append(source)
    print(f'Checking {source}', flush=True)
    start = time.monotonic()
    result = subprocess.run(command, cwd=PROJECT, env=env,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    elapsed = time.monotonic() - start
    (EVIDENCE / log).write_bytes(result.stdout)
    checks['commands'].append({'source': source, 'source_sha256': sha(PROJECT / source),
        'command': command, 'exit_code': result.returncode, 'elapsed_seconds': elapsed,
        'log': log, 'log_sha256': sha(EVIDENCE / log),
        'artifacts': {str(p.relative_to(prefix)): sha(p) for p in artifacts if p.exists()}})
    save('fresh-checks.json', checks)
    print(f'Exit {result.returncode}, {elapsed:.2f}s: {log}', flush=True)
    if result.returncode:
        print(result.stdout.decode(), flush=True)
        raise SystemExit(result.returncode)

reports = []
for log in ['proof.log', 'solution.log']:
    text = (EVIDENCE / log).read_text()
    assert not re.search(r'\b(error|warning):', text)
    for name, axioms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text):
        values = [a.strip() for a in axioms.split(',') if a.strip()]
        assert set(values) == {'propext', 'Classical.choice', 'Quot.sound'}, name
        reports.append({'declaration': name, 'axioms': values, 'log': log})
assert len(reports) == 52
save('axiom-audit.json', {'count': len(reports), 'all_exact_standard_three': True,
                         'reports': reports})
after = {}
for name, path in paths.items():
    value = sha(path)
    assert value == before[name]['sha256'], name
    after[name] = {'before': before[name]['sha256'], 'after': value, 'unchanged': True}
save('inputs-after.json', after)
print(f'PASS: {len(paths)} frozen files unchanged; ten clean pinned dependencies; 52 standard-three axiom reports.', flush=True)
