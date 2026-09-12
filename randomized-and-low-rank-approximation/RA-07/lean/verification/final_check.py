"""Author's fresh local check. Does not edit mathematics or dependency sources."""
from pathlib import Path
import datetime, hashlib, json, os, platform, re, subprocess, tempfile, time

OUT = Path(__file__).resolve().parent
PROJECT = OUT.parent
REPO = PROJECT.parents[2]

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def save(name, value):
    (OUT / name).write_text(json.dumps(value, indent=2) + '\n')

def capture(command, cwd=PROJECT):
    result = subprocess.run(command, cwd=cwd, capture_output=True, text=True)
    if result.returncode:
        raise RuntimeError(f'{command}: {result.stderr}')
    return result.stdout.strip()

statement = json.loads((PROJECT / 'reviews/statement-freeze.json').read_text())
paths, expected = {}, {}
for category in ['mathematical_sha256', 'configuration_sha256', 'documentation_sha256',
                 'source_sha256', 'evidence_sha256']:
    for name, digest in statement[category].items():
        paths[name] = (REPO if category == 'source_sha256' else PROJECT) / name
        expected[name] = digest
for name, info in json.loads((OUT / 'proof-start.json').read_text())['files'].items():
    paths[name], expected[name] = PROJECT / name, info['sha256']
for name in ['NLA/RA07/Algebra.lean', 'NLA/RA07/Roots.lean', 'NLA/RA07/Sums.lean',
             'NLA/RA07/Proof.lean', 'Solution.lean']:
    paths[name], expected[name] = PROJECT / name, sha(PROJECT / name)
before = {}
for name, path in paths.items():
    assert sha(path) == expected[name], name
    before[name] = {'sha256': sha(path), 'bytes': path.stat().st_size}
save('inputs-before.json', before)

packages = []
for package in json.loads((PROJECT / 'lake-manifest.json').read_text())['packages']:
    folder = PROJECT / '.lake/packages' / package['name']
    head = capture(['git', 'rev-parse', 'HEAD'], folder)
    status = capture(['git', 'status', '--porcelain'], folder)
    assert head == package['rev'] and not status, package['name']
    packages.append({'name': package['name'], 'expected': package['rev'], 'actual': head,
                     'source_status': status, 'matches_pin': True})
save('dependencies.json', packages)

challenge = (PROJECT / 'Challenge.lean').read_text()
solution = (PROJECT / 'Solution.lean').read_text()
pattern = re.compile(r'^theorem ([A-Za-z_0-9]+)(.*?):= by', re.M | re.S)
cs = {name: signature.strip() for name, signature in pattern.findall(challenge)}
ss = {name: signature.strip() for name, signature in pattern.findall(solution)}
assert cs == ss and len(cs) == 6
config = json.loads((PROJECT / 'comparator.json').read_text())
names = ['NLA.RA07.' + name for name in cs]
assert config['theorem_names'] == names and config['definition_names'] == []
assert set(config['permitted_axioms']) == {'propext', 'Classical.choice', 'Quot.sound'}
implementation_paths = sorted((PROJECT / 'NLA/RA07').glob('*.lean')) + [PROJECT / 'Solution.lean']
implementation_text = '\n'.join(p.read_text() for p in implementation_paths)
for path in implementation_paths:
    clean = re.sub(r'/-.*?-/', '', path.read_text(), flags=re.S)
    clean = re.sub(r'--[^\n]*', '', clean)
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b', clean), path
    assert not re.search(r'^import\s+Challenge\b', clean, re.M), path
save('source-audit.json', {'verbatim_signatures': names, 'definition_names': [],
    'implementation_forbidden_constructs': [], 'challenge_imported': False,
    'intentional_Challenge_placeholders': len(re.findall(r'\bsorry\b', challenge)),
    'source_kernel_assertions': implementation_text.count('#assert_trust kernel'),
    'source_axiom_prints': implementation_text.count('#print axioms'),
    'interval_certificates': 0,
    'trust_scope': 'Exact algebraic theorem; LeanCert kernel assertions, no artificial interval witness.'})

parent = PROJECT / '.verification'
parent.mkdir(exist_ok=True)
prefix = Path(tempfile.mkdtemp(prefix='ra07-author-final-', dir=parent))
original_path = capture(['lake', 'env', 'printenv', 'LEAN_PATH'])
old_target = (PROJECT / '.lake/build/lib/lean').resolve()
dependencies = [part for part in original_path.split(os.pathsep) if Path(part).resolve() != old_target]
assert len(dependencies) + 1 == len(original_path.split(os.pathsep))
env = dict(os.environ)
env['LEAN_PATH'] = os.pathsep.join([str(prefix)] + dependencies)
checks = {'date_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'platform': platform.platform(), 'lean_version': capture(['lean', '--version']),
    'repository_head': capture(['git', 'rev-parse', 'HEAD']),
    'fresh_prefix': str(prefix), 'LEAN_PATH': env['LEAN_PATH'],
    'old_project_target_prefix_excluded': True,
    'scope': 'Fresh macOS project target compilation; existing dependency caches reused at ten checked clean pins. Linux Comparator and independent final referees remain pending.',
    'commands': []}
jobs = [(f'NLA/RA07/{module}.lean', f'{module.lower()}.log', True)
        for module in ['Definitions', 'Algebra', 'Roots', 'Sums', 'Proof']]
jobs += [('Solution.lean', 'solution.log', True), ('Challenge.lean', 'challenge.log', True),
         ('verification/InspectProof.lean', 'inspection.log', False)]
for source, log, produce in jobs:
    command, artifacts = ['lean'], []
    if produce:
        for suffix, flag in [('.olean', '-o'), ('.ilean', '-i')]:
            output = prefix / Path(source).with_suffix(suffix)
            output.parent.mkdir(parents=True, exist_ok=True)
            command += [flag, str(output)]
            artifacts.append(output)
    command.append(source)
    print(f'Checking {source}', flush=True)
    start = time.monotonic()
    result = subprocess.run(command, cwd=PROJECT, env=env,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (OUT / log).write_bytes(result.stdout)
    elapsed = time.monotonic() - start
    checks['commands'].append({'source': source, 'source_sha256': sha(PROJECT / source),
        'command': command, 'exit_code': result.returncode, 'elapsed_seconds': elapsed,
        'log': log, 'log_sha256': sha(OUT / log),
        'artifacts': {str(p.relative_to(prefix)): sha(p) for p in artifacts if p.exists()}})
    save('fresh-checks.json', checks)
    print(f'Exit {result.returncode}, {elapsed:.2f}s: {log}', flush=True)
    if result.returncode:
        print(result.stdout.decode(), flush=True)
        raise SystemExit(result.returncode)
    if source != 'Challenge.lean':
        assert not re.search(rb'\b(error|warning):', result.stdout), source

reports = []
for log in ['proof.log', 'solution.log']:
    for name, axioms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", (OUT / log).read_text()):
        values = [a.strip() for a in axioms.split(',') if a.strip()]
        assert set(values) == {'propext', 'Classical.choice', 'Quot.sound'}, name
        reports.append({'declaration': name, 'axioms': values, 'log': log})
assert len(reports) == 12
save('axiom-audit.json', {'reports': reports, 'count': 12, 'all_exact_standard_three': True})
after = {}
for name, path in paths.items():
    current = sha(path)
    assert current == before[name]['sha256'], name
    after[name] = {'before': before[name]['sha256'], 'after': current, 'unchanged': True}
save('inputs-after.json', after)
print(f'PASS: {len(paths)} inputs unchanged; 12 standard-three axiom reports; six exact public signatures.', flush=True)
