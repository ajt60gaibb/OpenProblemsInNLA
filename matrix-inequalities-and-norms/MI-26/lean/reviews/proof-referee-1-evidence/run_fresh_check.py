"""Independent final proof review; no mathematical/configuration mutation."""
from pathlib import Path
import datetime, hashlib, json, os, platform, re, subprocess, tempfile, time

OUT = Path(__file__).resolve().parent
PROJECT = OUT.parents[1]
REPO = PROJECT.parents[2]

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def save(name, value):
    (OUT / name).write_text(json.dumps(value, indent=2) + '\n')

def capture(args, cwd=PROJECT):
    result = subprocess.run(args, cwd=cwd, capture_output=True, text=True)
    if result.returncode:
        raise RuntimeError(f'{args}: {result.stderr}')
    return result.stdout.strip()

freeze = json.loads((PROJECT / 'verification/proof-freeze.json').read_text())
statement = json.loads((PROJECT / 'verification/statement-freeze/hashes.json').read_text())
expected = dict(statement['project_files'])
expected.update(freeze['files'])
paths = {name: PROJECT / name for name in expected}
expected.update(statement['repository_sources'])
paths.update({name: REPO / name for name in statement['repository_sources']})
for name in ['verification/proof-freeze.json', 'verification/statement-freeze/hashes.json']:
    paths[name] = PROJECT / name
    expected[name] = {'sha256': sha(paths[name]), 'bytes': paths[name].stat().st_size}
before = {}
for name, path in paths.items():
    value = sha(path)
    assert value == expected[name]['sha256'] and path.stat().st_size == expected[name]['bytes'], name
    before[name] = {'sha256': value, 'bytes': path.stat().st_size, 'matches_freeze': True}
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
proof = (PROJECT / 'NLA/MI26/Proof.lean').read_text()
definitions = (PROJECT / 'NLA/MI26/Definitions.lean').read_text()
pattern = re.compile(r'^theorem ([A-Za-z_0-9]+)(.*?):= by', re.M | re.S)
cs = {name: signature.strip() for name, signature in pattern.findall(challenge)}
ss = {name: signature.strip() for name, signature in pattern.findall(solution)}
assert cs == ss and len(cs) == 7
config = json.loads((PROJECT / 'comparator.json').read_text())
names = ['NLA.MI26.' + name for name in cs]
assert config['theorem_names'] == names and config['definition_names'] == []
assert set(config['permitted_axioms']) == {'propext', 'Classical.choice', 'Quot.sound'}
for name, source in [('Definitions', definitions), ('Proof', proof), ('Solution', solution)]:
    clean = re.sub(r'/-.*?-/', '', source, flags=re.S)
    clean = re.sub(r'--[^\n]*', '', clean)
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b', clean), name
assert not re.search(r'^import\s+Challenge\b', proof + '\n' + solution, re.M)
save('source-audit.json', {'verbatim_signatures': names, 'definition_names': [],
    'implementation_forbidden_constructs': [], 'challenge_imported': False,
    'intentional_Challenge_placeholders': len(re.findall(r'\bsorry\b', challenge)),
    'source_kernel_assertions': (proof + solution).count('#assert_trust kernel'),
    'source_axiom_prints': (proof + solution).count('#print axioms')})

parent = PROJECT / '.verification'
parent.mkdir(exist_ok=True)
prefix = Path(tempfile.mkdtemp(prefix='mi26-proof-referee1-', dir=parent))
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
    'scope': 'Fresh macOS project target compilation; existing dependency caches reused at ten checked clean pins. No Linux Comparator or fresh dependency-source rebuild.',
    'commands': []}
jobs = [('NLA/MI26/Definitions.lean', 'definitions.log', True),
        ('NLA/MI26/Proof.lean', 'proof.log', True),
        ('Solution.lean', 'solution.log', True),
        ('Challenge.lean', 'challenge.log', True),
        ('reviews/proof-referee-1-evidence/InspectProof.lean', 'inspection.log', False),
        ('reviews/proof-referee-1-evidence/InspectSemantics.lean', 'semantics.log', False),
        ('reviews/proof-referee-1-evidence/InspectPowers.lean', 'powers.log', False)]
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

reports = []
for log in ['proof.log', 'solution.log']:
    text = (OUT / log).read_text()
    assert not re.search(r'\b(error|warning):', text)
    for name, axioms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text):
        values = [a.strip() for a in axioms.split(',') if a.strip()]
        assert set(values) == {'propext', 'Classical.choice', 'Quot.sound'}, name
        reports.append({'declaration': name, 'axioms': values, 'log': log})
assert len(reports) == 15
save('axiom-audit.json', {'reports': reports, 'count': 15, 'all_exact_standard_three': True})
after = {}
for name, path in paths.items():
    current = sha(path)
    assert current == before[name]['sha256'], name
    after[name] = {'before': before[name]['sha256'], 'after': current, 'unchanged': True}
save('inputs-after.json', after)
print(f'PASS: {len(paths)} frozen input files unchanged; 15 standard-three axiom reports; seven exact public signatures.', flush=True)
