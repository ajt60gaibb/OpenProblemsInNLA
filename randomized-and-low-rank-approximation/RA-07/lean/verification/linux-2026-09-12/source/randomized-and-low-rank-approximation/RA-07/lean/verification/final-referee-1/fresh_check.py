"""Independent final referee 1 source re-elaboration and integrity audit.

Reviewer: Codex agent /root/leancert_examples, not the RA-07 implementer.
Fresh-prefix pattern follows earlier NLA reviews and the author's separate
verification/final_check.py; this script writes only the referee's new evidence.
It does not run or claim the Linux Comparator stage.
"""

from pathlib import Path
import datetime, hashlib, json, os, platform, re, subprocess, tempfile, time

OUT = Path(__file__).resolve().parent
PROJECT = OUT.parent.parent
REPO = PROJECT.parents[2]
BIN = Path('/Users/georgestepaniants/.elan/toolchains/leanprover--lean4---v4.33.1/bin')
LEAN = str(BIN / 'lean')
LAKE = str(BIN / 'lake')

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def save(name, obj):
    (OUT / name).write_text(json.dumps(obj, indent=2) + '\n')

def capture(argv, cwd=PROJECT):
    result = subprocess.run(argv, cwd=cwd, capture_output=True, text=True)
    if result.returncode:
        raise RuntimeError((argv, result.stdout, result.stderr))
    return result.stdout.strip()

assert sha(PROJECT / 'verification/proof-freeze.json') == 'ecd94daf2dee9fe4625e09f1a08026eb75ac8a14bea6efb688921a3e78eb6b4a'
assert sha(PROJECT / 'reviews/proof-completion.md') == 'c80547f6d812d879d7e7d9d7ed05c089146b6e0ad3a208c27d3b666b49981689'
freeze = json.loads((PROJECT / 'verification/proof-freeze.json').read_text())
inputs = {}
for field, base in [('files', PROJECT), ('original_sources', REPO)]:
    for name, entry in freeze[field].items():
        path = base / name
        assert sha(path) == entry['sha256'], name
        assert path.stat().st_size == entry['bytes'], name
        inputs[str(path)] = entry
save('inputs-before.json', inputs)

pins = []
for package in json.loads((PROJECT / 'lake-manifest.json').read_text())['packages']:
    folder = PROJECT / '.lake/packages' / package['name']
    head = capture(['git', 'rev-parse', 'HEAD'], folder)
    status = capture(['git', 'status', '--porcelain'], folder)
    assert head == package['rev'] and status == '', package['name']
    pins.append({'name': package['name'], 'expected': package['rev'], 'actual': head,
                 'git_status_porcelain': status})
assert len(pins) == 10
save('dependencies.json', pins)

challenge = (PROJECT / 'Challenge.lean').read_text()
solution = (PROJECT / 'Solution.lean').read_text()
pattern = re.compile(r'^theorem ([A-Za-z_0-9]+)(.*?):= by', re.M | re.S)
cs = dict(pattern.findall(challenge))
ss = dict(pattern.findall(solution))
assert cs == ss and len(cs) == 6
comparator = json.loads((PROJECT / 'comparator.json').read_text())
assert comparator['theorem_names'] == ['NLA.RA07.' + name for name in cs]
assert comparator['definition_names'] == []
assert set(comparator['permitted_axioms']) == {'propext','Classical.choice','Quot.sound'}
sources = list((PROJECT / 'NLA/RA07').glob('*.lean')) + [PROJECT / 'Solution.lean']
for path in sources:
    clean = re.sub(r'/-.*?-/', '', path.read_text(), flags=re.S)
    clean = re.sub(r'--[^\n]*', '', clean)
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b', clean), path
    assert not re.search(r'^import\s+Challenge\b', clean, re.M), path
save('source-audit.json', {'signatures_verbatim_equal': list(cs),
    'comparator_exact_export_match': True, 'definition_holes': [],
    'forbidden_implementation_constructs': [], 'challenge_imported_by_implementation': False,
    'intentional_challenge_holes': len(re.findall(r'\bsorry\b', challenge)),
    'source_kernel_assertions': sum(p.read_text().count('#assert_trust kernel') for p in sources)})

(PROJECT / '.verification').mkdir(exist_ok=True)
prefix = Path(tempfile.mkdtemp(prefix='ra07-independent-final-referee-1-', dir=PROJECT / '.verification'))
old_path = capture([LAKE, 'env', 'printenv', 'LEAN_PATH'])
old_target = (PROJECT / '.lake/build/lib/lean').resolve()
dependencies = [p for p in old_path.split(os.pathsep) if Path(p).resolve() != old_target]
assert len(dependencies) + 1 == len(old_path.split(os.pathsep))
env = dict(os.environ)
env['LEAN_PATH'] = os.pathsep.join([str(prefix)] + dependencies)
checks = {'reviewer': '/root/leancert_examples', 'independent_of_implementation': True,
    'date_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'platform': platform.platform(), 'lean_version': capture([LEAN, '--version']),
    'repository_head': capture(['git', 'rev-parse', 'HEAD']),
    'fresh_prefix': str(prefix), 'LEAN_PATH': env['LEAN_PATH'],
    'author_project_artifacts_excluded': str(old_target),
    'scope': 'Fresh macOS source elaboration with pinned dependency artifacts reused; no Linux Comparator claim',
    'commands': []}
jobs = [(f'NLA/RA07/{name}.lean', name.lower(), True)
        for name in ['Definitions','Algebra','Roots','Sums','Proof']]
jobs += [('Solution.lean','solution',True), ('Challenge.lean','challenge',True),
         ('verification/final-referee-1/Inspect.lean','inspection',False)]
for source, label, produce in jobs:
    argv = [LEAN]
    artifacts = []
    if produce:
        for suffix, flag in [('.olean','-o'),('.ilean','-i')]:
            output = prefix / Path(source).with_suffix(suffix)
            output.parent.mkdir(parents=True, exist_ok=True)
            argv += [flag,str(output)]
            artifacts.append(output)
    argv.append(source)
    print('Checking', source, flush=True)
    start = time.monotonic()
    result = subprocess.run(argv, cwd=PROJECT, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    logfile = OUT / (label + '.log')
    logfile.write_bytes(result.stdout)
    checks['commands'].append({'source': source, 'source_sha256': sha(PROJECT/source),
        'argv': argv, 'exit_code': result.returncode, 'elapsed_seconds': time.monotonic()-start,
        'log': logfile.name, 'log_sha256': sha(logfile),
        'artifacts': {str(p.relative_to(prefix)):sha(p) for p in artifacts if p.exists()}})
    save('fresh-checks.json', checks)
    print('Exit', result.returncode, 'log', logfile.name, flush=True)
    assert result.returncode == 0, result.stdout.decode()
    if source != 'Challenge.lean':
        assert not re.search(rb'\b(error|warning):', result.stdout), source

reports = []
for log in ['proof.log','solution.log','inspection.log']:
    for name, axioms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", (OUT/log).read_text()):
        values = [a.strip() for a in axioms.split(',') if a.strip()]
        assert set(values) == {'propext','Classical.choice','Quot.sound'}, (name,values)
        reports.append({'declaration':name,'axioms':values,'log':log})
assert len(reports) == 18
assert len({r['declaration'] for r in reports}) == 12
save('axiom-audit.json', {'reports':reports,'actual_standard_three_checks':18,'distinct_declarations':12})
after = {}
for path, entry in inputs.items():
    current = sha(path)
    assert current == entry['sha256'], path
    after[path] = {'before':entry['sha256'],'after':current,'unchanged':True}
save('inputs-after.json', after)
print(f'PASS: {len(inputs)} frozen inputs unchanged; 18 standard-three checks, 12 distinct declarations; six exact exports',flush=True)
