#!/usr/bin/env python3
"""Independent read-only authentication. Never invokes Lean/Lake/Comparator."""
from pathlib import Path
import datetime, gzip, hashlib, json, re, subprocess

D = Path('/Users/georgestepaniants/Research/OpenProblemsInNLA/.local-recovery-20260918')
S = D / 'final-review-packets/MI27-v1'
E = D / 'verification/MI27-local-20260919'
T = D / 'verification/MI27-type-preflight-118'
R = D / 'reviews/MI27-final-referee-b'
L = D / 'local-lean'
def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def digest(b):
    return hashlib.sha256(b).hexdigest()
def check(p, expected):
    assert Path(p).is_file(), ('missing', str(p))
    assert sha(p) == expected, ('hash', str(p), sha(p), expected)

check(S / 'REVIEW-SNAPSHOT.json', 'd9a8bb1b4cf6e228d6c211c57f58cfd79e710f3961dffe65cb06db6c39249790')
check(E / 'LOCAL-REPLAY-AUDIT.json', '17230c39a125c0f67931aa3259679ff7fa6e14b90541c353fe99cb3dd938a390')
check(T / 'AUDIT.json', '8ebb6afdb40ed9c83abad156d5e6fd522bddfcb000da71181afd34af1cc620db')
snap = json.loads((S / 'REVIEW-SNAPSHOT.json').read_text())
for rel, h in snap['files'].items():
    check(S / rel, h)
actual_files = {str(p.relative_to(S)) for p in S.rglob('*') if p.is_file()}
assert actual_files == set(snap['files']) | {'REVIEW-SNAPSHOT.json'}
assert not any(p.is_symlink() for p in S.rglob('*'))
proof = {p[:-5].replace('/', '.'): p for p in snap['files']
         if p.endswith('.lean') and (p.startswith('NLA/') or p == 'Solution.lean')}
assert len(proof) == 52
old = json.loads((D / 'reviews/MI27-prefinal-stable-referee-b/PREFINAL-SNAPSHOT.json').read_text())
for rel, rec in old['sources'].items():
    check(S / rel, rec['sha256'])
    check(rec['reviewed_copy'], rec['sha256'])
pre = D / 'reviews/MI27-final-referee-b-preliminary-read'
for name in ['EntropyTrajectory', 'LogarithmicCommutatorDual', 'LogarithmicCommutator']:
    check(S / 'NLA/MI27' / (name + '.lean'), sha(pre / (name + '.lean')))
for current, prior in [('source-context/canonical-README.md', 'CANONICAL-README.md'),
                       ('source-context/holden-solution.md', 'MATHEMATICAL-SOURCE.md'),
                       ('source-context/holden-solution.tex', 'MATHEMATICAL-SOURCE.tex')]:
    check(S / current, sha(D / 'reviews/MI27-prefinal-stable-referee-b/source-context' / prior))

cfg = json.loads((S / 'comparator.json').read_text())
names = cfg['theorem_names']
assert len(names) == len(set(names)) == 20
assert cfg['definition_names'] == []
assert cfg['challenge_module'] == 'Challenge' and cfg['solution_module'] == 'Solution'
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
assert set(cfg['permitted_axioms']) == allowed
freeze = json.loads((S / 'STATEMENT-FREEZE.json').read_text())
for rel, h in freeze['frozen_files'].items():
    check(S / rel, h)
assert freeze['contract_names'] == names

imports = {}
headers = {}
for mod, rel in proof.items():
    text = (S / rel).read_text()
    plain = re.sub(r'/-.*?-/', '', text, flags=re.S)
    plain = re.sub(r'--[^\n]*', '', plain)
    assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by|ofReduceBool)\b|skipKernelTC|^\s*opaque\b|^\s*run_cmd\b', plain, re.M), rel
    imports[mod] = [word for line in plain.splitlines() if line.startswith('import ')
                    for word in line[7:].split() if not word.startswith(('Mathlib.', 'LeanCert.'))]
    assert all(d in proof for d in imports[mod]), (mod, imports[mod])
    for m in re.finditer(r'^theorem\s+(\w+)(.*?)\s*:=\s*by', text, re.M | re.S):
        full = 'NLA.MI27.' + m.group(1)
        if full in names:
            assert full not in headers
            headers[full] = {'module': mod, 'header': re.sub(r'\s+', ' ', m.group(2)).strip()}
reference = (S / 'Challenge.lean').read_text()
for m in re.finditer(r'^theorem\s+(\w+)(.*?)\s*:=\s*by', reference, re.M | re.S):
    full = 'NLA.MI27.' + m.group(1)
    assert headers[full]['header'] == re.sub(r'\s+', ' ', m.group(2)).strip(), full
assert set(headers) == set(names)
closures = {}
def closure(m, active=()):
    assert m not in active
    if m not in closures:
        result = {m}
        for dep in imports[m]:
            result.update(closure(dep, active + (m,)))
        closures[m] = result
    return closures[m]
assert closure('Solution') == set(proof)

audit = json.loads((E / 'LOCAL-REPLAY-AUDIT.json').read_text())
env = json.loads((E / 'LOCAL-ENVIRONMENT.json').read_text())
check(env['compiler'], env['compiler_sha256'])
assert audit['compiler_sha256'] == env['compiler_sha256']
check(E / 'serial_compile_recovery.py', audit['runner_sha256'])
check(L / 'serial_compile_recovery.py', audit['runner_sha256'])
assert env['threads'] == 1 and env['memory_cap_mib'] == 4096
lock = json.loads((S / 'lake-manifest.json').read_text())
pins = {p['name']: p['rev'] for p in lock['packages']}
observed_packages = {}
for p in env['packages']:
    actual = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=p['path'], text=True).strip()
    assert actual == p['commit'] == pins[p['name']]
    clean = subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=no'], cwd=p['path'], text=True)
    assert not clean, p['name']
    observed_packages[p['name']] = actual
assert (S / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.33.1'

receipts = {}
receipt_hashes = {}
for run, rec in audit['lossless_original_receipts'].items():
    p = E / rec['file']
    check(p, rec['gzip_sha256'])
    raw = gzip.decompress(p.read_bytes())
    assert digest(raw) == rec['original_sha256']
    check(L / 'runs' / run / 'RECEIPT.json', digest(raw))
    receipts[run] = json.loads(raw)
    receipt_hashes[run] = digest(raw)
    rr = receipts[run]
    assert rr['compiler_sha256'] == env['compiler_sha256']
    assert rr['platform'] == 'darwin' and rr['threads'] == 1 and rr['memory_cap_mib'] == 4096
    assert rr['max_compiler_processes'] == 1 and 'end' in rr
    assert len({c['module'] for c in rr['commands']}) == len(rr['commands'])
aggregate = receipts['recovery-118']
assert receipt_hashes['recovery-118'] == audit['aggregate_receipt_sha256']
check(L / 'ASSEMBLY-recovery-118.json', aggregate['assembly_sha256'])
assert aggregate['completed_modules'] == 55 and aggregate['failed_modules'] == aggregate['blocked_modules'] == []

module_records = {x['module']: x for x in audit['module_records']}
assert set(module_records) == set(proof)
authenticated = {}
fresh_intervals = []
reuse_edges = 0
def source_hash(rr, rel):
    h = rr['source_inputs'][rel]
    return h['sha256'] if isinstance(h, dict) else h
for mod, rel in proof.items():
    check(L / rel, snap['files'][rel])
    wanted = snap['files'][rel]
    claimed = module_records[mod]
    assert claimed['source_sha256'] == wanted and claimed['source'] == rel
    output = L / '.lake/build/lib/lean' / (rel[:-5] + '.olean')
    check(output, claimed['output_sha256'])
    run, chain, seen = 'recovery-118', [], set()
    while True:
        assert run not in seen
        seen.add(run)
        rr = receipts[run]
        for dep in closure(mod):
            assert source_hash(rr, proof[dep]) == snap['files'][proof[dep]], (run, mod, dep)
        cc = next(x for x in rr['commands'] if x['module'] == mod)
        assert cc['source_sha256'] == wanted and cc['output_sha256'] == claimed['output_sha256']
        if cc.get('status') == 'reused_exact_successful_local_output':
            prior = Path(cc['prior_receipt']).parent.name
            assert receipt_hashes[prior] == cc['prior_receipt_sha256']
            expected_closure = {proof[d]: snap['files'][proof[d]] for d in closure(mod)}
            assert cc['transitive_source_hashes'] == expected_closure
            chain.append({'run': run, 'prior': prior, 'prior_receipt_sha256': receipt_hashes[prior]})
            reuse_edges += 1
            run = prior
            continue
        assert cc['exit_code'] == 0
        assert cc['argv'] == [env['compiler'], '--threads=1', '--memory=4096', '-o', str(output), rel]
        assert cc['cwd'] == str(L)
        assert cc['dependency_olean_sha256'] == {d: module_records[d]['output_sha256'] for d in imports[mod]}
        check(E / claimed['log'], cc['log_sha256'])
        check(L / 'runs' / run / (mod + '.log'), cc['log_sha256'])
        log = (E / claimed['log']).read_text()
        assert not re.search(r'\b(error|sorryAx)\b', log)
        assert claimed['fresh_success_run'] == run and claimed['actual_fresh_command'] == cc
        assert claimed['reuse_chain'] == chain
        start, end = map(datetime.datetime.fromisoformat, [cc['start'], cc['end']])
        assert start < end and cc['elapsed_seconds'] > 0
        fresh_intervals.append((start, end, mod))
        authenticated[mod] = {'source_sha256': wanted, 'output_sha256': sha(output), 'fresh_run': run,
                              'log_sha256': cc['log_sha256'], 'reuse_hops': len(chain), 'command': cc['argv']}
        break
for a, b in zip(sorted(fresh_intervals), sorted(fresh_intervals)[1:]):
    assert a[1] <= b[0], ('overlapping reviewed compiles', a, b)

solution_log = (E / 'logs/recovery-118/Solution.log').read_text()
axioms = {m.group(1): [x.strip() for x in m.group(2).split(',')]
          for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", solution_log)}
assert set(axioms) == set(names) and all(set(a) == allowed for a in axioms.values())
assert axioms == json.loads((E / 'actual-axioms.json').read_text())
assert re.findall(r'^#assert_trust kernel (.+)$', (S / 'Solution.lean').read_text(), re.M) == names

type_audit = json.loads((T / 'AUDIT.json').read_text())
assert type_audit['receipt_sha256'] == receipt_hashes['recovery-118']
logs = [(T / (name + '.log')).read_bytes() for name in ['MI27SolutionTypes118', 'MI27ChallengeTypes118']]
assert logs[0] == logs[1] and digest(logs[0]) == type_audit['log_sha256']
rawtypes = logs[0].decode()
assert re.findall(r'^TYPEJSON (\S+) ', rawtypes, re.M) == names
assert re.findall(r'^LEVELJSON (\S+) ', rawtypes, re.M) == names
for mod, imported in [('MI27SolutionTypes118', 'Solution'), ('MI27ChallengeTypes118', 'Challenge')]:
    text = (T / (mod + '.lean')).read_text()
    assert text.startswith('import ' + imported + '\nimport Lean\n')
    assert len(re.findall(r'let info ← getConstInfo', text)) == 20
    assert re.findall(r'let info ← getConstInfo `(\S+)', text) == names
    assert 'reprStr info.type' in text and 'reprStr info.levelParams' in text
    cc = next(x for x in aggregate['commands'] if x['module'] == mod)
    assert cc['exit_code'] == 0 and cc['source_sha256'] == sha(T / (mod + '.lean'))
    check(L / (mod + '.lean'), cc['source_sha256'])
    check(L / 'runs/recovery-118' / (mod + '.log'), cc['log_sha256'])
    check(T / (mod + '.log'), cc['log_sha256'])
    imported_cmd = next(x for x in aggregate['commands'] if x['module'] == imported)
    assert cc['dependency_olean_sha256'] == {imported: imported_cmd['output_sha256']}
    check(L / '.lake/build/lib/lean' / (mod + '.olean'), cc['output_sha256'])
    assert cc['argv'][1:3] == ['--threads=1', '--memory=4096']
challenge_cmd = next(x for x in aggregate['commands'] if x['module'] == 'Challenge')
assert challenge_cmd['exit_code'] == 0 and challenge_cmd['source_sha256'] == sha(S / 'Challenge.lean')
assert challenge_cmd['dependency_olean_sha256'] == {'NLA.MI27.Definitions': module_records['NLA.MI27.Definitions']['output_sha256']}
check(L / 'Challenge.lean', challenge_cmd['source_sha256'])
check(L / 'runs/recovery-118/Challenge.log', challenge_cmd['log_sha256'])
check(L / '.lake/build/lib/lean/Challenge.olean', challenge_cmd['output_sha256'])
assert type_audit['fresh_commands'] == [c for c in aggregate['commands'] if c.get('exit_code') == 0]

result = {'verdict': 'PASS_READ_ONLY_AUTHENTICATION', 'time': datetime.datetime.now(datetime.timezone.utc).isoformat(),
          'scope': 'Source/evidence hashes and recorded local execution provenance; no compiler, Comparator or Linux execution by reviewer',
          'snapshot_sha256': sha(S / 'REVIEW-SNAPSHOT.json'), 'snapshot_files_authenticated': len(snap['files']),
          'proof_modules_authenticated': len(proof), 'previously_read_dependency_sources_unchanged': 51,
          'isolated_reference_and_diagnostic_modules': 3, 'receipt_count': len(receipts), 'reuse_edges': reuse_edges,
          'local_environment_sha256': sha(E / 'LOCAL-ENVIRONMENT.json'), 'compiler_sha256': sha(env['compiler']),
          'runner_sha256': sha(E / 'serial_compile_recovery.py'), 'observed_package_pins': observed_packages,
          'all20_source_headers_match': True, 'all20_standard_axiom_reports_match': True,
          'raw_type_and_universe_logs_byteidentical': True, 'raw_type_log_bytes': len(logs[0]),
          'raw_type_log_sha256': digest(logs[0]), 'solution_aggregate_seconds': audit['aggregate_command']['elapsed_seconds'],
          'GitHub_Comparator': 'NOT_RUN', 'standalone_lake_build': 'NOT_RUN',
          'packaging_note': 'Snapshot lake-manifest top-level name is NLANR04 while lakefile names NLAMI27; root will correct only publication metadata, no pin or proof change.',
          'contracts': headers, 'authenticated_modules': authenticated, 'receipt_hashes': receipt_hashes}
(R / 'SOURCE-AND-LOCAL-AUDIT.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['contracts','authenticated_modules','receipt_hashes','observed_package_pins']}, indent=2))
