#!/usr/bin/env python3
"""Serial local compiler with source-bound incremental reuse. Development only."""
from pathlib import Path
import datetime, fcntl, hashlib, json, os, resource, subprocess, sys, time

ROOT = Path(__file__).resolve().parent
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
now = lambda: datetime.datetime.now(datetime.timezone.utc).isoformat()
assembly_path = ROOT / sys.argv[1]
assembly = json.loads(assembly_path.read_text())
environment = json.loads((ROOT / 'LOCAL-ENVIRONMENT.json').read_text())
sources = assembly['sources']
modules = {p[:-5].replace('/', '.'): p for p in sources}
imports = {}
for mod, rel in modules.items():
    assert sha(ROOT / rel) == sources[rel]['sha256'], rel
    imports[mod] = [d for line in (ROOT / rel).read_text().splitlines()
                    if line.startswith('import ') for d in line[7:].split() if d.startswith('NLA.')]
    assert all(d in modules for d in imports[mod]), mod
ordered, visiting, closures = [], set(), {}
def visit(mod):
    if mod in closures:
        return closures[mod]
    assert mod not in visiting, ('cycle', mod)
    visiting.add(mod)
    deps = {mod}
    for dep in imports[mod]:
        deps.update(visit(dep))
    visiting.remove(mod)
    closures[mod] = deps
    ordered.append(mod)
    return deps
for mod in sys.argv[3:]:
    assert mod in modules, mod
    visit(mod)
registry = []
for f in sorted((ROOT / 'runs').glob('recovery-*/RECEIPT.json')):
    j = json.loads(f.read_text())
    assert 'end' in j, ('prior run still active', f)
    for c in j['commands']:
        if c.get('exit_code') == 0 or c.get('status') == 'reused_exact_successful_local_output':
            registry.append((f, sha(f), j, c))
run = ROOT / 'runs' / sys.argv[2]
run.mkdir(parents=True, exist_ok=False)
lock = (ROOT / '.compiler.lock').open('w')
fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
env = os.environ.copy()
env['LEAN_PATH'] = environment['lean_path']
env['LEAN_NUM_THREADS'] = '1'
receipt = {'scope': 'macOS serial recovery development only; fresh project outputs or exact source-matched successes from this recovery; no Comparator, isolation controls, publication or whole-problem acceptance',
           'start': now(), 'assembly_sha256': sha(assembly_path), 'runner_sha256': sha(__file__),
           'compiler_sha256': sha(environment['compiler']), 'platform': sys.platform,
           'max_compiler_processes': 1, 'threads': 1, 'memory_cap_mib': 4096,
           'source_inputs': {p: v['sha256'] for p, v in sources.items()},
           'module_order': ordered, 'commands': [], 'count_change': 0}
def save():
    (run / 'RECEIPT.json').write_text(json.dumps(receipt, indent=2) + '\n')
save()
results = {}
for mod in ordered:
    rel = modules[mod]
    failed = [d for d in imports[mod] if results[d] != 0]
    if failed:
        results[mod] = 'blocked'
        receipt['commands'].append({'module': mod, 'status': 'not_run', 'failed_dependencies': failed})
        save()
        continue
    output = ROOT / '.lake/build/lib/lean' / (rel[:-5] + '.olean')
    output.parent.mkdir(parents=True, exist_ok=True)
    if output.exists():
        matches = []
        for prior_path, prior_sha, prior, command in registry:
            if command['module'] != mod or command.get('source_sha256') != sources[rel]['sha256'] or command.get('output_sha256') != sha(output):
                continue
            def prior_matches(d):
                value = prior['source_inputs'].get(modules[d])
                return (value.get('sha256') if isinstance(value, dict) else value) == sources[modules[d]]['sha256']
            if all(prior_matches(d) for d in closures[mod]):
                matches.append((prior_path, prior_sha, command))
        assert matches, ('unbound existing module output; do not silently reuse', mod)
        prior_path, prior_sha, command = matches[-1]
        results[mod] = 0
        receipt['commands'].append({'module': mod, 'status': 'reused_exact_successful_local_output',
          'source_sha256': sources[rel]['sha256'], 'output_sha256': sha(output),
          'prior_receipt': str(prior_path), 'prior_receipt_sha256': prior_sha,
          'transitive_source_hashes': {modules[d]: sources[modules[d]]['sha256'] for d in sorted(closures[mod])}})
        save()
        print('REUSE', mod, flush=True)
        continue
    argv = [environment['compiler'], '--threads=1', '--memory=4096', '-o', str(output), rel]
    log = run / (mod + '.log')
    command = {'module': mod, 'argv': argv, 'cwd': str(ROOT), 'start': now(),
               'source_sha256': sha(ROOT / rel), 'dependency_olean_sha256':
               {d: sha(ROOT / '.lake/build/lib/lean' / (modules[d][:-5] + '.olean')) for d in imports[mod]}}
    print('START', mod, flush=True)
    start = time.monotonic()
    with log.open('w') as stream:
        try:
            child = subprocess.run(argv, cwd=ROOT, env=env, stdout=stream, stderr=subprocess.STDOUT, timeout=180)
            code = child.returncode
        except subprocess.TimeoutExpired:
            code = 'timeout_180_seconds'
    results[mod] = code
    command.update(exit_code=code, end=now(), elapsed_seconds=time.monotonic()-start,
      log_sha256=sha(log), maxrss_bytes_macos_cumulative=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
      output_sha256=sha(output) if output.exists() else None)
    assert all(sha(ROOT / p) == v['sha256'] for p, v in sources.items()), 'source mutation during compilation'
    receipt['commands'].append(command)
    save()
    print('END', mod, code, round(command['elapsed_seconds'], 2), flush=True)
    if code != 0:
        print(log.read_text(), flush=True)
receipt.update(end=now(), completed_modules=sum(v == 0 for v in results.values()),
               failed_modules=[m for m,v in results.items() if v not in (0,'blocked')],
               blocked_modules=[m for m,v in results.items() if v == 'blocked'])
save()
print(json.dumps({k: receipt[k] for k in ['completed_modules','failed_modules','blocked_modules']}), flush=True)
