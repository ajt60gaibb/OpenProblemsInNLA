"""Independent statement referee 2: fresh local source, no target proof."""
from pathlib import Path
import datetime, hashlib, json, os, platform, re, subprocess, tempfile, time

out = Path(__file__).resolve().parent
project = out.parents[1]
repo = project.parents[2]
cache = Path('/tmp/nla-lean-mi22-worktree/matrix-inequalities-and-norms/MI-22/lean')
toolchain = Path('/Users/georgestepaniants/.elan/toolchains/leanprover--lean4---v4.33.1')
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
git = lambda path, *a: subprocess.check_output(['git', '-C', str(path), *a])
write = lambda name, data: (out / name).write_text(json.dumps(data, indent=2) + '\n')
freeze_path = project / 'reviews/statement-freeze.json'
assert sha(freeze_path) == '8c940e34c5d97c8b00d5560fe881416b7e5bbc563a005ed214db9bd54ad71d6b'
freeze = json.loads(freeze_path.read_text())
assert len(freeze['files']) == 32 and len(freeze['source_files']) == 8
assert not (project / 'Solution.lean').exists() and not (project / 'NLA/IV06/Proof.lean').exists()
for rel, expected in freeze['files'].items():
    assert sha(project / rel) == expected, rel
for rel, expected in freeze['source_files'].items():
    assert sha(repo / rel) == expected, rel
    assert (repo / rel).read_bytes() == git(repo, 'show', freeze['base'] + ':' + rel)
write('integrity-before.json', freeze)

manifest = json.loads((project / 'lake-manifest.json').read_text())
pins = []
for p in manifest['packages']:
    d = cache / '.lake/packages' / p['name']
    actual = git(d, 'rev-parse', 'HEAD').decode().strip()
    status = git(d, 'status', '--porcelain=v1').decode()
    assert actual == p['rev'] and not status, (p['name'], actual, status)
    pins.append({'name': p['name'], 'revision': actual, 'path': str(d.resolve()), 'source_clean': True, 'dependency_object_directory_present': (d / '.lake/build/lib/lean').is_dir()})
assert len(pins) == 10
write('dependency-pins.json', pins)
prefix = Path(tempfile.mkdtemp(prefix='nla-iv06-independent-statements-ref2-', dir='/tmp'))
order = ['Cli','batteries','Qq','aesop','proofwidgets','importGraph','LeanSearchClient','plausible','mathlib','leancert']
paths = [prefix, *((cache / '.lake/packages' / name / '.lake/build/lib/lean').resolve() for name in order), toolchain / 'lib/lean']
assert all(p == prefix or '/.lake/packages/' in str(p) or p == toolchain / 'lib/lean' for p in paths)
env = os.environ.copy()
env['LEAN_PATH'] = ':'.join(map(str, paths))
lean = str(toolchain / 'bin/lean')
version = subprocess.check_output([lean, '--version'], text=True).strip()
assert '4.33.1' in version
write('environment.json', {'scope': 'Local macOS statement-only source elaboration; exact MI-22 dependency caches reused read-only; no Lake command, full dependency build or Linux Comparator', 'date_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'platform': platform.platform(), 'lean': lean, 'version': version, 'fresh_prefix': str(prefix), 'LEAN_PATH': env['LEAN_PATH'], 'excluded_project_object_directories': [str((project / '.lake/build/lib/lean').resolve()), str((cache / '.lake/build/lib/lean').resolve())]})
commands = []
for source in ['NLA/IV06/Definitions.lean', 'Challenge.lean', 'reviews/statement-referee-2-evidence/Inspect.lean']:
    target = prefix / (Path(source).with_suffix('.olean') if not source.startswith('reviews/') else Path('IndependentInspect.olean'))
    target.parent.mkdir(parents=True, exist_ok=True)
    cmd = [lean, '-o', str(target), source]
    start = time.monotonic()
    r = subprocess.run(cmd, cwd=project, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log = out / (Path(source).stem + '.log')
    log.write_bytes(r.stdout)
    commands.append({'source': source, 'command': cmd, 'exit_code': r.returncode, 'seconds': round(time.monotonic() - start, 3), 'source_sha256': sha(project / source), 'object_sha256': sha(target) if target.exists() else None, 'log_sha256': sha(log)})
    write('fresh-checks.json', commands)
    print(source, r.returncode, flush=True)
    assert r.returncode == 0, r.stdout.decode()
    text = r.stdout.decode()
    assert 'error:' not in text
    if source == 'Challenge.lean':
        assert text.count('declaration uses `sorry`') == 8 and text.count('warning:') == 8
    else:
        assert 'warning:' not in text
reports = re.findall(r"'([^'\n]+)' depends on axioms: \[([^\]]*)\]", (out / 'Inspect.log').read_text())
assert len(reports) == 5
for name, raw in reports[:3]:
    assert [s.strip() for s in raw.split(',')] == ['propext', 'Classical.choice', 'Quot.sound'], (name, raw)
for name, raw in reports[3:]:
    assert 'sorryAx' in raw, (name, raw)
write('axioms.json', {'definition_kernel_audits': 3, 'definition_axioms': reports[:3], 'intentional_challenge_sorry_observations': reports[3:]})
for rel, expected in freeze['files'].items():
    assert sha(project / rel) == expected, rel
for rel, expected in freeze['source_files'].items():
    assert sha(repo / rel) == expected, rel
write('fresh-result.json', {'result': 'PASS', 'commands': len(commands), 'eight_isolated_Challenge_holes': True, 'three_definition_kernel_checks': True, 'all_32_frozen_inputs_and_8_original_sources_unchanged': True, 'proof_exists': False})
print('PASS: three fresh commands; eight isolated placeholders; three kernel-audited definitions; no proof claim')
