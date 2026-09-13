"""Package unchanged, independently approved MI-03 proof for its Linux gate."""
from pathlib import Path
import datetime, hashlib, json, re, subprocess
import yaml

repo = Path('/tmp/nla-lean-mi03-worktree')
project = repo / 'matrix-inequalities-and-norms/MI-03/lean'
drafts = Path('/tmp/nla-lean-formalization/mi03-candidate-drafts')
out = project / 'verification/candidate-2026-09-12'
base = 'c0601d8825e9f9e744212c62e6a43fefc1c60a22'
sha = lambda data: hashlib.sha256(data).hexdigest()
def digest(path):
    data = path.read_bytes()
    return {'sha256': sha(data), 'bytes': len(data)}
def git(*args):
    return subprocess.check_output(['git', *args], cwd=repo)
def check(path, expected):
    assert sha(path.read_bytes()) == expected, str(path)

assert git('rev-parse', 'HEAD').decode().strip() == base
assert not git('status', '--porcelain', '--untracked-files=no')
freeze_path = project / 'reviews/proof-freeze.json'
check(freeze_path, 'fcff9e256a6425853b15def24260b419613a72d9122c0a5bedea4b4cd5f0fd1d')
freeze = json.loads(freeze_path.read_text())
assert len(freeze['files']) == 101 and len(freeze['source_files']) == 8
archive = out / 'README.statement.md'
for rel, value in freeze['files'].items():
    path = archive if rel == 'README.md' and archive.exists() else project / rel
    check(path, value['sha256'])
for rel, expected in freeze['source_files'].items():
    check(repo / rel, expected)
    assert (repo / rel).read_bytes() == git('show', base + ':' + rel)
reports = {
    'statement-referee-1.md': '2a46c81ee78c4d0718c862cecf76a20425447c3ba502a78a477caf8a30e20de2',
    'statement-referee-2.md': '47c4a7ada59afabcbf5657da3cdc31598db49c88e2beed7b7b50f5b0dde09ce0',
    'proof-referee-1.md': '7a00100cd2070c759b0dc71c743f9d58428c2ae5bfe41ffda4696efd4003391f',
    'proof-referee-2.md': '129c3b352346d1da8a192a0f4d662eb0a6e9b9f5a7a02b7efc176f2a7a051ba3',
}
for rel, expected in reports.items():
    check(project / 'reviews' / rel, expected)
referee_evidence = {}
for number, expected in [(1, '3e3b31ec7ed0fdc50b06305a215d568e38849a2d437ae4cfc06e9ba3651f18eb'), (2, '7422f5c308563fd2e343a107f1aaf4c7dc060c09b4f03638f2e59fd4a9c99ea0')]:
    path = project / f'reviews/proof-referee-{number}-evidence/EVIDENCE-MANIFEST.json'
    check(path, expected)
    manifest = json.loads(path.read_text())
    for rel, value in manifest['files'].items():
        check(path.parent / rel, value['sha256'])
    if 'review_report' in manifest:
        value = manifest['review_report']
        check(path.parent / value['path'], value['sha256'])
    referee_evidence[str(path.relative_to(project))] = digest(path)

out.mkdir(parents=True, exist_ok=True)
if not archive.exists():
    archive.write_bytes((project / 'README.md').read_bytes())
check(archive, freeze['files']['README.md']['sha256'])
(project / 'README.md').write_bytes((drafts / 'README.md').read_bytes())
metadata = json.loads((drafts / 'metadata.json').read_text())
metadata['review']['statement_reports'] = [{'file': 'reviews/' + rel, 'sha256': value} for rel, value in reports.items() if rel.startswith('statement-')]
metadata['review']['proof_reports'] = [{'file': 'reviews/' + rel, 'sha256': value} for rel, value in reports.items() if rel.startswith('proof-')]
metadata['review']['proof_report_evidence'] = referee_evidence
metadata['acknowledgements'] = metadata['acknowledgements'].replace('/root/cardinality', '/root/infimum')
(project / 'formalization.yaml').write_text('# yaml-language-server: $schema=../../../docs/lean/schema/v0.4.schema.json\n' + yaml.safe_dump(metadata, sort_keys=False, allow_unicode=True, width=105))
(out / 'prepare_candidate.py').write_bytes(Path(__file__).read_bytes())

commands = [
    ['/tmp/nla-lean-formalization/venv/bin/python', 'tools/lean/validate_manifest.py', str(project.relative_to(repo))],
    ['python3', 'tools/validate_problem_ids.py', '--base-ref', 'origin/main'],
    ['python3', 'tools/validate_problem_ids.py', '--base-ref', base],
    ['python3', 'tools/update_catalog.py', '--base-ref', 'origin/main'],
    ['python3', '-m', 'unittest', 'discover', '-s', 'tests', '-p', 'test_problem_ids.py', '-v'],
]
checks = []
for i, command in enumerate(commands):
    result = subprocess.run(command, cwd=repo, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log = out / f'check-{i}.log'
    log.write_bytes(result.stdout)
    checks.append({'command': command, 'returncode': result.returncode, 'log': log.name, **digest(log)})
    assert result.returncode == 0, result.stdout.decode()
assert not git('status', '--porcelain', '--untracked-files=no'), 'Unexpected tracked-file change'
config = json.loads((project / 'comparator.json').read_text())
names = re.findall(r'^theorem\s+(\w+)', (project / 'Challenge.lean').read_text(), re.M)
assert len(names) == 8 and config['theorem_names'] == ['NLA.MI03.' + n for n in names]
assert config['definition_names'] == [] and set(config['permitted_axioms']) == {'propext', 'Classical.choice', 'Quot.sound'}
assert '**Status:** Solved' in (project.parent / 'README.md').read_text()
for rel, value in freeze['files'].items():
    check(archive if rel == 'README.md' else project / rel, value['sha256'])
for rel in ['README.md', 'formalization.yaml']:
    text = (project / rel).read_text()
    flat = ' '.join(text.split())
    assert all(x in flat for x in ['George Stepaniants', 'Department of Computing and Mathematical Sciences', 'California Institute of Technology'])
    assert not re.search(r'[\w.%+\-]+@[\w.\-]+\.[A-Za-z]{2,}', text)
integrity = {
    'status': 'PASS; locally approved proof packaged for actual Linux verification',
    'date_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'base': base, 'proof_freeze': digest(freeze_path),
    'frozen_project_inputs': 101, 'unchanged_nonREADME_inputs': 100,
    'unchanged_original_sources_compared_with_Git': 8,
    'historical_README_archive': str(archive.relative_to(project)),
    'independent_reports': reports, 'proof_referee_evidence': referee_evidence,
    'complete_target': 'Every odd k>=3; stronger IsLeast k/4 for every k>=2, all positive dimensions and all complex contractions with genuine norms and CFC moduli.',
    'exports': config['theorem_names'], 'commands': checks,
    'LeanCert_role': 'Explicit kernel trust auditing of a pure exact proof; no interval certificate.',
    'local_checks': 'Two independent final referees freshly elaborated the unchanged proof with old project objects excluded and actual transitive mathematical dependencies audited.',
    'Linux_status': 'Pending. No MI-03 Linux Comparator, default-kernel replay or operational review is claimed.',
    'canonical_status': 'Solved',
}
(out / 'integrity.json').write_text(json.dumps(integrity, indent=2) + '\n')
handoff = '''# MI-03 Linux candidate packaging

The complete mathematical implementation has two independent final approvals after two independent statement approvals. Root authored the implementation and is **not** either referee. Both full reports and their retained artifacts were read and rehashed before this packaging.

The current guide now accurately describes the completed local proof and the pending Linux gate, closing both referees' historical-README finding. The exact original guide is preserved at `README.statement.md`. All other 100 of 101 proof-freeze inputs and all eight original source files remain unchanged; original sources also match their recorded Git blobs. No Lean statement, proof, configuration, pin or canonical page was edited. Frozen numerical-target and source-map language is expressly identified as historical.

The actual v0.4 schema and all eight Comparator exports validate. Permanent IDs validate against both origin/main and the original published base; index generation makes no tracked changes; all 17 ID tests pass. Formalization credits George Stepaniants and the approved Caltech department affiliation without an email. Colbrook retains mathematical authorship, and Bourin–Lee retain conjecture/prior-bound attribution.

LeanCert supplies explicit kernel trust auditing of the pure exact proof. No interval certificate or Linux execution is claimed. The full original odd-k conjecture follows from the stronger least admissible constant k/4 for every k≥2. Actual Linux sandboxed Comparator/default-kernel checks, controls, independent operational audit and publication review remain required. The canonical status is still Solved.

`integrity.json` retains exact commands, source counts and review identities. `EVIDENCE-MANIFEST.json` binds this handoff, the archived guide, the packaging script, all check logs, and both current metadata files.
'''
(out / 'HANDOFF.md').write_text(handoff)
manifest = {'scope': 'MI-03 candidate packaging only; actual Linux pending', 'files': {}, 'metadata': {}}
for path in sorted(out.iterdir()):
    if path.is_file() and path.name != 'EVIDENCE-MANIFEST.json':
        manifest['files'][path.name] = digest(path)
for rel in ['README.md', 'formalization.yaml']:
    manifest['metadata'][rel] = digest(project / rel)
(out / 'EVIDENCE-MANIFEST.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(json.dumps({'status': 'PACKAGED', 'manifest': digest(out / 'EVIDENCE-MANIFEST.json'), 'metadata': manifest['metadata'], 'files': len(manifest['files']), 'handoff': digest(out / 'HANDOFF.md')}, indent=2))
