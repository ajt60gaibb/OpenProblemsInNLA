from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re, subprocess, sys
import yaml

SETTINGS = {
    'MF-16': dict(root='/tmp/nla-lean-mf16-worktree', prefix='matrix-functions-and-stability/MF-16/lean/',
        readme='c918adbb893f7afac530fa1b9582416fa7e26f1e51f12761c63bc318ca303d69',
        metadata='8ad758f3b8e78c5fccebb5fad1e606cf8da9fb0641924a4eafe5f2406001c3d2',
        handoff='eba4f1bfb8c7a45575e832f2ae88499d18371e3b85a16ea14cbdd7dbb68c1e9a',
        integrity='24e644975c8e1f1f39871f9c34937c7f543eb865ffff991a0ab3301bd4a27f72',
        outer='5ce1d3313888dd2f8b95a9e23513e754841880725b017102b88aa92ce3494393',
        gate='94a681f53089ea8b45e9fc8e1760d015d00cfcd18af145a61c87c021aa021753',
        proof='f4b21be066d0e55e56aae5b3fd1119433ef09d7ed5822d57dacab906b38ac720',
        statements='eaba8311f143727f2061f2b4c945e403e62b7e9041712d983ef56ccf2e7f0587',
        count=290, nested=5, proof_count=182, statement_count=45, originals=14, exports=9,
        baseline_key='reviewer_entry_inputs', baseline_count=271,
        baseline_map={'formalization.yaml': 'verification/linux-candidate-2026-09-12/formalization.initial.yaml'},
        frozen_map={'README.md': 'verification/pre-candidate-README.md'},
        role='Disclosed mathematical route contributor and original wrapper preparer; independent packaging audit supplied by mf16_final_referee. Coordinator acceptance is not another independent mathematical or packaging approval.',
        scope='Complete original ordinary palindrome/all-complex-Hermitian-positive-definite order-two word-uniqueness assertion negated. Material actual kernel Krawczyk box certificate, actual matrix characteristic-polynomial reduction, all-entry complex word recovery, positivity and distinctness.'),
    'RA-08': dict(root='/tmp/nla-lean-ra08-worktree', prefix='randomized-and-low-rank-approximation/RA-08/lean/',
        readme='dbb7e67327c6da9f31a5bdfd21cac6f029c4e565ce2336735997487cc8f876df',
        metadata='8730f7f9e2a70483d31e7046de87a71fb7085401127093dee12dab0317109478',
        handoff='9a4615d9283d5a4098f0e9ceff098c474fcc36a015df568955c3ebbf523a3593',
        integrity='c22667c2bbc9510ad109c34727bec33b2968df23cb507889bccb1b943f16a315',
        outer='bf9faf859b4184c4b27717e4eda8b482f272105eca0f693adf6a9643d91a6e4a',
        gate='ab7c97b219b098a9d6e1f72cad49e21d68a1ac37cd73f600d971aca5977de84d',
        proof='ab05e2bf801e6906453e88a4d84d5e73191f776db05610fb8b8e5e4a03d4f856',
        statements='eb0460c3dd4c13a42f928e3f00c9c3710e486922b99aff74f4d6a3098c5ed332',
        count=609, nested=6, proof_count=450, statement_count=39, originals=10, exports=14,
        baseline_key='original_project_inputs', baseline_count=586,
        baseline_map={'README.md': 'verification/pre-candidate-README.md', 'formalization.yaml': 'verification/pre-candidate-formalization.yaml'},
        frozen_map={'README.md': 'verification/pre-candidate-README.md', 'formalization.yaml': 'verification/pre-candidate-formalization.yaml'},
        role='Disclosed mathematical spectral-helper coauthor; independent of candidate documentation preparer leancert_examples. This is independent packaging review, not an independent mathematical approval.',
        scope='Complete original all-real-PSD/all-function/all-parameter/all-eigenbasis spectral transfer assertion negated. Genuine CFC and Euclidean norm, exact spectral/tail proofs, and a materially consumed kernel strict-upper-bound certificate for zero on [0,0] against the exact positive rational gap.'),
}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


problem = sys.argv[1]
c = SETTINGS[problem]
repo = Path(c['root'])
project = repo / c['prefix']
pack = project / 'verification/linux-candidate-2026-09-12'
out = project / 'verification/root-candidate-2026-09-12'
assert not out.exists()
git = lambda *args: subprocess.check_output(['git', *args], cwd=repo)
expected = {'README.md': c['readme'], 'formalization.yaml': c['metadata'],
    'verification/final-review-acceptance.json': c['gate'],
    'verification/proof-freeze.json': c['proof'], 'reviews/statement-freeze.json': c['statements'],
    'verification/linux-candidate-2026-09-12/CANDIDATE-HANDOFF.md': c['handoff'],
    'verification/linux-candidate-2026-09-12/integrity.json': c['integrity'],
    'verification/linux-candidate-2026-09-12/EVIDENCE-MANIFEST.json': c['outer']}
for rel, h in expected.items():
    assert sha(project / rel) == h, rel
outer = pack / 'EVIDENCE-MANIFEST.json'
manifest = json.loads(outer.read_text())
assert len(manifest['files']) == c['count'] - 1
bound = {}
for rel, item in manifest['files'].items():
    path = pack / rel
    assert path.resolve().is_relative_to(project.resolve()) and path.resolve() != outer.resolve()
    assert not path.is_symlink()
    assert sha(path) == item['sha256'] and path.stat().st_size == item['bytes'], rel
    canonical = path.resolve().relative_to(project.resolve()).as_posix()
    assert canonical not in bound
    bound[canonical] = item['sha256']
bound[outer.relative_to(project).as_posix()] = sha(outer)
actual = {r.removeprefix(c['prefix']) for r in git('ls-files', '--others', '--exclude-standard', '--', c['prefix']).decode().splitlines()}
assert actual == set(bound) and len(actual) == c['count']
baseline = json.loads((pack / 'baseline.json').read_text())[c['baseline_key']]
assert len(baseline) == c['baseline_count']
for rel, item in baseline.items():
    path = project / c['baseline_map'].get(rel, rel)
    assert sha(path) == item['sha256'] and path.stat().st_size == item['bytes'], rel
for rel, count in [('verification/proof-freeze.json', c['proof_count']), ('reviews/statement-freeze.json', c['statement_count'])]:
    f = json.loads((project / rel).read_text())
    assert len(f['files']) == count and len(f['source_files']) == c['originals']
    for source, h in f['files'].items():
        assert sha(project / c['frozen_map'].get(source, source)) == h, source
    for source, h in f['source_files'].items():
        assert sha(repo / source) == h and hashlib.sha256(git('show', f['base'] + ':' + source)).hexdigest() == h, source
nested = [rel for rel in bound if rel.endswith('/EVIDENCE-MANIFEST.json') and rel != outer.relative_to(project).as_posix()]
assert len(nested) == c['nested']
inventories = {}
for rel in nested:
    path = project / rel
    m = json.loads(path.read_text())
    for source, item in m['files'].items():
        q = path.parent / source
        assert q.resolve() != path.resolve() and not q.is_symlink()
        assert sha(q) == item['sha256'] and q.stat().st_size == item['bytes'], (rel, source)
    internal = {source for source in m['files'] if not source.startswith('../')}
    assert internal == {q.relative_to(path.parent).as_posix() for q in path.parent.rglob('*') if q.is_file() and q != path}
    inventories[rel] = dict(sha256=sha(path), bound_files=len(m['files']), complete=True)
meta = yaml.safe_load((project / 'formalization.yaml').read_text())
config = json.loads((project / 'comparator.json').read_text())
names = config['theorem_names']
assert len(names) == c['exports'] and not config.get('definition_names', [])
assert [x['declaration'] for x in meta['status']['main_results']] == names
assert [x['declaration'] for x in meta['alignment']] == names
assert meta['version'] == 'v0.4' and meta['status']['sorry_count'] == meta['status']['sorry_in_definitions'] == 0
assert meta['status']['axioms'] == ['propext', 'Classical.choice', 'Quot.sound']
assert meta['review']['linux_verification']['status'] == 'pending'
for group in ['statement_reports', 'proof_reports']:
    assert len(meta['review'][group]) == 2
    for report in meta['review'][group]:
        assert sha(project / report['file']) == report['sha256']
for group in ['statement_report_evidence', 'proof_report_evidence']:
    for rel, item in meta['review'].get(group, {}).items():
        assert sha(project / rel) == item['sha256'] and (project / rel).stat().st_size == item['bytes']
for key in ['statement_freeze', 'proof_freeze', 'coordinator_acceptance', 'historical_readme', 'historical_formalization']:
    if key in meta['review']:
        item = meta['review'][key]
        assert sha(project / item['file']) == item['sha256']
assert meta['project']['authors'] == ['George Stepaniants']
assert meta['project']['affiliations']['George Stepaniants'] == 'Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA'
assert any(s.get('authors') == ['Matthew J. Colbrook'] for s in meta['sources'])
for rel in ['README.md', 'formalization.yaml']:
    assert not re.search(r'[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}', (project / rel).read_text())
for link in re.findall(r'\]\(([^)]+)\)', (project / 'README.md').read_text()):
    if not re.match(r'[a-z]+:', link):
        assert (project / link.split('#')[0]).exists(), link
assert git('rev-parse', 'HEAD').decode().strip() == '5830ed4fb06da0659414a3deb2a40ad327aca052'
assert not git('diff', '--name-only') and not git('diff', '--cached', '--name-only')
assert '**Status:** Solved' in (project.parent / 'README.md').read_text()
assert len(json.loads((repo / 'problem_ids.json').read_text())) == 217
assert (repo / 'problem_ids.json').read_bytes() == git('show', 'HEAD:problem_ids.json')
out.mkdir()
schema_cmd = ['/tmp/nla-lean-formalization/venv/bin/python', 'tools/lean/validate_manifest.py', c['prefix'].rstrip('/')]
schema = subprocess.run(schema_cmd, cwd=repo, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
(out / 'schema.log').write_bytes(schema.stdout)
assert schema.returncode == 0, schema.stdout.decode()
record = dict(status='ACCEPT exact reviewed Linux candidate for blank-email commit and authorized fork push; actual Linux still pending',
    utc=datetime.now(timezone.utc).isoformat(), problem=problem, coordinator='/root', coordinator_role=c['role'],
    full_reads='Current complete README, v0.4 metadata, packaging handoff and both complete final mathematical reports read. Frozen complete-target/source correspondence was reviewed in prior recorded phases. Every current candidate byte and nested evidence inventory independently rehashed.',
    exact_metadata_and_gate_sha256=expected, preparer_input_count=c['count'], preparer_all_input_sha256=bound,
    prepackaging_inputs_verified=c['baseline_count'], baseline_archive_mapping=c['baseline_map'],
    proof_inputs_preserved=c['proof_count'], statement_inputs_preserved=c['statement_count'], frozen_archive_mapping=c['frozen_map'],
    original_Git_source_files_preserved=c['originals'], complete_nested_inventories=inventories,
    exact_exports=names, actual_schema_command=schema_cmd, schema_exit_code=0, scope=c['scope'],
    canonical_status='Solved, unchanged', all_217_original_ID_paths_preserved=True,
    new_proof_or_dependency_computation=False, actual_Linux_Comparator_controls_replay='pending',
    next_gates='Immutable candidate/fork push; actual Ubuntu default-kernel/Comparator/real controls; independent operational review; publication/PDF/catalog/ID checks and separate upstream PR',
    inventory_note='This acceptance adds its own separate directory without rewriting the preparer full-project frozen phase inventory. Only the exact root outer manifest is excluded from its own evidence inventory.')
(out / 'ROOT-CHECKS.json').write_text(json.dumps(record, indent=2) + '\n')
(out / 'review_candidate.py').write_bytes(Path(__file__).read_bytes())
root_manifest = out / 'EVIDENCE-MANIFEST.json'
files = {q.relative_to(out).as_posix(): dict(sha256=sha(q), bytes=q.stat().st_size) for q in out.rglob('*') if q.is_file() and q != root_manifest}
root_manifest.write_text(json.dumps(dict(file_count=len(files), files=files, inventory_rule='Every internal file except only this exact outer manifest; nested manifests included'), indent=2) + '\n')
receipt = dict(problem=problem, status=record['status'], root_checks_sha256=sha(out / 'ROOT-CHECKS.json'), root_evidence_manifest_sha256=sha(root_manifest), total_candidate_inputs=c['count'] + len(files) + 1)
Path('/tmp/nla-lean-formalization/' + problem + '-root-candidate-review.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt, indent=2))
