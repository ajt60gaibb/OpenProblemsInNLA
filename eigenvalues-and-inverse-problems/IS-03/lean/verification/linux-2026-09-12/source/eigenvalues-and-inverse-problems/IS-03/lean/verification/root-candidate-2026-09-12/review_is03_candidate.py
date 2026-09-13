from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re,subprocess,yaml
repo=Path('/tmp/nla-lean-is03-worktree');project=repo/'eigenvalues-and-inverse-problems/IS-03/lean'
pack=project/'verification/linux-candidate-2026-09-12';out=project/'verification/root-candidate-2026-09-12'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();git=lambda *a:subprocess.check_output(['git',*a],cwd=repo)
assert not out.exists()
expected={'README.md':'c175a58f3ae272b8398e2c895381bae1848c0e41db2ef8fd8695f6a59a377302','formalization.yaml':'eacd7fcec2ffe63c109dd6ce48e7849146448175b2b574276ebe4bc34a90d8f5',
'verification/linux-candidate-2026-09-12/CANDIDATE-HANDOFF.md':'e85ff5200011caacd8d72b34639d4be47e5170ab8cc7db318ac377a0019fdace',
'verification/linux-candidate-2026-09-12/integrity.json':'3d4817a12b7352110407255516ac762d97b0b918bfffbbed6f5d5278ab8382e5',
'verification/linux-candidate-2026-09-12/EVIDENCE-MANIFEST.json':'2f80b30b36059c084494a125e844bbb2ec5a5d021801b51b8f36960deae5b6d0',
'verification/final-review-acceptance.json':'73b53a03c34cf25666338767107c48fce2ea320bc36206ea134dc2717342ab12'}
for r,h in expected.items():assert sha(project/r)==h,r
outer=pack/'EVIDENCE-MANIFEST.json';m=json.loads(outer.read_text());assert len(m['files'])==298
bound={}
for rel,v in m['files'].items():
    p=(pack/rel).resolve();assert p.is_relative_to(project.resolve()) and p!=outer.resolve() and not (pack/rel).is_symlink(),rel
    assert sha(p)==v['sha256'] and p.stat().st_size==v['bytes'],rel
    bound[p.relative_to(project.resolve()).as_posix()]=v['sha256']
prefix=project.relative_to(repo).as_posix()+'/'
actual={r.removeprefix(prefix) for r in git('ls-files','--others','--exclude-standard','--',prefix).decode().splitlines()}
assert actual==set(bound)|{outer.relative_to(project).as_posix()};assert len(actual)==299
nested=[r for r in bound if r.endswith('/EVIDENCE-MANIFEST.json')];assert len(nested)==4
baseline=json.loads((pack/'baseline.json').read_text());assert len(baseline['original_project_inputs'])==288
for r,v in baseline['original_project_inputs'].items():
    p=pack/'README.statement.md' if r=='README.md' else project/r
    assert sha(p)==v['sha256'] and p.stat().st_size==v['bytes'],r
for freeze_name,count in [('verification/proof-freeze.json',203),('reviews/statement-freeze.json',34)]:
    freeze=json.loads((project/freeze_name).read_text());assert len(freeze['files'])==count
    for r,h in freeze['files'].items():assert sha(pack/'README.statement.md' if r=='README.md' else project/r)==h,r
    assert len(freeze['source_files'])==10
    for r,h in freeze['source_files'].items():assert sha(repo/r)==h and hashlib.sha256(git('show',freeze['base']+':'+r)).hexdigest()==h,r
manifest=yaml.safe_load((project/'formalization.yaml').read_text());config=json.loads((project/'comparator.json').read_text())
assert manifest['version']=='v0.4'
names=config['theorem_names'];assert len(names)==7 and not config.get('definition_names',[])
assert [r['declaration'] for r in manifest['status']['main_results']]==names and [r['declaration'] for r in manifest['alignment']]==names
assert manifest['status']['sorry_count']==0 and manifest['status']['sorry_in_definitions']==0
assert manifest['status']['axioms']==['propext','Classical.choice','Quot.sound']
assert manifest['review']['linux_verification']['status']=='pending'
for group in ['statement_reports','proof_reports']:
    assert len(manifest['review'][group])==2
    for r in manifest['review'][group]:assert sha(project/r['file'])==r['sha256'],r
inventories={}
for group in ['statement_report_evidence','proof_report_evidence']:
    for rel,v in manifest['review'][group].items():
        p=project/rel;assert sha(p)==v['sha256'] and p.stat().st_size==v['bytes'],rel
        files=json.loads(p.read_text())['files']
        for r,x in files.items():assert sha(p.parent/r)==x['sha256'] and (p.parent/r).stat().st_size==x['bytes'],r
        # One statement inventory has no external report, the others explicitly bind it.
        internal={r for r in files if not r.startswith('../')}
        assert internal=={f.relative_to(p.parent).as_posix() for f in p.parent.rglob('*') if f.is_file() and f!=p}
        inventories[rel]=dict(sha256=sha(p),bound_files=len(files))
assert sorted(v['bound_files'] for v in inventories.values())==[23,26,36,45]
for key in ['statement_freeze','proof_freeze','coordinator_acceptance']:
    r=manifest['review'][key];assert sha(project/r['file'])==r['sha256']
assert manifest['project']['authors']==['George Stepaniants'] and manifest['project']['affiliations']['George Stepaniants']=='Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA'
for r in ['README.md','formalization.yaml']:
    assert not re.search(r'[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}',(project/r).read_text())
for link in re.findall(r'\]\(([^)]+)\)',(project/'README.md').read_text()):
    if not re.match(r'[a-z]+:',link):assert (project/link.split('#')[0]).exists(),link
assert git('rev-parse','HEAD').decode().strip()=='f41f1f9ffa2171550d4bb795862c6170c4f26070'
assert not git('diff','--name-only') and not git('diff','--cached','--name-only')
assert '**Status:** Solved' in (project.parent/'README.md').read_text()
out.mkdir();schema=subprocess.run(['/tmp/nla-lean-formalization/venv/bin/python','tools/lean/validate_manifest.py',prefix.rstrip('/')],cwd=repo,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
(out/'schema.log').write_bytes(schema.stdout);assert schema.returncode==0,schema.stdout
record=dict(status='APPROVE exact Linux candidate; commit and fork push authorized, actual Linux still pending',utc=datetime.now(timezone.utc).isoformat(),root_role='Proof and statement coauthor, independent of candidate packager; not an independent mathematical referee',
    read_scope='Root read full current README, v0.4 manifest, handoff and both sealed final reports. Hash-checked all 299 current inputs, 288 prepackaging inputs via archived README, 203 proof and 34 statement freeze inputs, ten original Git sources and all four review inventories.',
    metadata_sha256=expected,preparer_input_count=299,preparer_all_input_sha256={**bound,outer.relative_to(project).as_posix():sha(outer)},
    unchanged_nonREADME_proof_inputs=202,unchanged_other_prepackaging_inputs=287,review_evidence=inventories,exact_exports=names,
    actual_schema_command=['tools/lean/validate_manifest.py',prefix.rstrip('/')],schema_exit_code=0,all_original_canonical_and_catalog_bytes_unchanged=True,
    target='Full original every n>=5 real entrywise-nonnegative matrix exact-order n-1 derivative realizability assertion negated. Seven exact exports and all genuine matrix polynomial/trace/power bridges are proved.',
    numerical='Material explicit kernel LeanCert rational singleton -8593/823543<0; both independent referees replayed same checker and actual consumer chain',
    authorship='George full Caltech CMS affiliation; Colbrook mathematical counterexample; Johnson and Hoover-McCormick-Paparella-Thrall source credit. Root and inventory coauthors; leancert and standards are both independent statement/final referees.',
    next_gate='Immutable candidate commit/fork push, actual Ubuntu Comparator/default-kernel/controls, independent operational review, root acceptance and publication review before promotion',canonical_status='Solved',new_Lean_or_dependency_work=False,
    inventory_note='Preparer full-project outer binds the exact 299-input packaging phase, including its four nested manifests. Root acceptance adds a separate directory without rewriting that frozen phase inventory.')
(out/'ROOT-CHECKS.json').write_text(json.dumps(record,indent=2)+'\n')
(out/'review_is03_candidate.py').write_bytes(Path(__file__).read_bytes())
outmanifest=out/'EVIDENCE-MANIFEST.json';files={p.relative_to(out).as_posix():dict(sha256=sha(p),bytes=p.stat().st_size) for p in out.rglob('*') if p.is_file() and p!=outmanifest}
outmanifest.write_text(json.dumps(dict(file_count=len(files),files=files,inventory_rule='Every internal file except only this exact outer manifest; every nested manifest included'),indent=2)+'\n')
print(json.dumps(dict(status=record['status'],root_checks_sha256=sha(out/'ROOT-CHECKS.json'),root_manifest_sha256=sha(outmanifest),total_candidate_inputs=299+len(files)+1),indent=2))
