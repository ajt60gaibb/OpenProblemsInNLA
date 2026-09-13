from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re, shutil, subprocess
import yaml

R=Path('/tmp/nla-lean-ra09-worktree'); P=R/'randomized-and-low-rank-approximation/RA-09/lean'
draft=Path('/tmp/nla-lean-formalization/ra09-candidate-draft')
D=P/'verification/linux-candidate-2026-09-13';assert not D.exists()
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
F=json.loads((P/'verification/proof-freeze.json').read_text())
gate=P/'verification/final-review-acceptance.json'
assert h(gate)=='ed2eef518099d23090e21786b626a111d511b32fea12e7193442273e2d980132'
for r,v in F['files'].items():assert h(P/r)==v,r
assert not (P/'formalization.yaml').exists()
manifest=draft/'EVIDENCE-MANIFEST.json';m=json.loads(manifest.read_text())
assert h(manifest)=='9efeb8fc1276b0291708af16fc8136f937cb3887a220fe3dac68fb8ca0cb2117'
for r,v in m['files'].items():assert h(draft/r)==v['sha256'],r
assert {str(p.relative_to(draft)) for p in draft.rglob('*') if p.is_file() and p!=manifest}==set(m['files'])
D.mkdir();shutil.copytree(draft,D/'external-draft')
baseline={str(f.relative_to(P)):dict(sha256=h(f),bytes=f.stat().st_size) for f in sorted(P.rglob('*')) if f.is_file() and not f.is_relative_to(D)}
archive=P/'verification/pre-candidate-README.md';assert not archive.exists()
assert h(P/'README.md')=='ca0cd8e9da1abf5e929a528e98a67b13143056ad1b9403c6477093a1d68fbd0c'
shutil.copyfile(P/'README.md',archive)
t=(draft/'README.md').read_text()
t=t.replace('Coordinator acceptance and authoritative Linux verification are pending.', 'The coordinator has accepted both reports; authoritative Linux verification is pending.',1)
t=t.replace('Coordinator acceptance, actual non-root Ubuntu Comparator/default-kernel replay and rejection controls, operational review and publication remain pending.', '[Coordinator acceptance](verification/final-review-acceptance.json) binds both reports and their complete evidence. Actual non-root Ubuntu Comparator/default-kernel replay and rejection controls, operational review and publication remain pending.',1)
t=t.replace('Frozen Lean bytes remain intact.', 'Frozen Lean bytes remain intact. The exact old README is [archived](verification/pre-candidate-README.md).',1)
(P/'README.md').write_text(t)
meta=yaml.safe_load((draft/'formalization.yaml').read_text())
meta['status']['scope']=meta['status']['scope'].replace('Coordinator acceptance and authoritative Ubuntu\n','Coordinator acceptance and authoritative Ubuntu\n')
meta['status']['scope']=meta['status']['scope'].replace('Coordinator acceptance and authoritative Ubuntu Comparator/default-kernel/control verification, operational acceptance and publication remain pending.','The coordinator accepted both final reports; authoritative Ubuntu Comparator/default-kernel/control verification, operational acceptance and publication remain pending.')
meta['review']['status']='agent-reviewed; Linux-verification-pending'
meta['review']['coordinator_acceptance']={'status':'accepted','file':'verification/final-review-acceptance.json','sha256':h(gate),'note':'Root accepted the two independent final reports after full report/source-boundary review, complete inventory/source rehashing and actual 66/50 axiom-report checks; this adds no independent mathematical approval.'}
meta['review']['candidate_documents']['installation']='Root installed these candidate wrappers after the accepted final-review gate; exact historical README and external draft retained. No Lean mathematics or canonical status changed. Independent concrete packaging review and Linux remain pending.'
meta['review']['candidate_documents']['archive_required_on_installation']=False
meta['review']['historical_readme']={'file':'verification/pre-candidate-README.md','sha256':h(archive)}
(P/'formalization.yaml').write_text('# yaml-language-server: $schema=../../../docs/lean/schema/v0.4.schema.json\n'+yaml.safe_dump(meta,sort_keys=False,allow_unicode=True,width=100))
checks=[]
for label,args in [('schema',['/tmp/nla-lean-formalization/venv/bin/python','tools/lean/validate_manifest.py','randomized-and-low-rank-approximation/RA-09/lean']),('permanent-ids',['python3','tools/validate_problem_ids.py','--base-ref','origin/main'])]:
    r=subprocess.run(args,cwd=R,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);f=D/(label+'.log');f.write_bytes(r.stdout);checks.append(dict(command=args,exit_code=r.returncode,log=f.name,log_sha256=h(f)));assert r.returncode==0,r.stdout.decode()
config=json.loads((P/'comparator.json').read_text());names=config['theorem_names'];assert len(names)==17 and not config.get('definition_names',[])
assert [x['declaration'] for x in meta['status']['main_results']]==names==[x['declaration'] for x in meta['alignment']]
assert 'Coordinator acceptance and authoritative' not in meta['status']['scope']
for link in re.findall(r'\]\(([^)]+)\)',t):
    if not re.match(r'[a-z]+:',link):assert (P/link.split('#')[0]).exists(),link
for r,v in baseline.items():assert h(P/('verification/pre-candidate-README.md' if r=='README.md' else r))==v['sha256'],r
for r,v in F['source_files'].items():assert h(R/r)==v,r
assert subprocess.check_output(['git','diff','--name-only'],cwd=R)==b''
assert subprocess.check_output(['git','diff','--cached','--name-only'],cwd=R)==b''
record=dict(utc=datetime.now(timezone.utc).isoformat(),phase='Live candidate installed after two independent final reviews and root acceptance; independent packaging review and actual Linux pending',coordinator='/root',draft_preparer='/root/mf16_final_referee',draft_outer_sha256=h(manifest),final_review_acceptance_sha256=h(gate),baseline=baseline,archive_mapping={'README.md':'verification/pre-candidate-README.md'},full_proof_inputs_preserved=len(F['files']),original_source_inputs_preserved=len(F['source_files']),wrapper_files={'README.md':h(P/'README.md'),'formalization.yaml':h(P/'formalization.yaml')},mathematical_edits=False,canonical_status='Solved, unchanged',checks=checks,exports=names,read_only_path_diagnostic='Coordinator initially looked for PROOF_MAP under verification; actual frozen file is project-root PROOF_MAP.md and was then fully read. No file was created or moved.')
(D/'INSTALLATION.json').write_text(json.dumps(record,indent=2)+'\n')
(D/'install_candidate.py').write_bytes(Path(__file__).read_bytes())
outer=D/'EVIDENCE-MANIFEST.json'
files={str(f.relative_to(D)):dict(sha256=h(f),bytes=f.stat().st_size) for f in sorted(D.rglob('*')) if f.is_file() and f!=outer}
outer.write_text(json.dumps({'scope':'Every file in this directory, exact outer self-exclusion only; external draft nested manifest retained','files':files},indent=2)+'\n')
print(json.dumps({'README':h(P/'README.md'),'yaml':h(P/'formalization.yaml'),'installation':h(D/'INSTALLATION.json'),'outer':h(outer),'baseline':len(baseline),'bound_files':len(files)},indent=2))
