from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re, subprocess, yaml

repo=Path('/tmp/nla-lean-ie23-worktree')
project=repo/'linear-systems-and-elimination/IE-23/lean'
candidate=project/'verification/linux-candidate-2026-09-12'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
git=lambda *args:subprocess.check_output(['git',*args],cwd=repo)
before=json.loads((candidate/'inputs-before.json').read_text())
assert git('rev-parse','HEAD').decode().strip()==before['base']
commands=[
 ('manifest',['/tmp/nla-lean-formalization/venv/bin/python','tools/lean/validate_manifest.py','linear-systems-and-elimination/IE-23/lean']),
 ('permanent-ids-origin',['python3','tools/validate_problem_ids.py','--base-ref','origin/main']),
 ('permanent-ids-upstream',['python3','tools/validate_problem_ids.py','--base-ref','nla-upstream/main']),
 ('catalog',['python3','tools/update_catalog.py','--base-ref','origin/main']),
 ('permanent-id-tests',['python3','-m','unittest','discover','-s','tests','-p','test_problem_ids.py','-v']),
 ('unchanged-tracked-tree',['git','diff','--exit-code','HEAD']),
]
checks=[]
for name,args in commands:
 r=subprocess.run(args,cwd=repo,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (candidate/(name+'.log')).write_bytes(r.stdout)
 checks.append({'name':name,'command':args,'exit_code':r.returncode,'log':name+'.log','sha256':hashlib.sha256(r.stdout).hexdigest()})
 (candidate/'checks.json').write_text(json.dumps(checks,indent=2)+'\n')
 print(name,'exit',r.returncode,r.stdout.decode()[-600:],flush=True)
 assert r.returncode==0,name
changes={p:{'frozen_sha256':r['sha256'],'current_sha256':sha(project/p)} for p,r in before['preexisting_project_inputs'].items() if sha(project/p)!=r['sha256']}
assert set(changes)=={'README.md'}
assert sha(candidate/'README.statement.md')==before['preexisting_project_inputs']['README.md']['sha256']
for p,r in before['proof_frozen_inputs'].items():
 f=candidate/'README.statement.md' if p=='README.md' else project/p
 assert sha(f)==r['sha256'] and f.stat().st_size==r['bytes'],p
for p,h in before['source_inputs'].items():
 assert sha(repo/p)==h and sha(project/'reviews/source-snapshot'/p)==h,p
 assert hashlib.sha256(git('show',before['base']+':'+p)).hexdigest()==h,p
assert sha(project/'comparator.json')==before['config_sha256']
assert sha(project/'reviews/statement-config-supplement.json')==before['supplement_sha256']
for p,h in before['report_sha256'].items():assert sha(project/p)==h,p
for p,r in before['review_evidence'].items():
 m=project/p;assert sha(m)==r['sha256'],p;data=json.loads(m.read_text())
 for q,s in data['files'].items():
  f=m.parent/q;assert sha(f)==s['sha256'] and f.stat().st_size==s['bytes'],q
 actual={str(f.relative_to(m.parent)) for f in m.parent.rglob('*') if f.is_file() and f!=m}
 assert actual=={q for q in data['files'] if not q.startswith('../')},p
assert git('diff','--name-only','HEAD')==b''
registry=json.loads((repo/'problem_ids.json').read_text())
assert len(registry)==217
for ident,rel in registry.items():assert (repo/rel).read_bytes()==git('show',before['base']+':'+rel),ident
canonical=(repo/'linear-systems-and-elimination/IE-23/README.md').read_text()
assert re.search(r'^\*\*Status:\*\* Solved\s*$',canonical,re.M)
deps=Path('/tmp/nla-lean-mi22-worktree/matrix-inequalities-and-norms/MI-22/lean/.lake/packages')
pins=[]
for pkg in json.loads((project/'lake-manifest.json').read_text())['packages']:
 p=deps/pkg['name']; rev=subprocess.check_output(['git','rev-parse','HEAD'],cwd=p,text=True).strip()
 status=subprocess.check_output(['git','status','--porcelain'],cwd=p,text=True)
 assert rev==pkg['rev'] and status=='',(pkg['name'],rev,status)
 pins.append({'name':pkg['name'],'path':str(p),'revision':rev,'git_status_porcelain':status})
assert len(pins)==10
(candidate/'dependency-pins.json').write_text(json.dumps({'scope':'Read-only source revision/cleanliness check; no dependency download, build or object mutation','pins':pins},indent=2)+'\n')
metadata=yaml.safe_load((project/'formalization.yaml').read_text());config=json.loads((project/'comparator.json').read_text())
assert [x['declaration'] for x in metadata['status']['main_results']]==config['theorem_names']
assert config['definition_names']==[] and set(config['permitted_axioms'])=={'propext','Classical.choice','Quot.sound'}
assert metadata['review']['linux_verification']['status']=='pending'
assert metadata['project']['authors']==['George Stepaniants']
assert metadata['project']['affiliations']['George Stepaniants']=='Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA'
for report in metadata['review']['statement_reports']+metadata['review']['proof_reports']:
 assert sha(project/report['file'])==report['sha256'],report
assert sha(project/metadata['review']['proof_freeze']['file'])==metadata['review']['proof_freeze']['sha256']
assert sha(project/metadata['review']['configuration_supplement']['file'])==metadata['review']['configuration_supplement']['sha256']
new_text=(project/'README.md').read_text()+(project/'formalization.yaml').read_text()
assert not re.search(r'[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}',new_text)
for marker in ['Department of Computing and Mathematical Sciences','California Institute of Technology','Matthew J. Colbrook','Dokmanić','Gribonval']:
 assert marker in new_text,marker
links=[]
for target in re.findall(r'\]\(([^)]+)\)',(project/'README.md').read_text()):
 if re.match(r'[a-z]+:',target):continue
 assert (project/target.split('#')[0]).exists(),target
 links.append(target)
record={'result':'PASS: completed local-proof Linux candidate metadata; parent review and actual Linux pending',
 'created_utc':datetime.now(timezone.utc).isoformat(),'source_base':before['base'],
 'current_upstream_tracking_reference':git('rev-parse','nla-upstream/main').decode().strip(),
 'base_scope_note':'The source review is bound to the frozen f41 source, not a claim about current upstream status counts.',
 'canonical_status':'Solved','canonical_source_and_all_tracked_files_unchanged':True,'all_217_canonical_pages_unchanged':True,
 'preexisting_input_count':len(before['preexisting_project_inputs']),'only_changed_preexisting_input':changes,
 'unchanged_preexisting_inputs':len(before['preexisting_project_inputs'])-1,
 'proof_freeze_inputs':len(before['proof_frozen_inputs']),'unchanged_nonREADME_proof_inputs':len(before['proof_frozen_inputs'])-1,
 'exact_historical_README_archive':{'file':'README.statement.md','sha256':sha(candidate/'README.statement.md')},
 'all_original_source_snapshots_preserved':before['source_inputs'],'original_source_count':len(before['source_inputs']),
 'review_reports_preserved':before['report_sha256'],'review_evidence_preserved':before['review_evidence'],
 'comparator_sha256':sha(project/'comparator.json'),'configuration_supplement_sha256':sha(project/'reviews/statement-config-supplement.json'),
 'export_count':len(config['theorem_names']),'exports':config['theorem_names'],'ten_clean_exact_pins':True,
 'Lean_or_Lake_run_in_packaging':False,'dependency_download_or_build':False,'actual_Linux_run':False,
 'no_new_email':True,'metadata_sha256':{'README.md':sha(project/'README.md'),'formalization.yaml':sha(project/'formalization.yaml')},
 'local_README_links_checked':links,'commit_or_push':False,
 'packager_role':'/root/formal_review_standards prepared documentation and preservation checks; it did not author or independently final-referee this IE-23 proof.'}
(candidate/'packaging-record.json').write_text(json.dumps(record,indent=2)+'\n')
(candidate/'check_packaging.py').write_bytes(Path(__file__).read_bytes())
print(json.dumps({k:record[k] for k in ['result','unchanged_preexisting_inputs','unchanged_nonREADME_proof_inputs','original_source_count','export_count','current_upstream_tracking_reference']},indent=2))
