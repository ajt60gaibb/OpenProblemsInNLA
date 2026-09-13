"""Independent RA09 candidate packaging checks only; no mathematical build or Git edits."""
from pathlib import Path
import datetime,hashlib,json,re,subprocess
import yaml
E=Path(__file__).resolve().parent;P=E.parents[1];W=P.parents[2]
D=P/'verification/linux-candidate-2026-09-13'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text())
git=lambda *a:subprocess.check_output(['git',*a],cwd=W)
known={P/'README.md':'8607a0ff43d23a301775c5db62bcdbeb7af474aef2e3aeac559c4a11c08f02c3',P/'formalization.yaml':'8dc23f21024b4789f470f40d9a43c5de9489f6a0eb8b212d326c7cb1ce9046be',D/'INSTALLATION.json':'e33156d4f14068a44227fc9135f3c5104c8897c9439a3bee6b5169c9b670c07b',D/'EVIDENCE-MANIFEST.json':'3304b2e84f77144ecd55c2b8f40ad2bf2233de306b456837f3e84f6cf4f79db4',P/'verification/final-review-acceptance.json':'ed2eef518099d23090e21786b626a111d511b32fea12e7193442273e2d980132',P/'verification/pre-candidate-README.md':'ca0cd8e9da1abf5e929a528e98a67b13143056ad1b9403c6477093a1d68fbd0c'}
for p,h in known.items():assert sha(p)==h,p
installation=load(D/'INSTALLATION.json');baseline=installation['baseline'];assert len(baseline)==499
for name,row in baseline.items():
 actual=P/installation['archive_mapping'].get(name,name)
 assert sha(actual)==row['sha256'] and actual.stat().st_size==row['bytes'],name
assert 'formalization.yaml' not in baseline
expected=set(baseline)|{'formalization.yaml','verification/pre-candidate-README.md'}|{str(x.relative_to(P)) for x in D.rglob('*') if x.is_file()}
actual={str(x.relative_to(P)) for x in P.rglob('*') if x.is_file() and not x.is_relative_to(E)}
assert actual==expected
counts={}
gate=load(P/'verification/final-review-acceptance.json')
paths=[D/'EVIDENCE-MANIFEST.json',D/'external-draft/EVIDENCE-MANIFEST.json']
paths += [P/r['path'] for r in gate['prior_complete_inventories']]
paths += [P/r['evidence']['path'] for r in gate['reports']]
for outer in paths:
 m=load(outer);directory=outer.parent
 for name,row in m['files'].items():
  f=(directory/name).resolve();h=row if isinstance(row,str) else row['sha256'];assert sha(f)==h,f
  if isinstance(row,dict) and 'bytes' in row:assert f.stat().st_size==row['bytes']
 if outer.is_relative_to(D):
  local={str(x.relative_to(directory)) for x in directory.rglob('*') if x.is_file() and x!=outer}
  assert local==set(m['files'])
 counts[str(outer.relative_to(P))]={'bound_files':len(m['files']),'outer_sha256':sha(outer)}
frozen={}
for name,n in [('verification/proof-freeze.json',361),('reviews/statement-freeze.json',31)]:
 f=load(P/name);assert len(f['files'])==n and len(f['source_files'])==17
 for rel,h in f['files'].items():assert sha(P/installation['archive_mapping'].get(rel,rel))==h,rel
 for rel,h in f['source_files'].items():
  b=git('show',f['base']+':'+rel);assert hashlib.sha256(b).hexdigest()==h
  assert git('rev-parse',f['base']+':'+rel).decode().strip()==f['source_git_blobs'][rel]
  assert (W/rel).read_bytes()==b,rel
 frozen[name]={'files':n,'source_files':17,'sha256':sha(P/name)}
y=yaml.safe_load((P/'formalization.yaml').read_text());c=load(P/'comparator.json');names=c['theorem_names']
assert len(names)==17 and c['definition_names']==[] and names[-1]=='NLA.RA09.concaveFrobeniusTransferConjecture'
assert y['version']=='v0.4' and [x['declaration'] for x in y['status']['main_results']]==names
assert [x['declaration'] for x in y['alignment']]==names==installation['exports']
assert y['status']['sorry_count']==y['status']['sorry_in_definitions']==0
assert all(x['sorry_count']==0 and set(x['axioms'])=={'propext','Classical.choice','Quot.sound'} for x in y['status']['main_results'])
assert set(y['status']['axioms'])==set(c['permitted_axioms'])=={'propext','Classical.choice','Quot.sound'}
assert y['review']['linux_verification']['status']=='pending'
assert y['review']['coordinator_acceptance']['status']=='accepted'
assert y['project']['authors']==['George Stepaniants']
assert y['project']['affiliations']['George Stepaniants']=='Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA'
def rehash_bound_fields(x):
 if isinstance(x,dict):
  if 'file' in x and 'sha256' in x:assert sha(P/x['file'])==x['sha256'],x['file']
  for v in x.values():rehash_bound_fields(v)
 elif isinstance(x,list):
  for v in x:rehash_bound_fields(v)
rehash_bound_fields(y['review'])
for path,v in y['review']['proof_report_evidence'].items():assert sha(P/path)==v['sha256'] and (P/path).stat().st_size==v['bytes']
assert not re.search(r'[\w.+-]+@[\w.-]+\.[A-Za-z]{2,}',(P/'README.md').read_text()+(P/'formalization.yaml').read_text())
assert '**Status:** Solved' in (P.parent/'README.md').read_text()
schema_cmd=['/tmp/nla-lean-formalization/venv/bin/python','tools/lean/validate_manifest.py','randomized-and-low-rank-approximation/RA-09/lean']
r=subprocess.run(schema_cmd,cwd=W,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);(E/'schema.log').write_bytes(r.stdout);assert r.returncode==0,r.stdout.decode()
for x in installation['checks']:assert x['exit_code']==0 and sha(D/x['log'])==x['log_sha256']
result={'verdict':'PASS concrete candidate packaging; independent of wrappers, disclosed mathematical coauthor','reviewer':'/root/formal_review_standards','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'prior_inputs_preserved':499,'archive_mapping':installation['archive_mapping'],'current_wrappers':installation['wrapper_files'],'frozen_inputs':frozen,'all_bound_inventories_checked':counts,'exports':names,'schema_command':schema_cmd,'schema_exit_code':r.returncode,'schema_log_sha256':sha(E/'schema.log'),'canonical_status':'Solved, unchanged','Linux':'pending','proof_or_source_or_pin_changes':False,'mathematical_rerun':False,'Git_or_publication_mutation':False,'additional_independent_mathematical_approval':False}
(E/'CHECKS.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'verdict':'PASS','prior_inputs':499,'proof_inputs':361,'statement_inputs':31,'source_blobs':17,'exports':17,'CHECKS_sha256':sha(E/'CHECKS.json')},indent=2))
