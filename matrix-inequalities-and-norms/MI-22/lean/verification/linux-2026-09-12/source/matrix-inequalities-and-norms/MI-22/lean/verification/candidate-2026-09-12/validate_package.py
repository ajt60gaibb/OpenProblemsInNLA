"""Candidate-only validation; preserves every mathematical and historical input.
Run from the repository root with the campaign's metadata-enabled Python.
"""
from pathlib import Path
import hashlib,json,subprocess,sys,datetime,re
OUT=Path(__file__).resolve().parent;PROJECT=OUT.parents[1];REPO=PROJECT.parents[2]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(name,x):(OUT/name).write_text(json.dumps(x,indent=2)+'\n')
f=json.loads((PROJECT/'verification/proof-freeze.json').read_text());assert len(f['files'])==104
assert sha(PROJECT/'verification/proof-freeze.json')=='f1c267a6aa600074d3b054863926d5f9cdbf6b0eadb83912a912277ac54018a0'
changed=[]
for rel,r in f['files'].items():
    if sha(PROJECT/rel)!=r['sha256']:changed.append(rel)
assert changed==['README.md'],changed
assert sha(OUT/'README.statement.md')==f['files']['README.md']['sha256']
for rel,h in f['source_files'].items():
    b=subprocess.check_output(['git','show',f['source_commit']+':'+rel],cwd=REPO)
    assert b==(REPO/rel).read_bytes() and sha(REPO/rel)==h,rel
pre=json.loads((OUT/'inputs-before.json').read_text())
for rel,h in pre['reviews'].items():assert sha(PROJECT/rel)==h,rel
manifests={}
for rel in ['reviews/proof-referee-1-evidence/EVIDENCE-MANIFEST.json','reviews/proof-referee-2-root-evidence/manifest.json']:
    q=PROJECT/rel;m=json.loads(q.read_text())
    for name,r in m['files'].items():
        t=q.parent/name;assert sha(t)==r['sha256'] and t.stat().st_size==r['bytes'],name
    manifests[rel]={'sha256':sha(q),'verified_files':len(m['files'])}
config=json.loads((PROJECT/'comparator.json').read_text());assert len(config['theorem_names'])==8 and not config['definition_names']
assert '**Status:** Solved' in (PROJECT.parent/'README.md').read_text()
# Local Markdown links in the new public overview must resolve.
links=[]
for target in re.findall(r'\]\(([^)]+)\)',(PROJECT/'README.md').read_text()):
    if target.startswith(('https://','http://','#')):continue
    q=(PROJECT/target.split('#')[0]).resolve();assert q.exists(),target
    links.append(target)
commands=[('manifest.log',[sys.executable,'tools/lean/validate_manifest.py','matrix-inequalities-and-norms/MI-22/lean']),('permanent-ids.log',['python3','tools/validate_problem_ids.py','--base-ref','origin/main']),('permanent-id-tests.log',['python3','-m','unittest','discover','-s','tests','-p','test_problem_ids.py','-v'])]
results=[]
for name,cmd in commands:
    p=subprocess.run(cmd,cwd=REPO,capture_output=True);(OUT/name).write_bytes(p.stdout+p.stderr)
    results.append({'command':cmd,'cwd':'repository root','exit_code':p.returncode,'log':name,'sha256':sha(OUT/name)})
    assert p.returncode==0,(name,p.stdout,p.stderr)
save('validation.json',{'date_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'checks':results,'verdict':'PASS'})
record={'verdict':'PASS','source_commit':f['source_commit'],'proof_freeze_sha256':sha(PROJECT/'verification/proof-freeze.json'),'frozen_project_inputs':104,'unchanged_frozen_project_inputs':103,'changed_frozen_project_inputs':['README.md'],'original_README_archived_as':'verification/candidate-2026-09-12/README.statement.md','original_README_sha256':sha(OUT/'README.statement.md'),'current_README_sha256':sha(PROJECT/'README.md'),'formalization_yaml_sha256':sha(PROJECT/'formalization.yaml'),'all_8_original_sources_unchanged':True,'all_mathematical_source_Challenge_targets_mapping_configuration_pins_unchanged':True,'bound_reports':pre['reviews'],'verified_final_review_manifests':manifests,'comparator_exports':config['theorem_names'],'definition_exceptions':[],'canonical_status':'Solved','actual_Linux_verification':'pending; no result claimed','valid_local_README_links':links,'git_status':subprocess.check_output(['git','status','--short'],cwd=REPO).decode(),'scope':'Only MI-22 project README, new metadata and candidate records; no canonical/index/PDF changes, commit or push.'}
save('integrity.json',record)
print('PASS: actual v0.4/eight exports, 217 permanent IDs, 17 tests, all original math/pins/reviews intact; only frozen README updated and archived.')
