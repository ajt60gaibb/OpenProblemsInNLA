"""Read-only completed MF16 boundary, fresh evidence and source integrity audit."""
from pathlib import Path
import datetime,hashlib,json,re,subprocess
P=Path(__file__).resolve().parents[2];W=P.parents[2];E=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
f=json.loads((P/'reviews/statement-freeze.json').read_text())
for rel,h in f['files'].items():assert sha(P/rel)==h,rel
for rel,h in f['source_files'].items():
 data=subprocess.check_output(['git','-C',str(W),'show',f['base']+':'+rel])
 assert data==(W/rel).read_bytes() and hashlib.sha256(data).hexdigest()==h,rel
cfg=json.loads((P/'comparator.json').read_text());assert len(cfg['theorem_names'])==9 and cfg['definition_names']==[]
challenge=(P/'Challenge.lean').read_text();solution=(P/'Solution.lean').read_text()
signatures={}
for full in cfg['theorem_names']:
 name=full.rsplit('.',1)[-1];pattern=rf'^theorem {name}\b(.*?):='
 a=re.findall(pattern,challenge,re.M|re.S);b=re.findall(pattern,solution,re.M|re.S)
 assert len(a)==len(b)==1
 assert re.sub(r'\s+','',a[0])==re.sub(r'\s+','',b[0]),full
 signatures[full]={'exact_signature_ignoring_whitespace':True,'signature_sha256':hashlib.sha256(re.sub(r'\s+','',a[0]).encode()).hexdigest()}
mathfiles=[*sorted((P/'NLA/MF16').glob('*.lean')),P/'Solution.lean']
for p in mathfiles:
 text=p.read_text()
 assert not re.search(r'\b(sorry|admit|native_decide)\b',text),p
 assert not re.search(r'^\s*(axiom|unsafe|partial)\b',text,re.M),p
 assert not re.search(r'^\s*import\s+Challenge\b',text,re.M),p
last=json.loads((E/'latest.json').read_text());run=Path(last['attempt']);r=json.loads((run/'result.json').read_text())
assert sha(run/'result.json')==last['result_sha256'] and r['verdict'].startswith('PASS')
assert len(r['commands'])==10 and len(r['pins'])==10 and r['pins_rechecked_after']
closures=[];logs={}
for row in r['commands']:
 p=P/row['source'];log=run/row['log'];text=log.read_text()
 assert row['exit_code']==0 and sha(p)==row['sha256'] and sha(log)==row['log_sha256']
 assert p.read_bytes()==(run/(row['source'].replace('/','-')+'.txt')).read_bytes()
 logs[row['source']]=text
 for axioms in re.findall(r'depends on axioms: \[(.*?)\]',text,re.S):
  values={x.strip() for x in axioms.split(',')}
  assert values=={'propext','Classical.choice','Quot.sound'}
  closures.append(sorted(values))
assert len(closures)==26,len(closures)
assert logs['Challenge.lean'].count('warning: declaration uses `sorry`')==9
inspect=logs['verification/final/Inspect.lean']
assert 'PROJECT_DECLARATIONS: 110' in inspect and 'LIBRARY_SEMANTIC_PROOFS_TRAVERSED: 9' in inspect
required=re.findall(r'^MATERIAL_DEPENDENCY: (.+)$',inspect,re.M);assert len(required)==35
assert 'SAFE_RETAINED_EDGE NLA.MF16.actual_krawczyk_checked._proof_1_1:' in inspect
assert 'NLA.MF16.actual_krawczyk_checked._proof_1_1' in inspect
assert not subprocess.check_output(['git','-C',str(W),'diff','--name-only'])
canonical=(W/'matrix-functions-and-stability/MF-16/README.md').read_text()
assert '**Status:** Solved' in canonical
g=json.loads((P/'verification/implementation-roles.json').read_text())
assert g['implementation_owners']['NLA/MF16/CayleyHamilton.lean']=='/root/solved_statement_inventory'
result={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'verdict':'PASS exact full boundary and completed source/fresh-evidence audit','statement_freeze_sha256':sha(P/'reviews/statement-freeze.json'),'statement_inputs_unchanged':len(f['files']),'original_Git_sources_unchanged':len(f['source_files']),'canonical_status':'Solved unchanged','signatures':signatures,'definition_exceptions':[],'math_sources':{str(p.relative_to(P)):{'sha256':sha(p),'bytes':p.stat().st_size} for p in mathfiles},'fresh_result_sha256':sha(run/'result.json'),'fresh_commands':10,'standard_three_reports':len(closures),'safe_project_declarations_traversed':110,'LeanCert_semantic_library_steps_traversed':9,'material_dependencies':required,'retained_kernel_Boolean_helper':'NLA.MF16.actual_krawczyk_checked._proof_1_1','local_platform':r['platform'],'linux_or_Comparator_success_claimed':False,'independent_final_reviews':'pending; implementation coauthors and root route contributor do not count','v0.4_metadata':'Required before candidate publication; not yet authored, no schema claim','no_source_changes':True}
(E/'source-audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['verdict','statement_inputs_unchanged','original_Git_sources_unchanged','fresh_commands','standard_three_reports','safe_project_declarations_traversed','LeanCert_semantic_library_steps_traversed']},indent=2))
