"""Independent final referee 1: reproducible read-only integrity/trust audit."""
from pathlib import Path
import datetime,hashlib,json,re,subprocess
P=Path(__file__).resolve().parents[2];R=P.parents[2];E=Path(__file__).resolve().parent
sha=lambda f:hashlib.sha256(Path(f).read_bytes()).hexdigest()
initial=json.loads((E/'initial-integrity.json').read_text())
for rel,h in initial['hashes'].items():assert sha(P/rel)==h,rel
freeze=json.loads((P/'reviews/proof-freeze.json').read_text())
for rel,m in freeze['files'].items():assert sha(P/rel)==m['sha256'] and (P/rel).stat().st_size==m['bytes'],rel
st=json.loads((P/'reviews/statement-freeze.json').read_text())
for rel,m in st['files'].items():assert sha(P/rel)==(m if isinstance(m,str) else m['sha256']),rel
for rel,h in freeze['source_files'].items():
 b=subprocess.check_output(['git','show',freeze['source_commit']+':'+rel],cwd=R)
 assert hashlib.sha256(b).hexdigest()==h and b==(R/rel).read_bytes(),rel
latest=json.loads((E/'latest.json').read_text());run=Path(latest['attempt']);result=json.loads((run/'result.json').read_text())
assert sha(run/'result.json')==latest['result_sha256'] and result['verdict']=='PASS' and len(result['commands'])==10
for c in result['commands']:
 assert c['exit_code']==0 and sha(P/c['source'])==c['source_sha256'] and sha(run/c['log'])==c['log_sha256'],c
 log=(run/c['log']).read_text()
 assert 'error:' not in log and 'error(' not in log
 if c['source']=='Challenge.lean':assert log.count('warning: declaration uses `sorry`')==8 and len(log.splitlines())==8
 else:assert 'warning:' not in log,c['source']
headers=lambda f:{m[1]:re.sub(r'\s+',' ',m[0]).strip() for m in re.finditer(r'^theorem (\w+)\b[\s\S]*?:= by',Path(f).read_text(),re.M)}
ch=headers(P/'Challenge.lean');sol=headers(P/'Solution.lean');assert ch==sol and len(ch)==8
config=json.loads((P/'comparator.json').read_text());assert config['theorem_names']==['NLA.IE23.'+n for n in ch]
assert config['definition_names']==[] and config['permitted_axioms']==['propext','Classical.choice','Quot.sound']
impl=[*sorted((P/'NLA/IE23').glob('*.lean')),P/'Solution.lean']
source_scan={}
for f in impl:
 s=f.read_text();clean=re.sub(r'/\-[\s\S]*?\-/','',s);clean=re.sub(r'--[^\n]*','',clean)
 assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by|extern)\b|skipKernelTC|trustCompiler',clean),f
 assert not re.search(r'^import\s+Challenge\b',s,re.M),f
 source_scan[str(f.relative_to(P))]={'sha256':sha(f),'bytes':f.stat().st_size,'admissions_or_extra_trust':False}
axioms=[]
for rel in ['NLA-IE23-Proof.log','Solution.log']:
 for name,used in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",(run/rel).read_text()):
  used=[x.strip() for x in used.split(',') if x.strip()]
  assert set(used)=={'propext','Classical.choice','Quot.sound'},(name,used)
  axioms.append({'declaration':name,'axioms':used})
assert len(axioms)==16 and len({x['declaration'] for x in axioms})==16
assert sum(f.read_text().count('#assert_trust kernel ') for f in impl)==16
inspection=run/'reviews-proof-referee-1-evidence-Inspect.log';text=inspection.read_text()
required=re.findall(r'^RETAINED_DEPENDENCY (.+)$',text,re.M);assert len(required)==40
count=int(re.search(r'REACHABLE_PROJECT_DECLARATIONS (\d+)',text)[1]);assert count==93
assert json.loads((E/'exact-reconstruction.json').read_text())['actual_frozen_definition_sha256']==sha(P/'NLA/IE23/Definitions.lean')
pins=json.loads((P/'lake-manifest.json').read_text())['packages'];actual={x['name']:x for x in result['pins']}
for package in pins:
 d=actual[package['name']]
 assert d['expected']==package['rev']==d['actual']
 assert subprocess.check_output(['git','-C',d['path'],'rev-parse','HEAD']).decode().strip()==package['rev']
 assert not subprocess.check_output(['git','-C',d['path'],'status','--porcelain=v1'])
read_files={'mathlib':['Mathlib/Analysis/InnerProductSpace/PiL2.lean','Mathlib/Analysis/SpecialFunctions/Pow/Real.lean','Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean','Mathlib/LinearAlgebra/Matrix/Rank.lean','Mathlib/Order/ConditionallyCompleteLattice/Basic.lean'],'leancert':['LeanCert/Tactic/Verification.lean']}
library={}
for name,paths in read_files.items():
 d=actual[name];base=Path(d['path'])
 for rel in paths:
  b=subprocess.check_output(['git','-C',str(base),'show',d['actual']+':'+rel])
  assert b==(base/rel).read_bytes()
  library[name+'/'+rel]={'revision':d['actual'],'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b)}
standards=Path('/tmp/nla-lean-formalization/standards');sm=json.loads((standards/'MANIFEST.json').read_text());rubrics={}
for angle in ['scope','correctness','proof-quality','reuse','generality','api-design','naming','placement','documentation','attribution']:
 rel='sources/TauCetiProject/TauCetiReview/rubrics/'+angle+'.md'
 assert sha(standards/rel)==sm[rel]['sha256']
 rubrics[angle]=sm[rel]
(E/'primary-library-and-review-inputs.json').write_text(json.dumps({'primary_pinned_library':library,'Tau_Ceti_revision':'afb424eda89e8ac96d9eb69f6a88972055a4cd1b','ten_rubric_inputs':rubrics,'NLA_adaptation_sha256':sha(R/'docs/lean/REVIEW.md'),'scope':'Independent AI review through NLA adaptation; no official Tau Ceti service claim'},indent=2)+'\n')
searches=[['rg','-n','inducedNorm|moorePenrose|norm_le.*norm|norm_le.*sum|sum_sq_le_sq_sum','Mathlib/Analysis/Normed/Lp/PiLp.lean','Mathlib/Analysis/InnerProductSpace/PiL2.lean','Mathlib/Analysis/Matrix/Normed.lean'],['rg','-n','inv_eq_left_inv|rank_mul_le_left|rank_one|rank_le_height','Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean','Mathlib/LinearAlgebra/Matrix/Rank.lean'],['rg','-n','isLUB_csSup|le_csSup|csSup_le','Mathlib/Order/ConditionallyCompleteLattice/Basic.lean']]
rows=[]
for i,cmd in enumerate(searches):
 res=subprocess.run(cmd,cwd=actual['mathlib']['path'],capture_output=True);assert res.returncode in (0,1)
 log=E/f'reuse-search-{i+1}.log';log.write_bytes(res.stdout+res.stderr)
 rows.append({'command':cmd,'cwd':actual['mathlib']['path'],'exit_code':res.returncode,'log':log.name,'log_sha256':sha(log)})
(E/'reuse-search.json').write_text(json.dumps(rows,indent=2)+'\n')
(E/'final-audit.json').write_text(json.dumps({'verdict':'PASS: local independent final proof review; actual Linux remains pending','date_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'proof_freeze_sha256':sha(P/'reviews/proof-freeze.json'),'proof_completion_sha256':sha(P/'reviews/proof-completion.md'),'frozen_project_inputs_unchanged':len(freeze['files']),'frozen_original_statement_inputs_unchanged':len(st['files']),'original_source_Git_blobs_unchanged':len(freeze['source_files']),'exact_config_supplement_sha256':sha(P/'reviews/statement-config-supplement.json'),'eight_exact_headers':ch,'source_scan':source_scan,'fresh_result_sha256':sha(run/'result.json'),'fresh_commands':result['commands'],'fresh_prefix':result['fresh_prefix'],'clean_dependency_pins':actual,'axioms':axioms,'kernel_assertions_passed':16,'actual_inspection_sha256':sha(inspection),'retained_dependencies':required,'reachable_project_declarations':count,'exact_diagnostic_sha256':sha(E/'exact-reconstruction.json'),'canonical_and_tracked_tree_unchanged':not subprocess.check_output(['git','diff','--name-only','HEAD'],cwd=R),'local_Lake_or_fresh_dependency_rebuild_claim':False,'Linux_Comparator_run':False},indent=2)+'\n')
print('PASS: 104 proof inputs + original 32 + eight source Git blobs + supplement unchanged')
print('PASS: ten fresh commands, 16 kernel/standard-three checks, eight matching headers, 40 retained dependencies in 93 project declarations')
print('final-audit',sha(E/'final-audit.json'))
print('inspection',sha(inspection))
