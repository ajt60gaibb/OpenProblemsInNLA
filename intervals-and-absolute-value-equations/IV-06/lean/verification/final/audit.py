"""Read-only proof/source audit; writes only the bound final audit receipt."""
from pathlib import Path
import datetime,hashlib,json,re,subprocess
P=Path(__file__).resolve().parents[2];R=P.parents[2];E=Path(__file__).resolve().parent
sha=lambda f:hashlib.sha256(Path(f).read_bytes()).hexdigest()
freeze=json.loads((P/'reviews/statement-freeze.json').read_text())
start=json.loads((P/'verification/proof-start.json').read_text())
assert start['proof_absent_at_gate'] and start['Solution_absent_at_gate']
assert sha(P/'reviews/statement-freeze.json')==start['statement_freeze_sha256']
for rel,h in freeze['files'].items():assert sha(P/rel)==h,rel
for rel,h in freeze['source_files'].items():
 b=subprocess.check_output(['git','show',freeze['base']+':'+rel],cwd=R)
 assert hashlib.sha256(b).hexdigest()==h and b==(R/rel).read_bytes(),rel
for rel,h in start['independent_approvals'].items():assert sha(P/rel)==h,rel
latest=json.loads((E/'latest.json').read_text());run=Path(latest['attempt']);result=json.loads((run/'result.json').read_text())
assert sha(run/'result.json')==latest['result_sha256'] and result['verdict']=='PASS'
assert len(result['commands'])==5
for c in result['commands']:
 assert c['exit_code']==0 and sha(P/c['source'])==c['source_sha256'] and sha(run/c['log'])==c['log_sha256'],c
 log=(run/c['log']).read_text()
 assert 'error:' not in log and 'error(' not in log
 if c['source']=='Challenge.lean':assert log.count('warning: declaration uses `sorry`')==8 and len(log.splitlines())==8
 else:assert 'warning:' not in log,c['source']
pins=json.loads((P/'lake-manifest.json').read_text())['packages']
actual={x['name']:x for x in result['pins']}
for dep in pins:
 d=actual[dep['name']];assert d['expected']==dep['rev']==d['actual']
 assert subprocess.check_output(['git','-C',d['path'],'rev-parse','HEAD']).decode().strip()==dep['rev']
 assert not subprocess.check_output(['git','-C',d['path'],'status','--porcelain=v1'])
headers=lambda f:{m[1]:re.sub(r'\s+',' ',m[0]).strip() for m in re.finditer(r'^theorem (\w+)\b[\s\S]*?:= by',Path(f).read_text(),re.M)}
ch=headers(P/'Challenge.lean');sol=headers(P/'Solution.lean');assert ch==sol,(ch,sol)
config=json.loads((P/'comparator.json').read_text());assert config['theorem_names']==['NLA.IV06.'+n for n in ch]
assert config['definition_names']==[] and config['permitted_axioms']==['propext','Classical.choice','Quot.sound']
for rel in ['NLA/IV06/Proof.lean','Solution.lean']:
 s=(P/rel).read_text();clean=re.sub(r'/\-[\s\S]*?\-/','',s);clean=re.sub(r'--[^\n]*','',clean)
 assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by|extern)\b|skipKernelTC|trustCompiler',clean),rel
 assert not re.search(r'^import\s+Challenge\b',s,re.M)
axioms=[]
for rel in ['NLA-IV06-Proof.log','Solution.log']:
 log=(run/rel).read_text()
 for name,used in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log):
  names=[x.strip() for x in used.split(',') if x.strip()]
  assert set(names)=={'propext','Classical.choice','Quot.sound'},(name,names)
  axioms.append({'declaration':name,'axioms':names})
assert len(axioms)==17 and len({x['declaration'] for x in axioms})==17
assert sum((P/rel).read_text().count('#assert_trust kernel ') for rel in ['NLA/IV06/Proof.lean','Solution.lean'])==17
inspection=(run/'verification-final-Inspect.log').read_text()
required=re.findall(r'^RETAINED_DEPENDENCY: (.+)$',inspection,re.M)
assert len(required)==20 and 'LeanCert.Validity.verify_strict_upper_bound_dyadic_checked' in required
assert 'NLA.IV06.numerical_separator_margin' in required
visited=int(re.search(r'PROJECT_DECLARATIONS_REACHABLE_FROM_FULL_NEGATION: (\d+)',inspection)[1]);assert visited==58
prefix=Path(result['fresh_prefix'])
objects={str(f.relative_to(prefix)):{'bytes':f.stat().st_size,'sha256':sha(f)} for f in sorted(prefix.rglob('*')) if f.is_file()}
for rel in ['NLA/IV06/Definitions.olean','NLA/IV06/Proof.olean','Solution.olean','Challenge.olean']:
 assert rel in objects,rel
out={'verdict':'PASS: author implementation complete and local kernel checks passed; two independent final reviews and actual Linux Comparator remain pending','date_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'statement_freeze_sha256':sha(P/'reviews/statement-freeze.json'),'statement_gate_sha256':sha(P/'verification/proof-start.json'),'frozen_project_inputs_unchanged':len(freeze['files']),'original_git_sources_unchanged':len(freeze['source_files']),'statement_review_hashes':start['independent_approvals'],'source_commit':freeze['base'],'fresh_checks':result['commands'],'fresh_result_sha256':sha(run/'result.json'),'fresh_prefix':str(prefix),'compiled_outputs':objects,'identical_challenge_solution_headers':list(ch),'exact_export_config':config,'clean_dependency_pins':actual,'standard_three_axiom_checks':axioms,'kernel_assertions_passed':17,'retained_full_negation_dependencies':required,'reachable_project_declarations':visited,'actual_inspection_sha256':sha(run/'verification-final-Inspect.log'),'core_files':{r:{'bytes':(P/r).stat().st_size,'sha256':sha(P/r)} for r in ['NLA/IV06/Definitions.lean','NLA/IV06/Proof.lean','Solution.lean','Challenge.lean','NUMERICAL_TARGETS.md','lakefile.toml','lake-manifest.json','lean-toolchain','comparator.json']},'no_canonical_status_changes':not subprocess.check_output(['git','diff','--name-only','HEAD'],cwd=R),'local_lake_or_dependency_rebuild_claim':False,'Linux_Comparator_run':False,'source_inspection':'No admissions, added axioms, unsafe declarations, native execution trust or Challenge import in actual Proof/Solution sources; archived failed attempts are retained as historical .txt snapshots and raw logs.'}
assert out['no_canonical_status_changes']
(E/'audit.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS: 5 fresh source commands; 17 standard-three/kernel checks; 20 retained dependencies in 58 project declarations; 32 frozen inputs + 8 original sources unchanged')
print('audit',sha(E/'audit.json'))
