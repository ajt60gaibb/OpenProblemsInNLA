#!/usr/bin/env python3
"""Bind the accepted final TR04 inputs and stage only immutable final evidence."""
import pathlib,json,hashlib,datetime,subprocess
R=pathlib.Path(__file__).resolve().parents[5];B=pathlib.Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();files=set()
def add(p):
 assert p.is_file() and not p.is_symlink(),p
 assert not any(x in p.relative_to(R).parts for x in ['.lake','objects','__pycache__']),p
 assert p.suffix not in ['.olean','.ilean','.o','.pyc','.so','.a'],p
 files.add(p)
freeze=B/'CANONICAL_PROMOTION_FREEZE_2026-10-26.json';assert sha(freeze)=='44b5df77ea7ed70c35aac6e87b2001f2b6860a36f58f1156a50d01a3c83374f7';f=json.loads(freeze.read_text())
for n,h in f['inputs'].items():
 p=R/f['project']/n;assert sha(p)==h,n
 assert hashlib.sha256(subprocess.check_output(['git','show','09cd782576559502787fb536bc1427bf64b7b3e4:'+f['project']+'/'+n],cwd=R)).hexdigest()==h,n
receipts={'independent_827':('independent-linux-promotion-algebra/APPROVAL.json','0e79c5f71ff3e2effae3a30c9bbeb18a7fd21212f1484de6615fb209b073ded9'),'independent_refetched_1214':('independent-linux-promotion-review/APPROVAL.json','c874e464c966bcde167bfa3a0c583b73384fe3c54572ebab5c41c108ef9de7d0')}
for n,(p,h) in receipts.items():assert sha(B/p)==h,(n,p)
for n in ['independent-linux-promotion-algebra','independent-linux-promotion-review','linux-pr370-promotion']:
 for p in sorted((B/n).rglob('*')):
  if p.is_file() and not any(x in p.parts for x in ['__pycache__','.lake','objects']):add(p)
add(R/'docs/lean/proofs/TR-04/LINUX_CI_RECEIPT.md');add(pathlib.Path(__file__).resolve())
record={'recorded_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'Complete original TR04 Target and exact descriptive promotion, final independently accepted source-bound Linux package','final_proof_metadata_source_commit':'09cd782576559502787fb536bc1427bf64b7b3e4','proof_candidate_commit':'027aaefbadf602ac460d0cf4cae7beed3181d712','historical_reproducible_checkpoint':'e7b6c9c592d823973aac5d39a6dbe6c81c0005ce','actual_Linux_run':40408919808,'actual_Linux_job':121875088207,'actual_executed_PR_merge':'5c58fa518732636edcb21c377f8014fa00f34480','actual_merge_parents':['01141f415715a27473cabc1f35ef898e86aafae2','09cd782576559502787fb536bc1427bf64b7b3e4'],'actual_GitHub_artifact':12692842329,'original_ZIP_sha256':'bd48f52a1f448b3f09b8f39e2a07a946b38bc9e610d9ca55f965a9a80196efcc','original_raw_job_sha256':'03be81cfc841504b92aa8a41e47d2798ba97996d9a18962779bb5b94f884f920','canonical_inputs':205,'canonical_Lean_inputs':190,'actual_Linux_imported_project_modules':187,'actual_Linux_proof_modules':179,'exact_shared_copies':184,'selected_exports':['candidate_count_le_first_mode','cyclic_window_count_le_first_mode','NLA.TR04.target'],'transitive_axioms':{'candidate_count_le_first_mode':[],'cyclic_window_count_le_first_mode':[],'NLA.TR04.target':['propext','Classical.choice','Quot.sound']},'complete_Target_source_sha256':'b2ce2ff0401ee4d4e0d6fe7ade4f29366acf5b30903348d0cf948ed521149ce1','fixed_program':'NLA.Proofs.TR04.ttProgram','fixed_C':1000000,'fixed_k':5,'canonical205_sha256':f['inputs'],'final_independent_receipts':{n:{'path':str((B/p).relative_to(R)),'sha256':h} for n,(p,h) in receipts.items()},'all217_problem_IDs_unchanged':True,'all25_original_inputs_archived_exact':True,'original_problem_statement_suffix_unchanged':True,'legacy_canonical_Challenge_Solution_SPEC_README_unchanged':True,'catalog_counts':{'Lean verified':87,'Solved':31,'Open':36,'Partially resolved':62,'Solution claimed':1},'remote_PR_merged':False,'PR':'https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/370','overall_all_Solved_goal_complete':False,'seal_commit_scope':'Documentation and retained evidence only; all205 executable-package/source inputs remain exactly equal to accepted09cd input hashes.','evidence_files':{str(p.relative_to(R)):sha(p) for p in sorted(files)}}
out=B/'FINAL_ACCEPTANCE_SEAL_2026-10-26.json';out.write_text(json.dumps(record,indent=2)+'\n');add(out)
w=R/'docs/lean/proofs/TR-04/campaign-2026-10-25/whitespace-preservation.json';d=json.loads(w.read_text())
for p in sorted(files):
 try:t=p.read_text()
 except UnicodeDecodeError:continue
 ls=t.splitlines();ns=[i for i,l in enumerate(ls,1) if l and l[-1] in ' \t']
 for i in range(len(ls),0,-1):
  if ls[i-1]!='':break
  ns.append(i)
 ns=sorted(set(ns))
 if not ns:continue
 rp=str(p.relative_to(R));h=sha(p);es=[e for e in d['files'] if e['path']==rp and e['sha256']==h]
 if es:es[-1]['lines']=sorted(set(ns)|set(es[-1].get('lines',[es[-1]['line']])))
 else:d['files'].append({'path':rp,'sha256':h,'line':ns[0],'lines':ns,'reason':'Retain exact original final GitHub raw logs, independently sealed final-audit artifacts, and frozen diagnostics. No proof, trust, model or ID exception.'})
w.write_text(json.dumps(d,indent=2)+'\n');add(w)
ordered=sorted(files)
for i in range(0,len(ordered),150):subprocess.run(['git','add','--',*[str(p.relative_to(R)) for p in ordered[i:i+150]]],cwd=R,check=True)
r=subprocess.run(['git','diff','--cached','--check'],cwd=R,text=True,capture_output=True);errs=[]
for line in r.stdout.splitlines():
 if ': trailing whitespace.' in line or ': new blank line at EOF.' in line:
  p,n,_=line.split(':',2);es=[e for e in d['files'] if e['path']==p and e['sha256']==sha(R/p) and int(n) in e.get('lines',[e['line']])]
  if not es:errs.append(line)
 elif line and not line.startswith('+'):errs.append(line)
assert not errs,errs
print(json.dumps({'final205_exact':True,'independent_actual_Linux_audits':[827,1214],'whitelisted_evidence_files':len(files),'compiled_objects_or_symlinks':False,'final_acceptance_seal_sha256':sha(out)},indent=2))
