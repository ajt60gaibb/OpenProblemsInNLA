#!/usr/bin/env python3
"""Stage the exact preacceptance TR04 candidate, excluding live audits and caches."""
import hashlib, json, pathlib, subprocess
from datetime import datetime, timezone
R=pathlib.Path(__file__).resolve().parents[5]
B=pathlib.Path(__file__).resolve().parent
assert (R/'problem_ids.json').is_file()
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def rel(p):return str(p.relative_to(R))
paths=set()
def add(p, expected=None):
 p=R/p if isinstance(p,str) else p
 assert p.is_file() and not p.is_symlink(),p
 assert not any(x in p.relative_to(R).parts for x in ['.lake','objects','__pycache__']),p
 assert p.suffix not in ['.olean','.ilean','.o','.pyc'],p
 if expected:assert digest(p)==expected,(p,'hash mismatch')
 paths.add(p)
def tree(p):
 for f in sorted(p.rglob('*')):
  if f.is_file() and f.suffix not in ['.olean','.ilean','.o','.pyc'] and not any(x in f.relative_to(p).parts for x in ['.lake','objects','__pycache__']):add(f)
freeze=B/'CANONICAL_PACKAGE_PREACCEPTANCE_FREEZE_2026-10-26.json'
assert digest(freeze)=='8ee1d4585f3c0a60b101ec962fa9631ebbc043270cf35360669b8018152301eb'
f=json.loads(freeze.read_text())
for name,h in f['inputs'].items():add(f['project']+'/'+name,h)
lock=json.loads((R/f['project']/'proof-source-lock.json').read_text())
for c in lock['copies']:add(c['source'],c['source_sha256'])
for name in ['FIRST_LOOP_CONTEXT_FREEZE_2026-10-26.json','ACTUAL_CANDIDATE_LOOP_FREEZE_2026-10-26.json','FULL_TARGET_DEVELOPMENT_FREEZE_2026-10-26.json','CANONICAL_PACKAGE_PREACCEPTANCE_FREEZE_2026-10-26.json','RECURSIVE_EXECUTION_CORE_FREEZE_2026-10-26.json','RECURSIVE_STAGE_SUPPORT_FREEZE_2026-10-26.json','TTFirstLoopContextConsumer.lean.txt','TTFullTargetConsumer.lean.txt','replay-first-loop-context.py','replay-full-target.py']:
 add(B/name)
for name in ['tt-first-loop-context-author','tt-full-target-author','tt-recursive-execution-author','minimum-strict-author','store-context-author','final-context-author','independent-first-context-geometry','independent-first-loop-context-algebra','independent-candidate-loop-geometry','independent-full-target-geometry','independent-full-target-source-algebra','independent-recursive-core-root','independent-recursive-execution-algebra','independent-recursive-support-algebra','independent-canonical-package-algebra','independent-canonical-package-geometry']:
 tree(B/name)
p=B/'independent-canonical-package-geometry/package-source-audit.json';a=json.loads(p.read_text());add(p)
for e in a['evidence']:add(e['path'],e['sha256'])
for name in ['first-context-build.log','first-gather-context-build.log','first-stage-build.log','first-original-build.log','candidate-loop-induction-build.log','completed-candidates-build.log','full-budget-build.log','candidate-execution-build.log','candidate-all-build.log','full-target-build.log','full-target-consumer-preflight.log','canonical-exports-development-build.log','canonical-direct-child-export-build.log']:
 p=B/'program-assembly'/name
 if p.exists():add(p)
add(R/'docs/lean/proofs/TR-04/sync-canonical-proof.py',f['source_sync']['sha256'])
tree(R/'docs/lean/proofs/TR-04/originals-before-full-proof-2026-10-26')
add(pathlib.Path(__file__).resolve())
# All six terminal author receipts must have passed before this candidate is staged.
receipts=['tt-first-loop-context-author/result.json','tt-full-target-author/result.json','tt-recursive-execution-author/final/result.json','minimum-strict-author/result.json','store-context-author/result.json','final-context-author/result.json']
for name in receipts:
 d=json.loads((B/name).read_text());assert d.get('passed',d.get('success',False)) is True,name
record={
 'recorded_utc':datetime.now(timezone.utc).isoformat(),
 'phase':'candidate for independent canonical and actual Linux/Comparator acceptance',
 'canonical_status':'Solved; no promotion in this commit',
 'parent_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),
 'canonical_freeze':{'path':rel(freeze),'sha256':digest(freeze),'inputs':205,'Lean_sources':190,'shared_copies':184,'TR04_proof_modules':179},
 'complete_target':{'theorem':'NLA.Proofs.TR04.fullTarget','type':'NLA.Statements.TR04.Target','program':'NLA.Proofs.TR04.ttProgram','C':1000000,'k':5,'source_sha256':'b2ce2ff0401ee4d4e0d6fe7ade4f29366acf5b30903348d0cf948ed521149ce1'},
 'terminal_author_receipts':[{'path':rel(B/n),'sha256':digest(B/n)} for n in receipts],
 'fresh_full_target_author_commands':183,
 'independent_canonical_engine_replay':{'result':'independent-canonical-package-geometry/final/result.json','sha256':'88ad8ef84bce0d457b2d1341d936c13729a913aa10eedd8cf8b4b5a92cb85979','fresh_sources':190,'kernel_commands':195,'source_review_excludes_own_prerequisites':True},
 'independent_comprehensive_source_and_canonical_replay':'running; no terminal acceptance claimed',
 'actual_Linux_Comparator':'pending; not claimed',
 'original_live_inputs_unchanged':25,'permanent_problem_IDs_unchanged':217,
 'legacy_arbitrary_unfoldingRank_scaffold_claimed_proved':False,
 'staged_inputs':{rel(p):digest(p) for p in sorted(paths)},
 'cache_or_compiled_files_included':False,
}
out=B/'CANONICAL_CANDIDATE_2026-10-26.json';out.write_text(json.dumps(record,indent=2)+'\n');add(out)
# Preserve exact independently bound snapshots; list the exact source hashes and lines.
w=R/'docs/lean/proofs/TR-04/campaign-2026-10-25/whitespace-preservation.json'
wd=json.loads(w.read_text());existing={x['path']:x for x in wd['files']}
new=[]
for p in sorted(paths):
 lines=[]
 try:txt=p.read_text()
 except UnicodeDecodeError:continue
 for i,line in enumerate(txt.splitlines(),1):
  if line and line[-1] in ' \t':lines.append(i)
 rawlines=txt.splitlines()
 for i in range(len(rawlines),0,-1):
  if rawlines[i-1] != '':break
  lines.append(i)
 lines=sorted(set(lines))
 if not lines:continue
 rp=rel(p);h=digest(p)
 if rp in existing:
  assert existing[rp]['sha256']==h,(rp,'old whitespace record changed')
  existing[rp]['lines']=sorted(set(lines)|set(existing[rp].get('lines',[existing[rp]['line']])))
 else:
  new.append({'path':rp,'sha256':h,'line':lines[0],'lines':lines,'reason':'Exact frozen candidate source/snapshot or raw author diagnostic bytes retained under SHA; no proof, model, trust or ID exception.'})
wd['files'].extend(new);w.write_text(json.dumps(wd,indent=2)+'\n');add(w)
for start in range(0,len(paths),200):subprocess.run(['git','add','--',*[rel(p) for p in sorted(paths)[start:start+200]]],cwd=R,check=True)
# This script intentionally leaves the running comprehensive independent audit unstaged.
check=subprocess.run(['git','diff','--cached','--check'],cwd=R,text=True,capture_output=True)
errors=[]
for ln in check.stdout.splitlines():
 if ': trailing whitespace.' in ln or ': new blank line at EOF.' in ln:
  rp,num,_=ln.split(':',2);entry=next((x for x in wd['files'] if x['path']==rp),None)
  if not entry or digest(R/rp)!=entry['sha256'] or int(num) not in entry.get('lines',[entry['line']]):errors.append(ln)
 elif ln and not ln.startswith('+'):errors.append(ln)
assert not errors,errors
print(json.dumps({'staged_whitelisted_files':len(paths),'new_exact_whitespace_records':len(new),'frozen205_inputs_unchanged':True,'six_terminal_author_replays_pass':True,'whitespace_check_exact_exceptions_only':True,'candidate_record_sha256':digest(out)},indent=2))
