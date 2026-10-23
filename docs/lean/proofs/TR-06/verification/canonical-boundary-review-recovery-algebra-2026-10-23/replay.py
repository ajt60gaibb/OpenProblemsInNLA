#!/usr/bin/env python3
"""Independent exact pre-Solution statement-boundary replay; no solution claim."""
import hashlib,json,os,platform,re,subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent
REPO=HERE.parents[5]
CAN=REPO/'tensor-computations/TR-06/lean'
LOCK=REPO/'docs/lean/proofs/TR-06/canonical-boundary-before-solution/source-lock.json'
LEAN=REPO.parent/'tooling/lean-4.33.1-darwin_aarch64/bin/lean'
def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()
initial_lock_hash=digest(LOCK)
lock=json.loads(LOCK.read_text())
assert len(lock['records'])==70
assert not (CAN/'Solution.lean').exists()
checks=[]
for x in lock['records']:
 p=CAN/x['path'];actual=digest(p)
 assert actual==x['sha256'],x['path']
 checks.append({'path':x['path'],'sha256':actual,'pass':True})
retained=json.loads((REPO/'docs/lean/proofs/TR-06/campaign-2026-10-18/retained-58-source-lock.json').read_text())
assert len(retained['records'])==58
for x in retained['records']:
 assert digest(REPO/x['published_path'])==x['sha256']
 assert digest(REPO/x['campaign_path'])==x['sha256']
old=(REPO/'docs/lean/proofs/TR-06/campaign-2026-10-18/published-partial-boundary/Challenge.lean').read_text()
new=(CAN/'Challenge.lean').read_text()
without_import=new.replace('import NLA.Statements.TR06\n','')
assert without_import.startswith(old)
assert old.count('\ntheorem ')==10 and new.count('\ntheorem ')==11
oldconfig=json.loads((REPO/'docs/lean/proofs/TR-06/campaign-2026-10-18/published-partial-boundary/comparator.json').read_text())
config=json.loads((CAN/'comparator.json').read_text())
assert config['theorem_names']==oldconfig['theorem_names']+['NLA.TR06.target']
assert config['definition_names']==[]
assert config['permitted_axioms']==['propext','Classical.choice','Quot.sound']
for rel,shared in [('NLA/Statements/Infrastructure.lean','NLA/Statements/Infrastructure.lean'),('NLA/Statements/TR06.lean','NLA/Statements/TR06.lean'),('Reviewed/TR06.lean','Reviewed/TR06.lean')]:
 assert (CAN/rel).read_bytes()==(REPO/'lean-statements'/shared).read_bytes()
order=['NLA/Statements/Infrastructure.lean','NLA/Statements/TR06.lean','Reviewed/TR06.lean','NLA/TR06/Definitions.lean','Identity.lean','Challenge.lean']
source=HERE/'sources';objects=HERE/'objects';source.mkdir(exist_ok=True);objects.mkdir(exist_ok=True)
assert not list(objects.rglob('*.olean')),'Fresh private outputs are required.'
for rel in order:
 p=source/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes((CAN/rel).read_bytes())
consumer=source/'BoundaryConsumer.lean'
consumer.write_text('import Identity\nimport Challenge\nset_option leancert.trust "kernel"\n'+
 '#assert_trust kernel NLA.TR06.target_eq_reviewed\n#print axioms NLA.TR06.target_eq_reviewed\n'+
 '#assert_trust kernel NLA.Statements.TR06.Target\n#print axioms NLA.Statements.TR06.Target\n')
cache=REPO/'lean-statements/.lake/packages'
paths=[objects]+[p/'.lake/build/lib/lean'for p in sorted(cache.iterdir())if(p/'.lake/build/lib/lean').is_dir()]
env=dict(os.environ,PATH=str(LEAN.parent)+os.pathsep+os.environ['PATH'],LEAN_PATH=os.pathsep.join(map(str,paths)))
commands=[]
for rel in order+['BoundaryConsumer.lean']:
 output=objects/Path(rel).with_suffix('.olean');output.parent.mkdir(parents=True,exist_ok=True)
 p=subprocess.run([str(LEAN),'-o',str(output),rel],cwd=source,env=env,text=True,capture_output=True)
 log=HERE/(Path(rel).stem+'.log');log.write_text(p.stdout+p.stderr)
 commands.append({'source':rel,'source_sha256':digest(source/rel),'exit_code':p.returncode,'log_sha256':digest(log)})
 print(rel,p.returncode,flush=True)
 if p.returncode:print(p.stdout+p.stderr);break
status='PASS'if len(commands)==7 and all(x['exit_code']==0 for x in commands)else'FAIL'
if status=='PASS':
 text=(HERE/'Challenge.log').read_text()
 assert text.count("declaration uses `sorry`")==11,text
 assert not (CAN/'Solution.lean').exists()
 assert digest(LOCK)==initial_lock_hash
 for item in lock['records']:assert digest(CAN/item['path'])==item['sha256'],item['path']
result={'status':status,'scope':'Independent pre-Solution boundary source/type review, not proof approval or Linux/Comparator evidence. Challenge contains exactly eleven intentional specification placeholders.','boundary_lock_sha256':digest(LOCK),'input_count':70,'retained_source_exact_comparisons':116,'preserved_published_theorem_types':10,'added_intrinsic_target_type':1,'comparator_definition_holes':[],'Solution_absent_at_review':not(CAN/'Solution.lean').exists(),'commands':commands,'checks':checks,'lean_version':subprocess.check_output([str(LEAN),'--version'],text=True).strip(),'platform':platform.platform(),'project_objects_reused':False}
(HERE/'result.json').write_text(json.dumps(result,indent=2)+'\n')
raise SystemExit(0 if status=='PASS'else 1)
