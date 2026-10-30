#!/usr/bin/env python3
"""Independent fresh RE06 canonical candidate replay of91 runtime sources, own exact consumers and3 real controls; no Linux/Comparator claim."""
from pathlib import Path
import argparse,hashlib,io,json,os,re,subprocess,tempfile,datetime
p=argparse.ArgumentParser(description=__doc__);p.add_argument('--repo',type=Path,required=True);p.add_argument('--commit',required=True);p.add_argument('--expected-lock-sha256',required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--lean',type=Path,default=Path('/private/tmp/nla-oct23-lean-runtime/lean-4.33.1-darwin_aarch64/bin/lean'));p.add_argument('--packages',type=Path,default=Path('/Users/ajt253/.codex/worktrees/pf05-lean-proof/OpenProblemsInNLA/nonnegative-and-positive-factorizations/PF-05/lean/.lake/packages'));a=p.parse_args();o=a.output.resolve();o.mkdir(parents=True,exist_ok=False);P='randomized-and-low-rank-approximation/RE-06/lean/';sha=lambda b:hashlib.sha256(b).hexdigest();checks=[];records=[];objects={};error=None;before={};after={};version=''
def ck(n,v,**x):
 checks.append(dict(name=n,passed=bool(v),**x))
 if not v:raise AssertionError(n)
def fetch(paths):
 paths=list(dict.fromkeys(paths));s=io.BytesIO(subprocess.check_output(['git','cat-file','--batch'],input=''.join(a.commit+':'+P+q+'\n' for q in paths).encode(),cwd=a.repo));out={}
 for q in paths:
  h=s.readline().decode().strip().split();assert len(h)==3 and h[1]=='blob',(q,h);out[q]=s.read(int(h[2]));assert s.read(1)==b'\n'
 return out
head=fetch(['PACKAGE_LOCK.json','SOURCE_MAP.json','lake-manifest.json','comparator.json']);lock=json.loads(head['PACKAGE_LOCK.json']);mapping=json.loads(head['SOURCE_MAP.json']);manifest=json.loads(head['lake-manifest.json']);config=json.loads(head['comparator.json']);order=mapping['runtime_lean_order'];pkg=fetch(order+['controls/ChallengeTrustRejection.lean.txt','controls/DefinitionKindRejection.lean.txt','controls/CustomAxiomRejection.lean.txt']);ck('exact-immutable-lock-before-replay',sha(head['PACKAGE_LOCK.json'])==a.expected_lock_sha256);ck('exact91-runtime-positive-set',len(order)==len(set(order))==91 and mapping['proof_source_ref']=='181c365dc426875aaa61984c901478b1b7c696e6')
for q,b in pkg.items():ck('exact-locked-source:'+q,sha(b)==lock['files'][q]['sha256'] and len(b)==lock['files'][q]['bytes'])
public=config['theorem_names'];ck('six-public-theorems-empty-definitions',len(public)==6 and config['definition_names']==[])
aud=Path(__file__).resolve().with_name('InventoryPackageAudit.lean.txt').read_text();consumer=['Inventory.RE06.Package.'+n for n in ['consumeSVD','consumeQueries','consumeSuccess','consumeOriginal','consumeExplicit','consumeTarget','liveReviewedIdentity','consumeReviewedTarget']];selected=public+consumer
for n in selected:aud+='\n#inventory_theorem '+n+'\n#assert_trust kernel '+n+'\n#print axioms '+n+'\n'
negative={'Negative.ChallengeTrust':'controls/ChallengeTrustRejection.lean.txt','Negative.DefinitionKind':'controls/DefinitionKindRejection.lean.txt','Negative.CustomAxiom':'controls/CustomAxiomRejection.lean.txt'}
def heads():
 result={}
 for e in manifest['packages']:
  q=a.packages/e['name'];h=subprocess.check_output(['git','-C',str(q),'rev-parse','HEAD'],text=True).strip();st=subprocess.check_output(['git','-C',str(q),'status','--porcelain','--untracked-files=normal'],text=True);ck('exact-clean-dependency:'+e['name'],h==e['rev'] and st=='');result[e['name']]=h
 return result
try:
 before=heads();version=subprocess.check_output([str(a.lean),'--version'],text=True).strip();ck('official-Lean4331-commit','4.33.1' in version and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version)
 with tempfile.TemporaryDirectory(prefix='nla-re06-package-independent-',dir='/private/tmp') as tmp:
  t=Path(tmp);s=t/'source';b=t/'objects';s.mkdir();b.mkdir();ck('initial-own-project-objects-empty',not list(b.iterdir()));jobs=[]
  for q in order:
   f=s/q;f.parent.mkdir(parents=True,exist_ok=True);f.write_bytes(pkg[q]);jobs.append((q,q.removesuffix('.lean').replace('/','.')))
  own='Inventory/PackageAudit.lean';f=s/own;f.parent.mkdir(parents=True,exist_ok=True);f.write_text(aud);jobs.append((own,'Inventory.PackageAudit'))
  for m,q in negative.items():
   rel=m.replace('.','/')+'.lean';f=s/rel;f.parent.mkdir(parents=True,exist_ok=True);f.write_bytes(pkg[q]);jobs.append((rel,m))
  env=os.environ.copy();env['LEAN_PATH']=':'.join([str(b)]+[str(a.packages/e['name']/'.lake/build/lib/lean') for e in manifest['packages']]+[str(a.lean.parent.parent/'lib/lean')]);env.pop('LEAN_SRC_PATH',None)
  for q,m in jobs:
   f=s/q;ob=b/(m.replace('.','/')+'.olean');ob.parent.mkdir(parents=True,exist_ok=True);argv=[str(a.lean),'-R',str(s),'-o',str(ob),str(f)];run=subprocess.run(argv,cwd=s,env=env,capture_output=True,text=True,timeout=900);log=run.stdout+run.stderr
   if m=='Negative.ChallengeTrust':passed=run.returncode!=0 and log.count('error: #assert_trust:')==6 and log.count('sorryAx: sorryAx')==6 and 'Unknown' not in log and 'unknown' not in log
   elif m=='Negative.DefinitionKind':passed=run.returncode!=0 and 'expected actual theorem declaration' in log and 'Unknown' not in log
   elif m=='Negative.CustomAxiom':passed=run.returncode!=0 and 'error: #assert_trust:' in log and 'PackageOracle' in log and 'Unknown' not in log
   else:passed=run.returncode==0
   dest=o/'sources'/(q+'.txt');dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(f.read_bytes());(o/(m+'.log')).write_text(log);records.append({'module':m,'command':argv,'source_sha256':sha(f.read_bytes()),'log_sha256':sha(log.encode()),'exit_code':run.returncode,'expected_negative':m in negative,'warning_count':log.count('warning:'),'passed':passed});print(m,'PASS' if passed else 'FAIL',flush=True);ck('actual-Lean-outcome:'+m,passed)
   if ob.exists():objects[m]={'sha256':sha(ob.read_bytes()),'bytes':ob.stat().st_size}
   if m=='Inventory.PackageAudit':
    ax=re.findall(r"'([^']+)' (?:(?:depends on axioms:\s*\[([^\]]*)\])|(?:does not depend on any axioms))",log);ck('all6public-and8literal-kinds-kernel-standard-axioms',len(ax)==14 and [n for n,x in ax]==selected and all(set(v.strip() for v in x.split(',') if v.strip())<={'propext','Classical.choice','Quot.sound'} for n,x in ax))
 after=heads();ck('clean-identical-dependencies-before-after',before==after)
except Exception as e:error=str(e)
j={'reviewer':'/root/inventory','authored_RE06_proof_sources':[],'scope':'Independent local macOS canonical candidate replay; package fidelity only, separate full-source and actual Linux/Comparator acceptance required.','UTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'commit':a.commit,'proof_source_ref':mapping['proof_source_ref'],'package_lock_sha256':sha(head['PACKAGE_LOCK.json']),'source_map_sha256':sha(head['SOURCE_MAP.json']),'passed':error is None and len(records)==95 and all(x['passed'] for x in records),'error':error,'check_count':len(checks),'checks':checks,'expected_outcomes':95,'runtime_source_builds':91,'own_literal_audit_builds':1,'actual_negative_commands':3,'literal_consumers':8,'selected_public_theorems':public,'selected_genuine_theorems':selected,'commands':records,'fresh_empty_project_objects':True,'borrowed_author_project_objects':False,'pinned_dependency_cache_used':True,'fresh_dependency_rebuild_claimed':False,'project_objects_removed_after_replay':True,'object_sha256':objects,'dependency_heads_before':before,'dependency_heads_after':after,'lean_version':version,'lean_binary_sha256':sha(a.lean.read_bytes()),'driver_sha256':sha(Path(__file__).read_bytes()),'consumer_template_sha256':sha(Path(__file__).with_name('InventoryPackageAudit.lean.txt').read_bytes())};(o/'RESULT.json').write_text(json.dumps(j,indent=2)+'\n');print(json.dumps({k:j[k] for k in ['passed','error','check_count']}));raise SystemExit(0 if j['passed'] else 1)
