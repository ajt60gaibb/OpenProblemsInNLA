#!/usr/bin/env python3
"""Independent immutable IE22 lower/support checkpoint build and kernel audit."""
import argparse,datetime,hashlib,json,os,re,subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent
REF='7660eae85e1636de38c85a5c103ff0480f971e05'
BASE='5487945e5a72abd952b0c89915915de8cc9b3e65'
STANDARD={'propext','Classical.choice','Quot.sound'}
def sha(b):return hashlib.sha256(b).hexdigest()
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--repo',type=Path,required=True);p.add_argument('--lean',type=Path,required=True);p.add_argument('--packages',type=Path,required=True);p.add_argument('--build',type=Path,required=True);a=p.parse_args()
 def git(*args):return subprocess.check_output(['git',*args],cwd=a.repo)
 def source(path,ref=REF):return git('show',ref+':'+path)
 assert not a.build.exists(),'Use a fresh private build directory'
 a.build.mkdir(parents=True);src=a.build/'source';out=a.build/'out';src.mkdir();out.mkdir();logs=HERE/'logs';logs.mkdir(exist_ok=True);saved=HERE/'sources';saved.mkdir(exist_ok=True)
 checks=[]
 def check(name,ok,**e):checks.append(dict(name=name,passed=bool(ok),**e))
 check('exact-immutable-checkpoint',git('rev-parse',REF).decode().strip()==REF)
 lock_path='docs/lean/proofs/IE-22/campaign-2026-10-23/preproof/INPUT_LOCK.json';lock=json.loads(source(lock_path));originals=[]
 for i in lock['reviewed_inputs']:
  b=source(i['path']);old=source(i['path'],BASE);frozen=source('docs/lean/proofs/IE-22/campaign-2026-10-23/preproof/frozen/'+i['path']);originals.append(dict(path=i['path'],sha256=sha(b),passed=b==old==frozen and sha(b)==i['sha256'] and len(b)==i['bytes']))
 check('all32-published-originals-ID-registry-and-statement-inputs-exact',len(originals)==32 and all(x['passed'] for x in originals))
 challenge=source('docs/lean/proofs/IE-22/campaign-2026-10-23/preproof/Challenge.lean')
 check('exact-preapproved-reference-boundary',sha(challenge)=='bd20cbb3d4495ff312192ab29fe7722463c8b74861f0a00ae83dd9b98ed4ec79')
 pins=[]
 manifest=json.loads(source('linear-systems-and-elimination/IE-22/lean/lake-manifest.json'))
 for pin in manifest['packages']:
  directory=a.packages/pin['name'];head=subprocess.check_output(['git','-C',str(directory),'rev-parse','HEAD']).decode().strip();clean=not subprocess.check_output(['git','-C',str(directory),'status','--porcelain','--untracked-files=no']);pins.append(dict(name=pin['name'],expected=pin['rev'],actual=head,tracked_clean=clean,passed=head==pin['rev'] and clean))
 check('ten-original-clean-immutable-dependency-pins',len(pins)==10 and all(x['passed'] for x in pins))
 version=subprocess.check_output([str(a.lean),'--version']).decode().strip();check('pinned-Lean4.33.1-compiler', '4.33.1' in version and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version)
 proof_paths=git('ls-tree','-r','--name-only',REF,'--','lean-statements/NLA/Proofs/IE22').decode().splitlines();check('exact14-proof-modules',len(proof_paths)==14)
 modules={};order=[];active=set()
 def imports(b):
  for line in b.decode().splitlines():
   m=re.match(r'\s*(?:public\s+)?import\s+(.+)',line)
   if m:
    yield from m[1].split('--',1)[0].split()
 def visit(name):
  if not name.startswith(('NLA.','Reviewed.')):return
  if name in modules:return
  assert name not in active,name
  active.add(name);b=source('lean-statements/'+name.replace('.','/')+'.lean')
  for child in imports(b):visit(child)
  active.remove(name);modules[name]=b;order.append(name)
 for path in proof_paths:visit(path[len('lean-statements/'):-5].replace('/','.'))
 visit('Reviewed.IE22')
 records=[];decls=[]
 for name,b in modules.items():
  rel=name.replace('.','/')+'.lean'
  for root in [src,saved]:
   path=root/rel;path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(b)
  records.append(dict(module=name,path='lean-statements/'+rel,sha256=sha(b),bytes=len(b),imports=list(imports(b))))
  if name.startswith('NLA.Proofs.IE22.'):
   clean=re.sub(r'/\-.*?\-/','',b.decode(),flags=re.S);clean=re.sub(r'--[^\n]*','',clean)
   assert not re.search(r'\b(?:axiom|sorry|admit|unsafe|native_decide)\b',clean),name
   assert 'set_option leancert.trust "kernel"' in clean,name
   assert re.findall(r'^namespace\s+(.+)$',clean,re.M)==['NLA.Proofs.IE22'],name
   for kind,label in re.findall(r'^(?:@\[[^\n]*\]\s*)?(theorem|lemma|def|abbrev)\s+([A-Za-z_][A-Za-z0-9_\']*)',clean,re.M):decls.append(dict(module=name,name='NLA.Proofs.IE22.'+label,kind='theorem' if kind in ['theorem','lemma'] else 'definition'))
 check('complete-owned18-module-source-closure',len(modules)==18 and len(order)==18)
 check('all14-source-modules-explicit-kernel-no-holes-custom-axioms-native-or-unsafe',len(decls)>0)
 env=os.environ.copy();deps=sorted(d/'.lake/build/lib/lean' for d in a.packages.iterdir() if (d/'.lake/build/lib/lean').is_dir());env['LEAN_PATH']=':'.join(map(str,[out]+deps+[a.lean.parent.parent/'lib/lean']))
 commands=[]
 def run(name,b,expected=0,obj=True):
  path=src/(name.replace('.','/')+'.lean');path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(b);retained=HERE/'consumers'/(name+'.lean.txt');retained.parent.mkdir(exist_ok=True);retained.write_bytes(b)
  argv=[str(a.lean),'-R',str(src)]
  if obj:
   op=out/(name.replace('.','/')+'.olean');op.parent.mkdir(parents=True,exist_ok=True);argv+=['-o',str(op)]
  argv.append(str(path));proc=subprocess.run(argv,cwd=src,env=env,capture_output=True,text=True,timeout=360);log=(proc.stdout+proc.stderr).encode();lp=logs/(name+'.log');lp.write_bytes(log);r=dict(module=name,argv=argv,exit_code=proc.returncode,expected_exit=expected,source_sha256=sha(b),log_sha256=sha(log));commands.append(r);print(name,proc.returncode,flush=True)
  if proc.returncode!=expected:
   print(log.decode(),flush=True);(HERE/'failed-command.json').write_text(json.dumps(r,indent=2)+'\n');raise RuntimeError(name+' unexpected exit')
  return log.decode()
 for name in order:run(name,modules[name])
 prefix='\n'.join('import '+n for n in order)+'\nset_option leancert.trust "kernel"\nopen Lean Elab Command\n'
 guards='''
elab "#review_theorem " target:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo target
  let info ← liftCoreM <| getConstInfo name
  match info with
  | .thmInfo _ => pure ()
  | _ => throwError "review requires an actual theorem: {name}"
elab "#review_definition " target:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo target
  let info ← liftCoreM <| getConstInfo name
  match info with
  | .defnInfo _ => pure ()
  | _ => throwError "review requires an actual definition: {name}"
'''
 audit=prefix+guards+'\n'.join('#review_'+d['kind']+' '+d['name']+'\n#assert_trust kernel '+d['name']+'\n#print axioms '+d['name'] for d in decls)+'\n'
 audit+='example : NLA.ReviewedStatements.IE22.Target ↔ NLA.Statements.IE22.Target := Iff.rfl\n'
 lower=challenge.decode().split('theorem near_sharp_unit_row_witness',1)[1].split(':= by',1)[0]
 audit+='open NLA.Statements.RowDeletion\nexample'+lower+':= NLA.Proofs.IE22.near_sharp_unit_row_witness θ a hθ0 hθ1 ha hquantile\n'
 audit+='run_cmd do\n  for n in [`NLA.Proofs.IE22.uniform_squared_upper, `NLA.Proofs.IE22.target] do\n    if (← getEnv).contains n then throwError "unapproved full endpoint present: {n}"\n'
 log=run('VerificationCheckpointAudit',audit.encode())
 closures={}
 for n,s in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log,re.S):closures.setdefault(n,[]).append([x.strip() for x in s.split(',') if x.strip()])
 check('all-explicit-declarations-theorem-or-definition-kind-and-kernel-checked',set(closures)=={d['name'] for d in decls} and all(len(v)==1 and set(v[0])<=STANDARD for v in closures.values()),declarations=len(decls),theorems=sum(d['kind']=='theorem' for d in decls),definitions=sum(d['kind']=='definition' for d in decls),closures=closures)
 check('exact-frozen-lower-full-type-and-reviewed-live-Target-identity',True,consumer_sha256=sha(audit.encode()))
 check('actual-upper-and-full-Target-proofs-absent',True)
 run('ReferenceHoles',challenge)
 negatives='import ReferenceHoles\nset_option leancert.trust "kernel"\n'+''.join('#assert_trust kernel NLA.Proofs.IE22.'+n+'\n' for n in ['uniform_squared_upper','near_sharp_unit_row_witness','target'])
 neglog=run('VerificationPlaceholderRejection',negatives.encode(),expected=1,obj=False)
 check('all-three-reference-holes-rejected-with-sorryAx',neglog.count('sorryAx')>=3 and all('NLA.Proofs.IE22.'+n in neglog for n in ['uniform_squared_upper','near_sharp_unit_row_witness','target']))
 fake='import NLA.Statements.IE22\n'+guards+'def VerificationFakeTheorem : True := True.intro\n#review_theorem VerificationFakeTheorem\n'
 kindlog=run('VerificationKindRejection',fake.encode(),expected=1,obj=False);check('theorem-kind-guard-rejects-proof-valued-definition','review requires an actual theorem' in kindlog)
 custom='import NLA.Statements.IE22\nset_option leancert.trust "kernel"\naxiom VerificationCustomAxiom : True\ntheorem VerificationTainted : True := VerificationCustomAxiom\n#assert_trust kernel VerificationTainted\n'
 customlog=run('VerificationCustomAxiomRejection',custom.encode(),expected=1,obj=False);check('kernel-trust-guard-rejects-custom-axiom','VerificationCustomAxiom' in customlog and 'error:' in customlog)
 postpins=[]
 for pin in pins:
  path=a.packages/pin['name'];head=subprocess.check_output(['git','-C',str(path),'rev-parse','HEAD']).decode().strip();clean=not subprocess.check_output(['git','-C',str(path),'status','--porcelain','--untracked-files=no']);postpins.append(head==pin['actual'] and clean)
 check('all-dependency-caches-remained-clean-at-original-pins',all(postpins))
 check('private-source-and-object-root-no-mutable-project-imports',all(str(a.packages) in str(d) for d in deps) and str(out)==env['LEAN_PATH'].split(':')[0])
 report=dict(reviewer='/root/verification (independent non-author OpenAI Codex AI agent)',UTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),checkpoint_commit=REF,scope='Exact near_sharp_unit_row_witness plus14 support modules; conditional assembly is not full Target',passed=all(c['passed'] for c in checks),checks=checks,source_records=records,declarations=decls,originals=originals,dependency_pins=pins,compiler_version=version,compiler_sha256=sha(a.lean.read_bytes()),private_build=str(a.build),LEAN_PATH=env['LEAN_PATH'],commands=commands,script_sha256=sha(Path(__file__).read_bytes()),proof_sources_authored=False,full_Target_approved=False,universal_upper_approved=False,Linux_Comparator_run=False)
 (HERE/'result.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(passed=report['passed'],checks=len(checks),source_modules=len(modules),proof_modules=len(proof_paths),declarations=len(decls),commands=len(commands),failed=[c['name'] for c in checks if not c['passed']]),indent=2));return 0 if report['passed'] else 1
if __name__=='__main__':raise SystemExit(main())
