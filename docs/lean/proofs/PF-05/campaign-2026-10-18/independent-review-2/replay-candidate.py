from pathlib import Path
import hashlib,json,subprocess,os,re
r=Path('/private/tmp/nla-tr14-lean-oct18');e=Path(__file__).parent;snap=e/'candidate-snapshot';out=e/'objects';out.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
mods=['NLA.Statements.Infrastructure','NLA.Statements.PF05','Reviewed.PF05','Challenge','Check','NLA.Proofs.PF05.Basic','NLA.Proofs.PF05.Congruence','NLA.Proofs.PF05.Operator','NLA.Proofs.PF05.ZeroPair','NLA.Proofs.PF05.ZeroNormalize','NLA.Proofs.PF05.PositiveReduction','NLA.Proofs.PF05.PositiveTopology']
bin=Path('/private/tmp/pf05-tooling/elan-home/toolchains/leanprover--lean4---v4.33.1/bin');packages=r/'lean-statements/.lake/packages';paths=[out]+[p/'.lake/build/lib/lean' for p in packages.iterdir() if(p/'.lake/build/lib/lean').is_dir()];env=dict(os.environ,PATH=str(bin)+':'+os.environ['PATH'],LEAN_PATH=':'.join(map(str,paths)))
j={'date':'2026-10-18','reviewer':'/root/fr05_statement','candidate_commit':'6e2c960557b6f61af1ed6e679b0634dd498181b2','pins':[],'commands':[],'boundary_equalities':[]}
for p in packages.iterdir():
 if (p/'.git').exists():j['pins'].append({'name':p.name,'revision':subprocess.check_output(['git','-C',str(p),'rev-parse','HEAD'],text=True).strip()})
for name in ['NLA/Statements/Infrastructure.lean','NLA/Statements/PF05.lean','Reviewed/PF05.lean']:
 j['boundary_equalities'].append({'path':name,'candidate_sha256':sha(snap/name),'shared_sha256':sha(r/'lean-statements'/name),'equal':(snap/name).read_bytes()==(r/'lean-statements'/name).read_bytes()})
assert all(x['equal'] for x in j['boundary_equalities'])
if (e/'build-result.json').exists():
 j['commands']=json.loads((e/'build-result.json').read_text())['commands']
def runfile(source,expected=0):
 obj=out/source.with_suffix('.olean');obj.parent.mkdir(parents=True,exist_ok=True)
 cmd=[str(bin/'lean'),'-o',str(obj),str(source)];run=subprocess.run(cmd,cwd=snap,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 log=e/(str(len(j['commands']))+'-'+source.stem+'.log');log.write_text(run.stdout);j['commands'].append({'source':str(source),'sha256':sha(snap/source),'command':cmd,'cwd':str(snap),'exit_code':run.returncode,'expected_exit_code':expected,'log':log.name,'log_sha256':sha(log),'object_sha256':sha(obj) if obj.exists() else None});print(source,run.returncode,run.stdout.strip() if run.returncode else '',flush=True);(e/'build-result.json').write_text(json.dumps(j,indent=2)+'\n');assert run.returncode==expected
 return run.stdout
for m in mods:
 p=Path(m.replace('.','/')+'.lean')
 if any(x['source']==str(p) and x['exit_code']==0 and x['sha256']==sha(snap/p) and x['object_sha256']==sha(out/p.with_suffix('.olean')) for x in j['commands']):continue
 runfile(p)
def strip_comments(s):
 out=[];i=0;depth=0
 while i<len(s):
  if s[i:i+2]=='/-':depth+=1;i+=2;continue
  if depth and s[i:i+2]=='-/':depth-=1;i+=2;continue
  if not depth and s[i:i+2]=='--':
   while i<len(s) and s[i]!='\n':i+=1
   continue
  if not depth or s[i]=='\n':out.append(s[i])
  i+=1
 return ''.join(out)
ns=[];names=[]
for m in mods[-7:]:
 ns=[]
 for line in strip_comments((snap/(m.replace('.','/')+'.lean')).read_text()).splitlines():
  match=re.match(r'namespace\s+([\w.]+)',line)
  if match:ns.append(match.group(1));continue
  if re.match(r'end(?:\s+|$)',line):
   if ns:ns.pop()
   continue
  match=re.match(r'(?:@\[[^\n]*\]\s*)?(?:noncomputable\s+)?(?:theorem|lemma|def|abbrev|structure)\s+([\w]+)',line)
  if match:names.append('.'.join(ns+[match.group(1)]))
consumer=Path('SupportKernelAudit.lean');(snap/consumer).write_text(''.join('import '+m+'\n' for m in mods[-7:])+'set_option leancert.trust "kernel"\n'+''.join('#assert_trust kernel '+n+'\n#print axioms '+n+'\n' for n in names))
stdout=runfile(consumer);assert 'sorryAx' not in stdout;j['audited_declarations']=names
negative=Path('ChallengeKernelNegative.lean');(snap/negative).write_text('import Challenge\n#assert_trust kernel NLA.PF05.target\n');stdout=runfile(negative,1);assert 'sorry' in stdout
j['resolved_harness_attempts']=[x for x in j['commands'] if x['exit_code']!=x['expected_exit_code']];j['pass']=True;j['scope']='Exact boundary and retained support replay only; Challenge is intentionally rejected by kernel negative test. No new mathematical proof bodies, no Solution and no proof of Target.';(e/'build-result.json').write_text(json.dumps(j,indent=2)+'\n')
