from pathlib import Path
from fractions import Fraction as F
import hashlib,json,re,subprocess,datetime
import jsonschema
P=Path(__file__).resolve().parent
S=P/'snapshot'; Q=S/'linear-systems-and-elimination/IE-14/lean'
A=P/'actual-run-artifact/verify-20260915T232613Z-3959'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((P/'SNAPSHOT-COMPLETE-MANIFEST.json').read_text())
tree={e['path']:e for e in json.loads((P/'GIT-TREE.json').read_text())['tree']}
checks=[]
def check(label,ok,detail=None):
 assert ok,label
 checks.append({'check':label,'passed':bool(ok),'detail':detail})
for f in manifest['files']:
 b=(S/f['path']).read_bytes()
 check('immutable-git-blob:'+f['path'],hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==tree[f['path']]['sha'] and hashlib.sha256(b).hexdigest()==f['sha256'])
r=json.loads((A/'result.json').read_text());run=json.loads((P/'RUN.json').read_text())
check('actual-run-head',run['head_sha']==r['repository_commit']==manifest['commit'])
check('actual-run-success',run['status']=='completed' and run['conclusion']=='success' and run['event']=='push')
for f,h in r['input_sha256'].items():check('actual-run-input:'+f,sha(Q/f)==h)
check('complete-project-input-set',set(r['input_sha256'])=={f[len(r['project'])+1:] for f,e in tree.items() if f.startswith(r['project']+'/') and e['type']=='blob'})
check('comparator-result',r['result']=='comparator-accepted')
check('source-lock',sha(S/'tools/lean/source-lock.json')==r['source_lock_sha256']==r['tool_receipt']['source_lock_sha256'])
check('linux-platform','linux' in r['tool_receipt']['lean_version'] and r['tool_receipt']['platform'].startswith('Linux-'))
config=json.loads((Q/'comparator.json').read_text())
check('actual-config',config==r['config'])
check('seven-targets',len(config['theorem_names'])==7 and len(set(config['theorem_names']))==7)
check('no-replaceable-definitions',config['definition_names']==[])
check('standard-axioms',set(config['permitted_axioms'])=={'propext','Classical.choice','Quot.sound'})
freeze=json.loads((Q/'reviews/statement-freeze.json').read_text())
for f,h in freeze['input_sha256'].items():check('frozen-statement:'+f,sha(Q/f)==h)
for f,h in freeze['independent_statement_reports'].items():check('frozen-referee:'+f,sha(Q/f)==h)
source=json.loads((Q/'reviews/final-source-inputs.json').read_text())
for f,h in source['input_sha256'].items():check('final-source-seal:'+f,sha(Q/f)==h)
proofs=sorted((Q/'NLA/IE14').glob('*.lean'))+[Q/'Solution.lean']
# Restricted here to the straightforward lexical structure used in this source;
# the actual Comparator/kernel result, not this token check, establishes closure trust.
def strip(t):
 return re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',t,flags=re.S))
for f in proofs:
 t=strip(f.read_text())
 check('source-no-holes-or-custom-axioms:'+str(f.relative_to(Q)),not re.search(r'\b(?:sorry|admit|axiom|native_decide)\b',t))
 check('no-Challenge-import:'+str(f.relative_to(Q)),not re.search(r'^import .*\bChallenge\b',t,re.M))
allproof='\n'.join(f.read_text() for f in proofs)
challenge=(Q/'Challenge.lean').read_text()
for name in config['theorem_names']:
 short=name.rsplit('.',1)[1]
 pattern=r'^theorem '+re.escape(short)+r'\b(.*?):='
 c=re.search(pattern,challenge,re.M|re.S);s=re.search(pattern,allproof,re.M|re.S)
 check('literal-signature:'+name,c is not None and s is not None and re.sub(r'\s+','',c.group(1))==re.sub(r'\s+','',s.group(1)))
cl=(A/'comparator.log').read_text()
for marker in ['Building Challenge','Building Solution','Build completed successfully (3642 jobs).','Running Lean default kernel on solution.','Lean default kernel accepts the solution','Your solution is okay!','EXIT_STATUS=0']:
 check('actual-comparator:'+marker,marker in cl)
for name in config['theorem_names']:
 check('actual-axioms:'+name,"'"+name+"' depends on axioms: [propext, Classical.choice, Quot.sound]" in cl)
for log,marker in [('negative-sorry.log',"Illegal axiom detected: 'sorryAx'"),('negative-native.log',"Illegal axiom detected: 'checked._native.native_decide.ax_1_1'"),('comparator-controls.log','PASS: all five Comparator regressions'),('kernel-controls.log','PASS: all three actual Comparator.runBuiltinKernel cases behaved as required'),('sandbox.log','Outer and export fixture contents unchanged; only designated build fixture written.')]:
 t=(A/log).read_text();check('actual-control:'+log,marker in t)
 if log.startswith('negative-'):check('rejection-exit:'+log,'EXIT_STATUS=1' in t)
 else:check('success-exit:'+log,'EXIT_STATUS=0' in t)
for name in ['build','export']:
 check('sandbox-mode:'+name,'MODE '+name+': exit=0' in (A/'sandbox.log').read_text())
check('nonroot-sandbox', 'Sandbox UID: 1001' in (A/'sandbox.log').read_text())
for marker in ['type_mismatch','simple_match','simple_mismatch','simple_axiom_issue','simple_kind_mismatch']:
 check('comparator-regression:'+marker,'PASS '+marker+':' in (A/'comparator-controls.log').read_text())
for marker in ['RETURN honest_with_inductives_and_quotients: accepted','RETURN invalid_raw_proof: rejected','RETURN quotient_postcheck_mismatch: rejected']:
 check('actual-kernel-control:'+marker,marker in (A/'kernel-controls.log').read_text())
for pkg in json.loads((Q/'lake-manifest.json').read_text())['packages']:
 check('actual-dependency:'+pkg['name'],pkg['rev'] in (A/'dependencies.log').read_text())
yaml=json.loads(subprocess.check_output(['/usr/bin/ruby','-rjson','-ryaml','-e','puts JSON.generate(YAML.safe_load(File.read(ARGV[0])))',str(Q/'formalization.yaml')]))
jsonschema.Draft7Validator(json.loads((S/'docs/lean/schema/v0.4.schema.json').read_text())).validate(yaml)
check('metadata-schema',True)
check('metadata-targets',set(x['declaration'] for x in yaml['status']['main_results'])==set(config['theorem_names']))
check('name-and-full-department',yaml['project']['authors']==['George Stepaniants'] and yaml['project']['affiliations']['George Stepaniants']=='Department of Computing and Mathematical Sciences, California Institute of Technology')
check('no-new-email-in-Lean-project',not any(re.search(r'[\w.+-]+@[\w.-]+\.[A-Za-z]{2,}',f.read_text()) for f in proofs+[Q/'formalization.yaml']))
for item in json.loads((P/'BASE-PRESERVATION.json').read_text()):check('published-base-preserved:'+item['path'],item['unchanged'])
# Fresh, independent exact rational transcription of input and literal updates.
def fib(n):
 a,b=0,1
 for _ in range(n):a,b=b,a+b
 return a
observations=[]
for n in range(4,15):
 L=[[F(1 if i==j else -1 if i-j in [1,2] else 0) for j in range(n)] for i in range(n)]
 U=[[F(fib(n+1)+1 if i==j else fib(i+2)) if j==n-1 else F(1,2) if i==j==1 or (i,j)==(0,1) else F(1) if i==j else F(0) for j in range(n)] for i in range(n)]
 C=[[sum(L[i][a]*U[a][j] for a in range(n)) for j in range(n)] for i in range(n)]
 label=lambda i:0 if i==0 else 1 if i==n-1 else i+1
 B=[C[label(i)][:] for i in range(n)]
 check('witness-pattern:'+str(n),all(B[i][j]==0 for i in range(n) for j in range(n) if abs(i-j)>1 and (i,j) not in [(0,n-1),(n-1,0)]))
 check('witness-normalization:'+str(n),max(abs(x) for row in B for x in row)==1 and B[0][-1]==1 and B[-1][0]==-1)
 actual=B;orig=list(range(n));peak=F(0);pivots=[];order=[]
 for k in range(n):
  p=0 if k==0 else n-1
  z=actual[p][k]
  check('actual-pivot:'+str((n,k)),z!=0 and abs(z)==max(abs(actual[i][k]) for i in range(k,n)))
  pivots.append(z);order.append(orig[p]);peak=max(peak,max(abs(actual[i][j]) for i in range(k,n) for j in range(k,n)))
  for i in range(k,n):
   fi=label(i) if k==0 else k if i==n-1 else i+1
   check('actual-tail:'+str((n,k,i)),all(actual[i][j]==sum(L[fi][a]*U[a][j] for a in range(k,n)) for j in range(k,n)))
  actual[k],actual[p]=actual[p],actual[k];orig[k],orig[p]=orig[p],orig[k]
  actual=[[actual[i][j]-actual[i][k]/actual[k][k]*actual[k][j] if i>k and j>k else F(0) for j in range(n)] for i in range(n)]
 check('actual-witness-growth:'+str(n),peak==fib(n+1)+1 and pivots[-1]==fib(n+1)+1 and order==[0,n-1]+list(range(1,n-1)))
 observations.append({'n':n,'growth':str(peak),'pivots':[str(x) for x in pivots],'original_pivot_labels_zero_based':order})
report={'reviewer':'/root/next_matrix_functions','reviewed_commit':manifest['commit'],'actual_run_id':run['id'],'actual_job_id':104603738111,'generated_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'checks':checks,'count':len(checks),'immutable_snapshot_files':len(manifest['files']),'actual_run_inputs':len(r['input_sha256']),'exact_diagnostics':observations,'diagnostic_limit':'Finite rational checks only; universal proof established by reviewed source and actual remote Comparator/kernel acceptance. No local Lean, Lake, cache or proof build was executed.','artifact_sha256':{f.relative_to(P).as_posix():sha(f) for f in (P/'actual-run-artifact').rglob('*') if f.is_file()}}
(P/'CHECKS.json').write_text(json.dumps(report,indent=2)+'\n')
print('PASS',len(checks),'checks;',len(r['input_sha256']),'run inputs;',len(observations),'independent rational witnesses')
print('CHECKS SHA256',sha(P/'CHECKS.json'))
