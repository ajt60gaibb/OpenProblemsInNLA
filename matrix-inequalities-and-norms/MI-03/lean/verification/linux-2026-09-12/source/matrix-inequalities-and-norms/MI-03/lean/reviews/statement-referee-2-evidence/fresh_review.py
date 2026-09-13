"""Independent MI-03 statement referee 2 fresh-source check.
Adapted from this referee's prior separate-prefix NLA reviews. No proof work.
"""
from pathlib import Path
import datetime,hashlib,json,os,platform,re,subprocess,tempfile,time
OUT=Path(__file__).resolve().parent
P=OUT.parents[1]
BIN=Path('/Users/georgestepaniants/.elan/toolchains/leanprover--lean4---v4.33.1/bin')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def put(name,obj):(OUT/name).write_text(json.dumps(obj,indent=2)+'\n')
def run(argv,cwd=P):return subprocess.run(argv,cwd=cwd,check=True,capture_output=True,text=True).stdout.strip()
assert not (P/'Solution.lean').exists()
assert list((P/'NLA/MI03').glob('*.lean'))==[P/'NLA/MI03/Definitions.lean']
pins=[]
for x in json.loads((P/'lake-manifest.json').read_text())['packages']:
 d=P/'.lake/packages'/x['name'];head=run(['git','rev-parse','HEAD'],d);status=run(['git','status','--porcelain'],d)
 assert head==x['rev'] and not status,x['name']
 pins.append({'name':x['name'],'head':head,'pinned':x['rev'],'status':status})
assert len(pins)==10;put('pins.json',pins)
old=run([str(BIN/'lake'),'env','printenv','LEAN_PATH'])
old_project=(P/'.lake/build/lib/lean').resolve()
parts=[part for part in old.split(os.pathsep) if Path(part).resolve()!=old_project]
assert len(parts)==len(old.split(os.pathsep))-1
prefix=Path(tempfile.mkdtemp(prefix='mi03-statement-referee-2-'))
env=dict(os.environ);env['LEAN_PATH']=os.pathsep.join([str(prefix)]+parts)
checks={'independent_reviewer':'/root/leancert_examples','phase':'Statements before proofs','date_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'platform':platform.platform(),'lean_version':run([str(BIN/'lean'),'--version']),'fresh_prefix':str(prefix),'old_project_objects_excluded':str(old_project),'LEAN_PATH':env['LEAN_PATH'],'scope':'Fresh macOS statements and actual declarations; pinned dependency artifacts reused; no Linux/Comparator or full dependency rebuild','commands':[]}
for source,label,holes,produce in [('NLA/MI03/Definitions.lean','definitions',0,True),('Challenge.lean','challenge',8,True),('reviews/statement-referee-2-evidence/Inspect.lean','inspection',0,False)]:
 argv=[str(BIN/'lean')];artifacts=[]
 if produce:
  for flag,ext in [('-o','.olean'),('-i','.ilean')]:
   path=prefix/Path(source).with_suffix(ext);path.parent.mkdir(parents=True,exist_ok=True);argv.extend([flag,str(path)]);artifacts.append(path)
 argv.append(source);print('Fresh',source,flush=True)
 start=time.monotonic();r=subprocess.run(argv,cwd=P,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);log=OUT/(label+'.log');log.write_bytes(r.stdout)
 checks['commands'].append({'argv':argv,'source':source,'source_sha256':sha(P/source),'exit_code':r.returncode,'seconds':time.monotonic()-start,'log':log.name,'log_sha256':sha(log),'objects':{str(f.relative_to(prefix)):sha(f) for f in artifacts if f.exists()}})
 put('fresh-checks.json',checks);assert r.returncode==0,(label,str(log))
 assert r.stdout.count(b'warning:')==holes,r.stdout.decode()
 assert r.stdout.count(b'declaration uses `sorry`')==holes
 print('PASS',label,flush=True)
axioms=[]
for name,body in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",(OUT/'inspection.log').read_text()):
 a={s.strip() for s in body.split(',') if s.strip()};assert a=={'propext','Classical.choice','Quot.sound'},(name,a);axioms.append({'name':name,'axioms':sorted(a)})
assert len(axioms)==20;put('axioms.json',{'count':20,'all_standard_three':True,'records':axioms,'scope':'Definitions only; intentional Challenge theorems are not certified'})
print('PASS: three fresh commands; exactly eight deliberate Challenge holes; twenty definition kernel/axiom checks; ten clean pins',flush=True)
