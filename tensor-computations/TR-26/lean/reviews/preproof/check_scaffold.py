from pathlib import Path
import argparse,os,subprocess,hashlib,json,datetime
p=argparse.ArgumentParser();p.add_argument('--packet',type=Path,required=True);p.add_argument('--lean',type=Path,required=True);p.add_argument('--packages',type=Path,required=True);p.add_argument('--build',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
a.build.mkdir(parents=True,exist_ok=False);a.output.mkdir(parents=True,exist_ok=False)
source=a.build/'source';out=a.build/'out';source.mkdir();out.mkdir()
own=[('NLA.Statements.Infrastructure','lean-statements/NLA/Statements/Infrastructure.lean'),('NLA.Statements.TR26','lean-statements/NLA/Statements/TR26.lean'),('Reviewed.TR26','lean-statements/Reviewed/TR26.lean')]
env=os.environ.copy();env['LEAN_PATH']=':'.join([str(out)]+[str(q/'.lake/build/lib/lean') for q in sorted(a.packages.iterdir()) if (q/'.lake/build/lib/lean').is_dir()]+[str(a.lean.parent.parent/'lib/lean')])
records=[]
def run(module,data,expected=0):
 f=source/(module.replace('.','/')+'.lean');f.parent.mkdir(parents=True,exist_ok=True);f.write_bytes(data)
 obj=out/(module.replace('.','/')+'.olean');obj.parent.mkdir(parents=True,exist_ok=True)
 argv=[str(a.lean),'-R',str(source),'-o',str(obj),str(f)]
 r=subprocess.run(argv,cwd=source,env=env,text=True,capture_output=True,timeout=300)
 log=r.stdout+r.stderr;(a.output/(module+'.log')).write_text(log)
 records.append({'module':module,'source_sha256':hashlib.sha256(data).hexdigest(),'argv':argv,'exit_code':r.returncode,'expected_exit':expected,'log_sha256':hashlib.sha256(log.encode()).hexdigest()})
 print(module,r.returncode,flush=True)
 assert r.returncode==expected,log
 return log
for module,rel in own:run(module,(a.packet/'frozen'/rel).read_bytes())
run('Challenge',(a.packet/'Challenge.lean').read_bytes())
identity=b'''import NLA.Statements.TR26
import Reviewed.TR26
set_option autoImplicit false
set_option leancert.trust "kernel"
example : NLA.Statements.TR26.Target = NLA.ReviewedStatements.TR26.Target := rfl
'''
run('BoundaryIdentity',identity)
control=b'''import Challenge
#assert_trust kernel NLA.Proofs.TR26.nonisotropic_degree
#assert_trust kernel NLA.Proofs.TR26.isotropic_degree
#assert_trust kernel NLA.Proofs.TR26.target
'''
log=run('PlaceholderRejection',control,1)
assert log.count('depends on sorry or unrecognized axioms')==3 and 'sorryAx' in log
for n,d in [('BoundaryIdentity.lean.txt',identity),('PlaceholderRejection.lean.txt',control)]: (a.output/n).write_bytes(d)
(a.output/'result.json').write_text(json.dumps({'scope':'TR26 draft exact boundary elaboration/live-frozen identity and rejection of all three reference placeholders; no problem theorem proved; no implementation authorized','UTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'records':records,'passed':True,'all_three_reference_holes_rejected':True,'Lean_version':subprocess.check_output([str(a.lean),'--version'],text=True).strip()},indent=2)+'\n')
