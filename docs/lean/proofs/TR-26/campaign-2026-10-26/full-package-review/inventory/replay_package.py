#!/usr/bin/env python3
"""Compile exact package wrappers/controls using only hash-bound own fresh ECC80 objects."""
import argparse,ast,hashlib,json,os,shutil,subprocess
from pathlib import Path
p=argparse.ArgumentParser(description=__doc__)
for n in ['project','own-prefix','own-bindings','own-receipt','lean','packages','build','output']:p.add_argument('--'+n,type=Path,required=True)
p.add_argument('--commit',required=True)
p.add_argument('--expected-locked-inputs',type=int,required=True)
a=p.parse_args()
for k,v in vars(a).items():
 if isinstance(v,Path):setattr(a,k,v.resolve())
a.build.mkdir(parents=True,exist_ok=False);a.output.mkdir(parents=True,exist_ok=False)
sha=lambda b:hashlib.sha256(b).hexdigest();checks=[];commands=[];reused=[]
def check(n,v):checks.append(dict(name=n,passed=bool(v)));assert v,n
bindingdata=a.own_bindings.read_bytes();bindings=json.loads(bindingdata);receipt=json.loads(a.own_receipt.read_bytes())
check('own-reviewed-object-manifest',sha(bindingdata)=='fcd352e906ea5dc8c62b4eea134ec74c80ab04dec408c1f93678c8f3e68fde7b')
check('own-reviewed-source-completion',sha(a.own_receipt.read_bytes())=='59e6f2146bfd6d0a891d48aa14e53729f8dde2540c1d15c703c78e1ce218cd51' and receipt['passed'] and receipt['reviewer']=='/root/inventory' and receipt['immutable_commit']=='ecc597cb68b65b473aecce9ac635e27d35c09694')
manifest=json.loads((a.project/'lake-manifest.json').read_bytes());lock=json.loads((a.project/'PACKAGE_LOCK.json').read_bytes());before={q:sha((a.project/q).read_bytes()) for q in lock['files']}
check('all-locked-inputs',len(before)==a.expected_locked_inputs and all(before[q]==v['sha256'] for q,v in lock['files'].items()))
def pins():
 arr=[]
 for z in manifest['packages']:
  d=a.packages/z['name'];h=subprocess.check_output(['git','rev-parse','HEAD'],cwd=d).decode().strip();s=subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=d).decode();check('pinned-clean:'+z['name'],h==z['rev'] and s=='');arr.append(dict(name=z['name'],revision=h,tracked_clean=s==''))
 return arr
pins_before=pins();version=subprocess.check_output([str(a.lean),'--version']).decode();check('same-official4331-compiler',sha(a.lean.read_bytes())==receipt['lean_executable_sha256'] and 'version 4.33.1,' in version)
# Use the actual canonical replay driver's selected runtime order, not a new broad glob.
tree=ast.parse((a.project/'reproduce.py').read_text());orders=[ast.literal_eval(n.value) for n in ast.walk(tree) if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='files' for t in n.targets)]
check('exactcanonical84runtimeorder',len(orders)==1 and len(orders[0])==84)
files=orders[0]
for q in files:
 if q.startswith(('NLA/','Reviewed/')):
  m=q[:-5].replace('/','.');b=(a.project/q).read_bytes();o=a.own_prefix/Path(q).with_suffix('.olean');r=bindings[m]
  check('ownsource-byte-exact:'+m,sha(b)==r['source_sha256'])
  check('ownobject-byte-exact:'+m,sha(o.read_bytes())==r['object_sha256'])
  to=a.build/Path(q).with_suffix('.olean');to.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(o,to)
  reused.append(dict(module=m,source_sha256=sha(b),object_sha256=sha(o.read_bytes()),own_origin=str(o),scope='Independent reviewer own previously fresh ECC source object; not a new compiler command.'))
check('all80ownobjects-only',len(reused)==80)
env=os.environ.copy();env['PATH']=str(a.lean.parent)+os.pathsep+env.get('PATH','');env['LEAN_PATH']=os.pathsep.join([str(a.build)]+[str(a.packages/x['name']/'.lake/build/lib/lean') for x in manifest['packages']]+[str(a.lean.parent.parent/'lib/lean')])
def run(name,source,root,expected,diagnostic=None):
 obj=a.build/(name+'.olean');cmd=[str(a.lean),'-R',str(root),'-o',str(obj),str(source)];r=subprocess.run(cmd,cwd=root,env=env,text=True,capture_output=True,timeout=600);b=(r.stdout+r.stderr).encode();log=a.output/(name+'.log');log.write_bytes(b);ok=r.returncode==expected and (diagnostic is None or diagnostic in b.decode());commands.append(dict(name=name,argv=cmd,source_sha256=sha(source.read_bytes()),exit_code=r.returncode,expected_exit=expected,diagnostic=diagnostic,log_sha256=sha(b)));print(name,r.returncode,flush=True);check('command:'+name,ok);return b.decode()
for q in files:
 if not q.startswith(('NLA/','Reviewed/')):run(q[:-5],a.project/q,a.project,0)
controlroot=a.build/'controls';controlroot.mkdir()
for n,d in [('ChallengeTrustRejection','sorryAx'),('DefinitionKindRejection','requires an actual theorem'),('CustomAxiomRejection','PackageOracle')]:
 b=(a.project/'controls'/(n+'.lean.txt')).read_bytes();source=controlroot/(n+'.lean');source.write_bytes(b);log=run(n,source,controlroot,1,d)
 if n=='ChallengeTrustRejection':check('all3actual-reference-holes-rejected',log.count('depends on sorry or unrecognized axioms')==3 and log.count('sorryAx: sorryAx')==3)
check('all-locked-inputs-remain-unchanged',before=={q:sha((a.project/q).read_bytes()) for q in before});pins_after=pins()
r=dict(reviewer='/root/inventory',scope=__doc__,package_input_commit=a.commit,new_compiler_commands=len(commands),own_prefix_objects_reused=len(reused),reused=reused,commands=commands,lean_version=version,lean_executable_sha256=sha(a.lean.read_bytes()),bindings_sha256=sha(bindingdata),source_receipt_sha256=sha(a.own_receipt.read_bytes()),canonical_driver_sha256=sha((a.project/'reproduce.py').read_bytes()),driver_sha256=sha(Path(__file__).read_bytes()),pins_before=pins_before,pins_after=pins_after,checks=checks,check_count=len(checks),passed=all(z['passed'] for z in checks),Linux=False,Comparator_pipeline=False,raw_kernel_replay=False,CI=False)
(a.output/'result.json').write_text(json.dumps(r,indent=2)+'\n');print('PASS',len(checks),'checks; own80 reused, four wrappers and actual3controls compiled')
