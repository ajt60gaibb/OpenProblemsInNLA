#!/usr/bin/env python3
"""Fresh statement/signature/identity replay and six real hole rejections.
No RE-06 mathematical proof is created or checked by this author-only driver.
"""
from pathlib import Path
import argparse,hashlib,json,os,subprocess,tempfile
ap=argparse.ArgumentParser()
ap.add_argument('--packet',type=Path,default=Path(__file__).resolve().parent)
ap.add_argument('--lean',type=Path,default=Path('/private/tmp/nla-oct23-lean-runtime/lean-4.33.1-darwin_aarch64/bin/lean'))
ap.add_argument('--packages',type=Path,default=Path('/Users/ajt253/.codex/worktrees/pf05-lean-proof/OpenProblemsInNLA/nonnegative-and-positive-factorizations/PF-05/lean/.lake/packages'))
ap.add_argument('--output',type=Path,required=True)
a=ap.parse_args();packet=a.packet.resolve();a.output.mkdir(parents=True,exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
lock=json.loads((packet/'INPUT_LOCK.json').read_text())
for row in lock['files']:
 assert sha(packet/'originals'/row['path'])==row['sha256'],row['path']
exports=json.loads((packet/'EXPORTS.json').read_text())['exports']
assert len(exports)==6
manifest=json.loads((packet/'originals/lean-statements/lake-manifest.json').read_text())
dep_heads={}
for pkg in manifest['packages']:
 path=a.packages/pkg['name']
 head=subprocess.check_output(['git','-C',str(path),'rev-parse','HEAD'],text=True).strip()
 assert head==pkg['rev'],(pkg['name'],head,pkg['rev'])
 dep_heads[pkg['name']]=head
version=subprocess.check_output([str(a.lean),'--version'],text=True).strip()
assert '4.33.1' in version,version
records=[]
with tempfile.TemporaryDirectory(prefix='nla-re06-scaffold-',dir='/private/tmp') as tmp:
 tmp=Path(tmp);source=tmp/'source';out=tmp/'out';source.mkdir();out.mkdir()
 for row in lock['files']:
  p=row['path']
  if p.startswith('lean-statements/') and p.endswith('.lean'):
   rel=Path(p).relative_to('lean-statements');dest=source/rel
   dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes((packet/'originals'/p).read_bytes())
 common='import NLA.Statements.RE06\n\nset_option autoImplicit false\nset_option leancert.trust "kernel"\n\n'
 sig=common+'namespace NLA.Preproof.RE06\n\n'
 for e in exports:
  prop=('∀ '+e['binders']+',\n    ' if e['binders'] else '')+e['type']
  sig+=f"def {e['name']}_type : Prop :=\n    {prop}\n\n#assert_statement {e['name']}_type\n#assert_trust kernel {e['name']}_type\n\n"
 sig+='end NLA.Preproof.RE06\n'
 identity='''import NLA.Statements.RE06
import Reviewed.RE06
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace NLA.Preproof.RE06
 theorem live_frozen_identity : NLA.Statements.RE06.Target = NLA.ReviewedStatements.RE06.Target := rfl
#assert_trust kernel live_frozen_identity
#print axioms live_frozen_identity
end NLA.Preproof.RE06
'''
 (source/'Scaffold').mkdir()
 (source/'Scaffold/Signatures.lean').write_text(sig)
 (source/'Scaffold/Identity.lean').write_text(identity)
 (source/'Challenge.lean').write_bytes((packet/'Challenge.lean').read_bytes())
 for e in exports:
  text=common+'namespace NLA.Proofs.RE06\n\n'
  text+=f"theorem {e['name']} {e['binders']} :\n    {e['type']} := by\n  sorry\n\n"
  text+=f"#assert_trust kernel {e['name']}\n#print axioms {e['name']}\nend NLA.Proofs.RE06\n"
  (source/f"Scaffold/Hole_{e['name']}.lean").write_text(text)
 env=os.environ.copy()
 env['LEAN_PATH']=':'.join([str(out)]+[str(p/'.lake/build/lib/lean') for p in sorted(a.packages.iterdir()) if (p/'.lake/build/lib/lean').is_dir()]+[str(a.lean.parent.parent/'lib/lean')])
 success=['NLA.Computation.SVDMachine','NLA.Computation.NonadaptiveMatrixQuery','NLA.Statements.Infrastructure','NLA.Statements.RE06','Reviewed.RE06','Scaffold.Signatures','Scaffold.Identity']
 cases=[(m,False) for m in success]+[(f"Scaffold.Hole_{e['name']}",True) for e in exports]+[('Challenge',True)]
 for module,negative in cases:
  src=source/(module.replace('.','/')+'.lean');obj=out/(module.replace('.','/')+'.olean');obj.parent.mkdir(parents=True,exist_ok=True)
  argv=[str(a.lean),'-R',str(source),'-o',str(obj),str(src)]
  p=subprocess.run(argv,cwd=source,env=env,capture_output=True,text=True,timeout=300)
  log=p.stdout+p.stderr
  expected=6 if module=='Challenge' else 1
  passed=(p.returncode!=0 and log.count('error: #assert_trust:')==expected and 'sorryAx' in log) if negative else p.returncode==0
  dest=a.output/'sources'/(module.replace('.','/')+'.lean.txt');dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(src.read_bytes())
  (a.output/(module+'.log')).write_text(log)
  rec={'module':module,'scope':'intentional mathematical hole rejection' if negative else 'statement/signature/identity only','source_sha256':sha(src),'argv':argv,'exit_code':p.returncode,'expected_failure':negative,'kernel_hole_rejections':log.count('error: #assert_trust:'),'passed':passed}
  records.append(rec)
  print(module,'PASS' if passed else 'FAIL',flush=True)
  if not passed:print(log,flush=True);break
for name,head in dep_heads.items():
 assert subprocess.check_output(['git','-C',str(a.packages/name),'rev-parse','HEAD'],text=True).strip()==head
report={'scope':'AUTHOR scaffold evidence only. No mathematical RE-06 theorem or independent review/approval; no CI or Comparator claim.','published_base':lock['published_base'],'lean_version':version,'lean_sha256':sha(a.lean),'external_dependency_heads':dep_heads,'fresh_project_objects':True,'project_local_source_count':5,'challenge_sha256':sha(packet/'Challenge.lean'),'exports_sha256':sha(packet/'EXPORTS.json'),'records':records,'passed':len(records)==14 and all(r['passed'] for r in records)}
(a.output/'RESULT.json').write_text(json.dumps(report,indent=2)+'\n')
raise SystemExit(0 if report['passed'] else 1)
