#!/usr/bin/env python3
"""Independent canonical IE22 wrapper replay using hash-identical fresh shared objects."""
import argparse,datetime,hashlib,json,os,re,subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent
REF='577846438f6cdb80bf237fc190021ddafd7a24a5'
DESC='06f31cdd4f76d90c7590b5582b8db4975a0055d8'
SHARED='353ebcfcbbcfc08184c32f391ecb6068c7d9098f'
BASE='5487945e5a72abd952b0c89915915de8cc9b3e65'
PROJECT='linear-systems-and-elimination/IE-22/lean'
AXIOMS=['propext','Classical.choice','Quot.sound']
ENDPOINTS=['uniform_squared_upper','near_sharp_unit_row_witness','target']
def sha(b):return hashlib.sha256(b).hexdigest()
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--repo',type=Path,required=True);p.add_argument('--build',type=Path,required=True);a=p.parse_args()
 def git(*args):return subprocess.check_output(['git',*args],cwd=a.repo)
 def source(path,ref=REF):return git('show',ref+':'+path)
 checks=[]
 def check(n,ok,**e):checks.append(dict(name=n,passed=bool(ok),**e))
 sharedpath=HERE.parent/'result.json';shared=json.loads(sharedpath.read_text());check('separate-fresh-shared23-review-passed',shared['passed'] and shared['checkpoint_commit']==SHARED and len(shared['source_records'])==23)
 assert not a.build.exists(),'Use a fresh private canonical build directory'
 a.build.mkdir(parents=True);src=a.build/'source';out=a.build/'out';src.mkdir();out.mkdir();(HERE/'logs').mkdir(exist_ok=True);(HERE/'sources').mkdir(exist_ok=True)
 def paths(ref):return [x[len(PROJECT)+1:] for x in git('ls-tree','-r','--name-only',ref,'--',PROJECT).decode().splitlines()]
 files=paths(REF);descfiles=paths(DESC);inputs={rel:sha(source(PROJECT+'/'+rel)) for rel in files};descinputs={rel:sha(source(PROJECT+'/'+rel,DESC)) for rel in descfiles}
 check('exact27-canonical-Lean-files',sum(n.endswith('.lean') for n in files)==27)
 check('descendant06-adds-only-exact-original-comparator-text-archive',set(descfiles)-set(files)=={'original-scaffold/comparator.json.txt'} and not(set(files)-set(descfiles)) and all(descinputs[n]==h for n,h in inputs.items()) and source(PROJECT+'/original-scaffold/comparator.json.txt',DESC)==source(PROJECT+'/comparator.json',BASE))
 for rel in files:
  b=source(PROJECT+'/'+rel);saved=HERE/'sources'/rel;saved.parent.mkdir(parents=True,exist_ok=True);saved.write_bytes(b)
  if rel.endswith('.lean'):
   q=src/rel;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(b)
 copies=[]
 private_shared=Path(shared['private_build']);sourcerecords={r['module']:r for r in shared['source_records']}
 for module,r in sourcerecords.items():
  rel=module.replace('.','/')+'.lean';b=source(PROJECT+'/'+rel);obj=private_shared/'out'/(module.replace('.','/')+'.olean')
  copies.append(dict(module=module,source_sha256=sha(b),shared_source_sha256=r['sha256'],private_object_sha256=sha(obj.read_bytes()),passed=sha(b)==r['sha256']==sha(source(r['path'],SHARED))==sha((private_shared/'source'/rel).read_bytes())))
 check('all23-canonical-copies-exact-shared353-and-private-objects',len(copies)==23 and all(i['passed'] for i in copies))
 config=json.loads(source(PROJECT+'/comparator.json'));expected=dict(challenge_module='Challenge',solution_module='Solution',theorem_names=['NLA.Proofs.IE22.'+n for n in ENDPOINTS],definition_names=[],permitted_axioms=AXIOMS)
 check('exact-three-full-endpoint-Comparator-selection-standard-axioms-no-definition-holes',config==expected)
 challenge=source(PROJECT+'/Challenge.lean');check('Challenge-exact-preapproved-three-signatures',sha(challenge)=='bd20cbb3d4495ff312192ab29fe7722463c8b74861f0a00ae83dd9b98ed4ec79')
 check('Definitions-byte-identical-original-and-Solution-does-not-import-Challenge',source(PROJECT+'/Definitions.lean')==source(PROJECT+'/Definitions.lean',BASE) and b'import Challenge' not in source(PROJECT+'/Solution.lean'))
 lock=json.loads(source('docs/lean/proofs/IE-22/campaign-2026-10-23/preproof/INPUT_LOCK.json'));preserved=[]
 for i in lock['reviewed_inputs']:
  old=source(i['path'],BASE);frozen=source('docs/lean/proofs/IE-22/campaign-2026-10-23/preproof/frozen/'+i['path']);preserved.append(dict(path=i['path'],sha256=sha(old),passed=old==frozen and sha(old)==i['sha256'] and len(old)==i['bytes']))
 check('all32-frozen-originals-and-published-identity-lock-preserved',all(i['passed'] for i in preserved) and len(preserved)==32)
 check('canonical-README-TeX-PDF-ID-registry-not-promoted-or-altered',all(source(p)==source(p,BASE) for p in ['problem_ids.json','linear-systems-and-elimination/IE-22/README.md','linear-systems-and-elimination/IE-22/problem.tex','linear-systems-and-elimination/IE-22/problem.pdf']))
 originalfiles=paths(BASE);archive=[]
 for rel in originalfiles:
  old=source(PROJECT+'/'+rel,BASE);options=[]
  if rel in descfiles and source(PROJECT+'/'+rel,DESC)==old:options.append('unchanged-canonical')
  archived='original-scaffold/'+rel+'.txt'
  if archived in descfiles and source(PROJECT+'/'+archived,DESC)==old:options.append(archived)
  frozen='docs/lean/proofs/IE-22/campaign-2026-10-23/preproof/frozen/'+PROJECT+'/'+rel
  if PROJECT+'/'+rel in {i['path'] for i in lock['reviewed_inputs']} and source(frozen)==old:options.append('locked-full-original-packet')
  archive.append(dict(path=rel,sha256=sha(old),preserved_at=options,passed=bool(options)))
 check('all-original-canonical-project-files-retained-byte-for-byte',all(i['passed'] for i in archive),files=len(archive))
 metadata=json.loads(source(PROJECT+'/formalization.yaml'));check('metadata-honestly-pending-CI-no-Lean-promotion',metadata['status']['phase']=='source-complete-awaiting-verification' and not metadata['status']['whole_problem_verified'] and metadata['status']['canonical_status']=='not Lean verified')
 packages=Path(shared['LEAN_PATH'].split(':')[1]).parents[4]
 pins=[]
 for pin in json.loads(source(PROJECT+'/lake-manifest.json'))['packages']:
  directory=packages/pin['name'];head=subprocess.check_output(['git','-C',str(directory),'rev-parse','HEAD']).decode().strip();clean=not subprocess.check_output(['git','-C',str(directory),'status','--porcelain','--untracked-files=no']);pins.append(dict(name=pin['name'],expected=pin['rev'],actual=head,tracked_clean=clean,passed=head==pin['rev'] and clean))
 check('original-ten-clean-dependency-pins',len(pins)==10 and all(i['passed'] for i in pins))
 lean=Path(shared['commands'][0]['argv'][0]);check('same-pinned-compiler-as-independent-shared-replay',sha(lean.read_bytes())==shared['compiler_sha256'])
 env=os.environ.copy();deps=sorted(d/'.lake/build/lib/lean' for d in packages.iterdir() if (d/'.lake/build/lib/lean').is_dir());env['LEAN_PATH']=':'.join(map(str,[out,private_shared/'out']+deps+[lean.parent.parent/'lib/lean']))
 commands=[]
 def run(name,data=None,expected_exit=0,obj=True):
  q=src/(name.replace('.','/')+'.lean')
  if data is not None:q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(data);(HERE/(name+'.lean.txt')).write_bytes(data)
  argv=[str(lean),'-R',str(src)]
  if obj:
   o=out/(name.replace('.','/')+'.olean');o.parent.mkdir(parents=True,exist_ok=True);argv+=['-o',str(o)]
  argv.append(str(q));proc=subprocess.run(argv,cwd=src,env=env,capture_output=True,text=True,timeout=240);log=(proc.stdout+proc.stderr).encode();(HERE/'logs'/(name+'.log')).write_bytes(log);commands.append(dict(module=name,argv=argv,exit_code=proc.returncode,expected_exit=expected_exit,source_sha256=sha(q.read_bytes()),log_sha256=sha(log)));print(name,proc.returncode,flush=True)
  if proc.returncode!=expected_exit:print(log.decode());raise RuntimeError(name)
  return log.decode()
 for name in ['Definitions','Challenge','Identity','Solution']:run(name)
 consumer='import Solution\nimport Identity\nset_option leancert.trust "kernel"\nopen Lean Elab Command\n'
 consumer+='''elab "#review_theorem " target:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo target
  let info ← liftCoreM <| getConstInfo name
  match info with
  | .thmInfo _ => pure ()
  | _ => throwError "actual theorem required: {name}"
'''
 names=config['theorem_names']+['NLA.Proofs.IE22.target_eq_reviewed','IE22.l2Sq_zero','IE22.rowEnergy_empty']
 for name in names:consumer+='#review_theorem '+name+'\n#assert_trust kernel '+name+'\n#print axioms '+name+'\n'
 consumer+='open NLA.Statements.RowDeletion\n'
 for endpoint in ENDPOINTS[:2]:
  header=challenge.decode().split('theorem '+endpoint,1)[1].split(':= by',1)[0];consumer+='example'+header+':= NLA.Proofs.IE22.'+endpoint+' θ a hθ0 hθ1 ha hquantile\n'
 consumer+='example : NLA.Statements.IE22.Target := NLA.Proofs.IE22.target\nexample : NLA.ReviewedStatements.IE22.Target := NLA.Proofs.IE22.target\nexample : NLA.Statements.IE22.Target = NLA.ReviewedStatements.IE22.Target := rfl\n'
 log=run('CanonicalExactAudit',consumer.encode());closures={}
 for n,body in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log,re.S):closures.setdefault(n,[]).append([x.strip() for x in body.split(',') if x.strip()])
 check('actual3exports-identity2legacy-support-theorem-kind-kernel-and-axioms',set(closures)==set(names) and all(len(v)==1 and set(v[0])<=set(AXIOMS) for v in closures.values()),closures=closures)
 check('all3-exact-signatures-and-literal-reviewed-liveTarget-rfl',True,consumer_sha256=sha(consumer.encode()))
 negative='import Challenge\nset_option leancert.trust "kernel"\n'+''.join('#assert_trust kernel '+n+'\n' for n in config['theorem_names']);neg=run('CanonicalReferenceRejection',negative.encode(),expected_exit=1,obj=False)
 check('all3actual-canonicalChallenge-holes-rejected-with-sorryAx',neg.count('sorryAx')>=3 and all(n in neg for n in config['theorem_names']))
 report=dict(reviewer='/root/verification (independent non-author OpenAI Codex AI agent)',UTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),canonical_commit=REF,archive_only_descendant=DESC,shared_commit=SHARED,scope='Immutable canonical27 Lean closure with23 hash-identical fresh shared objects reused; exact3 endpoints and frozenTarget',passed=all(c['passed'] for c in checks),checks=checks,copies=copies,package_input_sha256=inputs,descendant_package_input_sha256=descinputs,original_archives=archive,frozen_originals=preserved,dependency_pins=pins,compiler_sha256=shared['compiler_sha256'],LEAN_PATH=env['LEAN_PATH'],private_build=str(a.build),commands=commands,independent_shared_result_sha256=sha(sharedpath.read_bytes()),script_sha256=sha(Path(__file__).read_bytes()),Linux_or_Comparator_run=False,promotion_approved=False)
 (HERE/'result.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(passed=report['passed'],checks=len(checks),canonical_Lean=27,reused_private_shared=23,commands=len(commands),package_inputs=len(inputs),failed=[c['name'] for c in checks if not c['passed']]),indent=2));return 0 if report['passed'] else 1
if __name__=='__main__':raise SystemExit(main())
