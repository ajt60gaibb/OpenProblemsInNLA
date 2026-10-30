from pathlib import Path
import hashlib,json,os,subprocess,sys,shutil,time
base=Path('/private/tmp/nla-re06-repair-dev')
repo=Path('/Users/ajt253/.codex/worktrees/re06-nonadaptive-oct26/OpenProblemsInNLA')
packet=repo/'docs/lean/proofs/RE-06/campaign-2026-10-26/preproof'
packages=Path('/Users/ajt253/.codex/worktrees/pf05-lean-proof/OpenProblemsInNLA/nonnegative-and-positive-factorizations/PF-05/lean/.lake/packages')
lean=Path('/private/tmp/nla-oct23-lean-runtime/lean-4.33.1-darwin_aarch64/bin/lean')
source=base/'source';out=base/'out';logs=base/'logs';attempts=base/'attempts'
for p in [source,out,logs,attempts]:p.mkdir(parents=True,exist_ok=True)
for module in ['NLA.Computation.SVDMachine','NLA.Computation.NonadaptiveMatrixQuery','NLA.Statements.Infrastructure','NLA.Statements.RE06','Reviewed.RE06']:
 rel=Path(module.replace('.','/')+'.lean');dst=source/rel;dst.parent.mkdir(parents=True,exist_ok=True)
 if not dst.exists():shutil.copyfile(packet/'originals/lean-statements'/rel,dst)
for name in ['SVDCore','SVDTotal']:
 rel=Path('NLA/Proofs/TR04')/(name+'.lean');dst=source/rel;dst.parent.mkdir(parents=True,exist_ok=True)
 if not dst.exists():shutil.copyfile(packet/'supplementary-reuse/lean-statements'/rel,dst)
manifest=json.loads((packet/'originals/lean-statements/lake-manifest.json').read_text())
heads={}
for pkg in manifest['packages']:
 head=subprocess.check_output(['git','-C',str(packages/pkg['name']),'rev-parse','HEAD'],text=True).strip()
 assert head==pkg['rev'];heads[pkg['name']]=head
env=os.environ.copy();env['LEAN_PATH']=':'.join([str(out)]+[str(p/'.lake/build/lib/lean') for p in sorted(packages.iterdir()) if (p/'.lake/build/lib/lean').is_dir()]+[str(lean.parent.parent/'lib/lean')])
records=[]
for module in sys.argv[1:]:
 src=source/(module.replace('.','/')+'.lean');obj=out/(module.replace('.','/')+'.olean');obj.parent.mkdir(parents=True,exist_ok=True)
 stamp=str(time.time_ns());archive=attempts/(module+'-'+stamp);archive.mkdir()
 shutil.copyfile(src,archive/'source.lean')
 argv=[str(lean),'-R',str(source),'-o',str(obj),str(src)]
 p=subprocess.run(argv,cwd=source,env=env,capture_output=True,text=True,timeout=600)
 log=p.stdout+p.stderr;(logs/(module+'.log')).write_text(log);(archive/'output.log').write_text(log)
 rec={'module':module,'sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'argv':argv,'exit':p.returncode,'archive':str(archive),'heads':heads}
 (archive/'RESULT.json').write_text(json.dumps(rec,indent=2)+'\n');records.append(rec)
 print(module,p.returncode,flush=True)
 print(log,flush=True)
 if p.returncode:sys.exit(p.returncode)
(base/'LAST_RESULT.json').write_text(json.dumps(records,indent=2)+'\n')
