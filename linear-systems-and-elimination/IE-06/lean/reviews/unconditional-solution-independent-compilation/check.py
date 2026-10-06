from pathlib import Path
import os, subprocess, hashlib, json, tempfile, shutil
receipt=Path(__file__).resolve().parent
project=receipt.parents[1]
lean=Path('/Users/ajt253/Documents/ConvergenceOfAAA_chatgpt6/lean/.tools/lean-4.33.1-darwin_aarch64/bin/lean')
packages=Path('/Users/ajt253/Documents/ChrisResearch/RRF/SIMAX Version/Revision 2.2/lean/.lake/packages')
root=Path('/private/tmp/nla-ie06-root-dev')
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
work=Path(tempfile.mkdtemp(prefix='ie06-unconditional-solution-independent-'))
libs=[str(p/'.lake/build/lib/lean') for p in packages.iterdir() if (p/'.lake/build/lib/lean').is_dir()]
env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join([str(root)]+libs+[str(lean.parent.parent/'lib/lean')]);env['PATH']=str(lean.parent)+os.pathsep+env.get('PATH','')
records=[]
for rel in ['NLA/IE06/Unconditional.lean','Solution.lean']:
 source=project/rel;before=sha(source);snapshot=work/source.name;shutil.copyfile(source,snapshot)
 if sha(snapshot)!=before or sha(source)!=before:raise SystemExit('copy race')
 command=[str(lean),'-o',str(work/snapshot.with_suffix('.olean').name),snapshot.name]
 cp=subprocess.run(command,cwd=work,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 log=receipt/(source.stem+'.log');log.write_text(cp.stdout)
 record={'source':rel,'source_sha256':before,'source_unchanged':sha(source)==before,'command':command,'exit_code':cp.returncode,'log':log.name,'log_sha256':sha(log)}
 records.append(record);print(cp.stdout,flush=True)
 if cp.returncode:break
passed=len(records)==2 and all(r['exit_code']==0 and r['source_unchanged'] for r in records)
(receipt/'receipt.json').write_text(json.dumps({'scope':'Independent direct compilation of each frozen wrapper, using parent-rebuilt local dependency objects and pinned external caches; not full closure, Linux sandbox, exporter, or raw replay','compiler':str(lean),'records':records,'pass':passed},indent=2)+'\n')
raise SystemExit(0 if passed else 1)
