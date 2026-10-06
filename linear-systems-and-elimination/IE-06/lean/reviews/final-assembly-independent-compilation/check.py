from pathlib import Path
import os, subprocess, hashlib, json, tempfile, shutil
receipt=Path(__file__).resolve().parent
project=receipt.parents[1]
source=project/'NLA/IE06/FinalAssembly.lean'
lean=Path('/Users/ajt253/Documents/ConvergenceOfAAA_chatgpt6/lean/.tools/lean-4.33.1-darwin_aarch64/bin/lean')
packages=Path('/Users/ajt253/Documents/ChrisResearch/RRF/SIMAX Version/Revision 2.2/lean/.lake/packages')
root=Path('/private/tmp/nla-ie06-root-dev')
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
before=sha(source)
work=Path(tempfile.mkdtemp(prefix='ie06-final-assembly-independent-'))
libs=[str(p/'.lake/build/lib/lean') for p in packages.iterdir() if (p/'.lake/build/lib/lean').is_dir()]
env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join([str(root)]+libs+[str(lean.parent.parent/'lib/lean')]);env['PATH']=str(lean.parent)+os.pathsep+env.get('PATH','')
snapshot=work/'FinalAssembly.lean';shutil.copyfile(source,snapshot)
if sha(snapshot)!=before or sha(source)!=before:raise SystemExit('copy race')
command=[str(lean),'-o',str(work/'FinalAssembly.olean'),snapshot.name]
cp=subprocess.run(command,cwd=work,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
(receipt/'compile.log').write_text(cp.stdout)
record={'scope':'Independent direct compilation of frozen FinalAssembly only, using parent-rebuilt local dependency objects and pinned external caches; not full closure, Linux sandbox, exporter, or raw replay','source_sha256':before,'source_unchanged':sha(source)==before,'command':command,'compiler':str(lean),'exit_code':cp.returncode,'log_sha256':sha(receipt/'compile.log')}
(receipt/'receipt.json').write_text(json.dumps(record,indent=2)+'\n')
print(cp.stdout);print(json.dumps(record))
raise SystemExit(0 if cp.returncode==0 and record['source_unchanged'] else 1)
