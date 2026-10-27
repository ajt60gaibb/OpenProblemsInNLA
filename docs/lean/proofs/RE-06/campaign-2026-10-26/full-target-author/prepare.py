from pathlib import Path
import re,shutil,subprocess,sys,json
b=Path('/private/tmp/nla-re06-repair-dev');w=Path('/Users/ajt253/.codex/worktrees/re06-nonadaptive-oct26/OpenProblemsInNLA')
seen=set();order=[]
def add(m):
 if m in seen:return
 seen.add(m)
 rel=Path(m.replace('.','/')+'.lean');p=b/'source'/rel
 if not p.exists():p.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(w/'lean-statements'/rel,p)
 for x in re.findall(r'^import (\S+)',p.read_text(),re.M):
  if x.startswith(('NLA.','Reviewed.')):add(x)
 if not (b/'out'/rel.with_suffix('.olean')).exists() or m in sys.argv[1:]:order.append(m)
for m in sys.argv[1:]:add(m)
print(order,flush=True)
subprocess.run(['python3',str(b/'compile.py'),*order],check=True)
