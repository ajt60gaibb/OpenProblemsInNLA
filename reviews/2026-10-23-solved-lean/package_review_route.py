#!/usr/bin/env python3
"""Independent assembly replay, not an author-side hyperplane proof review."""
from pathlib import Path
import hashlib,json,subprocess,tempfile,os,re
repo=Path('/Users/ajt253/Documents/OpenProblemsInNLA')
pkg=Path('/private/tmp/nla-ra05-oct23-package')
evidence=repo/'reviews/2026-10-23-solved-lean/package-review-route-evidence'
evidence.mkdir(exist_ok=True)
lean=Path('/private/tmp/nla-oct23-lean-runtime/lean-4.33.1-darwin_aarch64/bin/lean')
deps=Path('/Users/ajt253/.codex/worktrees/pf05-lean-proof/OpenProblemsInNLA/nonnegative-and-positive-factorizations/PF-05/lean/.lake/packages')
hashes=lambda:{str(x.relative_to(pkg)):hashlib.sha256(x.read_bytes()).hexdigest() for x in sorted(pkg.rglob('*')) if x.is_file()}
inputs=hashes();lock=json.loads((pkg/'PACKAGE_LOCK.json').read_text())
result={'scope':'Independent combined package assembly + minimum proof review; authored hyperplane proof not self-reviewed','inputs':inputs,'package_lock_matches':all(inputs[k]==v['sha256'] for k,v in lock['files'].items()),'source_identity':{},'replay':[]}
source_map={'NLA/Statements/RA05.lean':'lean-statements/NLA/Statements/RA05.lean','NLA/Statements/RA06.lean':'lean-statements/NLA/Statements/RA06.lean','NLA/Statements/Infrastructure.lean':'lean-statements/NLA/Statements/Infrastructure.lean','Reviewed/RA05.lean':'lean-statements/Reviewed/RA05.lean','sources/ORIGINAL.md':'randomized-and-low-rank-approximation/RA-05/README.md','sources/NUMERICAL_TARGETS.md':'docs/lean/statements/RA-05/NUMERICAL_TARGETS.md','sources/part-1.tex':'references/holden-further-2026-09-14/RA-05/part-1.tex','sources/part-2.tex':'references/holden-further-2026-09-14/RA-05/part-2.tex'}
for dest,src in source_map.items():
 data=subprocess.check_output(['git','show',lock['published_base']+':'+src],cwd=repo)
 result['source_identity'][dest]={'published_source':src,'matches':data==(pkg/dest).read_bytes(),'sha256':hashlib.sha256(data).hexdigest()}
names=json.loads((pkg/'comparator.json').read_text())['theorem_names']
result['comparator_count']=len(names);result['comparator_distinct']=len(set(names))==11
challenge=(pkg/'Challenge.lean').read_text()
result['challenge_headers']={}
for name in names:
 short=name.rsplit('.',1)[-1]
 chead=re.search(r'theorem\s+'+short+r'\b(.*?):= by',challenge,re.S).group(1)
 file='SupportMinimum.lean' if '.SupportMinimum.' in name else 'HyperplaneBridge.lean'
 proof=(pkg/'NLA/Proofs/RA05'/file).read_text()
 phead=re.search(r'theorem\s+'+short+r'\b(.*?):= by',proof,re.S).group(1)
 result['challenge_headers'][name]=re.sub(r'\s+',' ',chead)==re.sub(r'\s+',' ',phead)
with tempfile.TemporaryDirectory(prefix='nla-package-route-') as tmp:
 out=Path(tmp)
 env=os.environ.copy();env['LEAN_PATH']=':'.join([str(out)]+[str(x/'.lake/build/lib/lean') for x in deps.iterdir() if (x/'.lake/build/lib/lean').is_dir()]+[str(lean.parent.parent/'lib/lean')])
 files=['NLA/Statements/Infrastructure.lean','NLA/Statements/RA05.lean','NLA/Statements/RA06.lean','NLA/Proofs/RA05/HyperplaneDefinitions.lean','NLA/Proofs/RA05/SupportMinimum.lean','NLA/Proofs/RA05/HyperplaneBridge.lean','Reviewed/RA05.lean','Challenge.lean','Solution.lean','Identity.lean','SupportAudit.lean']
 for file in files:
  target=out/Path(file).with_suffix('.olean');target.parent.mkdir(parents=True,exist_ok=True)
  argv=[str(lean),'-R',str(pkg),'-o',str(target),str(pkg/file)]
  p=subprocess.run(argv,cwd=pkg,env=env,capture_output=True,text=True,timeout=180)
  (evidence/(file.replace('/','-')+'.log')).write_text(p.stdout+p.stderr)
  result['replay'].append({'file':file,'argv':argv,'exit_code':p.returncode,'stdout':p.stdout,'stderr':p.stderr})
  print(file,p.returncode,flush=True)
  if p.returncode:
   print(p.stdout+p.stderr,flush=True)
   break
result['inputs_unchanged']=inputs==hashes()
result['passed']=result['package_lock_matches'] and all(x['matches'] for x in result['source_identity'].values()) and all(result['challenge_headers'].values()) and result['inputs_unchanged'] and len(result['replay'])==11 and all(x['exit_code']==0 for x in result['replay'])
(evidence/'result.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS=',result['passed'])
raise SystemExit(0 if result['passed'] else 1)
