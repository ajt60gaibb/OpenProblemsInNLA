#!/usr/bin/env python3
"""Fresh actual Challenge build, then expect kernel trust rejection of its sorry."""
import hashlib,json,os,subprocess,tempfile
from pathlib import Path
R=Path(__file__).resolve().parents[5]
P=R/'nonnegative-and-positive-factorizations/PF-05/lean'
E=R/'docs/lean/proofs/PF-05/verification/challenge-rejection-review-3'
E.mkdir(exist_ok=False)
sha=lambda b:hashlib.sha256(b).hexdigest()
full=json.loads((R/'docs/lean/proofs/PF-05/verification/full-target-review-3/result.json').read_text())
lean=Path('/private/tmp/pf05-tooling/elan-home/toolchains/leanprover--lean4---v4.33.1/bin/lean')
frozen={n:(P/n).read_bytes() for n in ['NLA/Statements/Infrastructure.lean','NLA/Statements/PF05.lean','Challenge.lean']}
frozen['NegativeChallenge.lean']=b'import Challenge\nset_option leancert.trust "kernel"\n#print axioms NLA.PF05.target\n#assert_trust kernel NLA.PF05.target\n'
for n,b in frozen.items():
 p=E/'source'/(n+'.txt');p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
records=[]
with tempfile.TemporaryDirectory(prefix='nla-pf05-negative-challenge-') as tmp:
 t=Path(tmp);s=t/'source';o=t/'output';o.mkdir()
 for n,b in frozen.items():
  p=s/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
 env=dict(os.environ,LEAN_PATH=':'.join([str(o),*full['lean_path'].split(':')[1:]]))
 for n in frozen:
  obj=o/Path(n).with_suffix('.olean');obj.parent.mkdir(parents=True,exist_ok=True)
  cmd=[str(lean),'-R',str(s),'-o',str(obj),str(s/n)]
  p=subprocess.run(cmd,cwd=s,env=env,capture_output=True,text=True,timeout=180)
  r=dict(source=n,command=cmd,exit_code=p.returncode,stdout=p.stdout,stderr=p.stderr);records.append(r)
  (E/(n.replace('/','-')+'.log')).write_text(p.stdout+p.stderr)
log=records[-1]['stdout']+records[-1]['stderr']
passed=len(records)==4 and all(r['exit_code']==0 for r in records[:-1]) and records[-1]['exit_code']==1 and 'sorryAx: sorryAx' in log and "error: #assert_trust: 'NLA.PF05.target' depends on sorry or unrecognized axioms" in log and b'#assert_trust kernel NLA.PF05.target' in frozen['NegativeChallenge.lean']
out=dict(reviewer='/root/lean_verification',scope='Actual deliberately admitted Challenge rejected under kernel trust, separately from Solution',passed=passed,expected_rejection=True,source_sha256={n:sha(b) for n,b in frozen.items()},source_unchanged_after={n:(P/n).read_bytes()==b for n,b in frozen.items() if n!='NegativeChallenge.lean'},commands=records,linux=False)
out['passed']=passed and all(out['source_unchanged_after'].values())
(E/'result.json').write_text(json.dumps(out,indent=2)+'\n')
(E/'audit-driver.py.txt').write_bytes(Path(__file__).read_bytes())
print(json.dumps(dict(passed=out['passed'],consumer_log=log),indent=2))
raise SystemExit(0 if out['passed'] else 1)
