#!/usr/bin/env python3
"""Independent exact-copy and boundary-delta check; no builds or source writes."""
import hashlib
import json
from pathlib import Path
import subprocess
R = Path(__file__).resolve().parents[5]
P = R / 'nonnegative-and-positive-factorizations/PF-05/lean'
D = R / 'docs/lean/proofs/PF-05'
checks=[]
def sha(b): return hashlib.sha256(b).hexdigest()
def check(n,p,**kw): checks.append(dict(name=n,passed=bool(p),**kw))
pre=P/'pre-solution-boundary-lock.json'
lock=P/'proof-source-lock.json'
b=json.loads(pre.read_text()); p=json.loads(lock.read_text())
a=json.loads((D/'verification/full-target-review-3/result.json').read_text())
check('independently-approved-boundary-lock',sha(pre.read_bytes())=='c0196c6806961a084f6474809e7ac0d60019ae8433455bb2775465329a0a694e',observed=sha(pre.read_bytes()))
check('exact-42-source-copy-list-unchanged-after-boundary',p['copies']==b['copies'] and len(p['copies'])==42)
for c in p['copies']:
 s=(R/c['source']).read_bytes();d=(R/c['destination']).read_bytes()
 local=c['source'].removeprefix('lean-statements/')
 check('exact-copy:'+c['module'],s==d and sha(s)==c['source_sha256']==c['destination_sha256']==a['source_sha256'][local])
for f,h in b['exports'].items():
 if f!='lakefile.toml': check('unchanged-reviewed-export:'+f,sha((P/f).read_bytes())==h)
old=P/'reviews/pre-solution-boundary-review-1-snapshot/lakefile.toml.txt'
oldbytes=old.read_bytes()
check('retained-historical-Lake-config',sha(oldbytes)==b['exports']['lakefile.toml'])
newbytes=oldbytes.replace(b'defaultTargets = ["Challenge", "Identity"]', b'defaultTargets = ["Challenge", "Identity", "Solution"]')+b'\n[[lean_lib]]\nname = "Solution"\n'
check('only-intended-Lake-Solution-extension',(P/'lakefile.toml').read_bytes()==newbytes)
expected={str(Path(c['destination']).relative_to(P.relative_to(R))) for c in p['copies']}|{'Reviewed/PF05.lean','Challenge.lean','Identity.lean','Solution.lean'}
actual={str(x.relative_to(P)) for x in P.rglob('*.lean') if '.lake' not in x.parts}
check('exact-46-actual-Lean-inputs',actual==expected and len(actual)==46,actual_count=len(actual),missing=sorted(expected-actual),extra=sorted(actual-expected))
stmt=(P/'NLA/Statements/PF05.lean').read_bytes()
base=subprocess.check_output(['git','show','36767fa430309f13d04dc6ebe080d470f5c2444a:lean-statements/NLA/Statements/PF05.lean'],cwd=R)
check('actual-statement-identical-to-published-base',stmt==base)
check('frozen-review-is-only-namespace-copy',(P/'Reviewed/PF05.lean').read_bytes()==b'/- Frozen statement boundary. Changes reopen independent review. -/\n'+stmt.replace(b'namespace NLA.Statements',b'namespace NLA.ReviewedStatements').replace(b'end NLA.Statements',b'end NLA.ReviewedStatements'))
check('literal-Solution-wrapper',(P/'Solution.lean').read_text().count('theorem target : NLA.Statements.PF05.Target := by')==1 and 'exact NLA.Proofs.PF05.target' in (P/'Solution.lean').read_text() and 'import Challenge' not in (P/'Solution.lean').read_text())
check('full-Target-only-comparator',json.loads((P/'comparator.json').read_text())=={'challenge_module':'Challenge','solution_module':'Solution','theorem_names':['NLA.PF05.target'],'definition_names':[],'permitted_axioms':['propext','Classical.choice','Quot.sound']})
out=dict(date='2026-10-18',reviewer='/root/lean_verification',reviewer_authored_PF05_proof_sources=[],checks=checks,passed=all(x['passed'] for x in checks),source_sha256={str(x.relative_to(P)):sha(x.read_bytes()) for x in sorted(P.rglob('*.lean')) if '.lake' not in x.parts},proof_source_lock_sha256=sha(lock.read_bytes()),pre_solution_lock_sha256=sha(pre.read_bytes()),authoritative_linux_comparator=False)
(D/'verification/canonical-copies-review-3.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(passed=out['passed'],checks=len(checks),failed=[x['name'] for x in checks if not x['passed']]),indent=2))
raise SystemExit(0 if out['passed'] else 1)
