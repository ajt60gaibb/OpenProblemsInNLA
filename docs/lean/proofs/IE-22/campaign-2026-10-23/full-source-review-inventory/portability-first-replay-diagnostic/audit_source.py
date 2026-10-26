#!/usr/bin/env python3
"""Independent immutable complete IE22 source bindings, not a kernel/CI replay."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--repo',type=Path,required=True,help='Git repository containing the immutable reviewed commit objects (read only)')
parser.add_argument('--output',type=Path,required=True,help='Reviewer evidence directory; only this directory is written')
args=parser.parse_args()
ROOT=args.repo.resolve()
OUT=args.output.resolve()
OUT.mkdir(parents=True,exist_ok=True)
COMMIT='353ebcfcbbcfc08184c32f391ecb6068c7d9098f'
LOWER='7660eae85e1636de38c85a5c103ff0480f971e05'
BASE='5487945e5a72abd952b0c89915915de8cc9b3e65'
PREFIX='lean-statements/NLA/Proofs/IE22/'
DOC='docs/lean/proofs/IE-22/campaign-2026-10-23/'
git=lambda *a:subprocess.check_output(['git',*a],cwd=ROOT)
read=lambda c,p:git('show',c+':'+p)
sha=lambda b:hashlib.sha256(b).hexdigest()
obj=lambda p:json.loads(read(COMMIT,p))
checks=[]
def check(name,passed,**detail):checks.append(dict(name=name,passed=bool(passed),**detail))
def without_comments(s):
    out=[];i=0;depth=0
    while i<len(s):
        if s.startswith('/-',i):depth+=1;i+=2
        elif depth and s.startswith('-/',i):depth-=1;i+=2
        elif depth:i+=1
        elif s.startswith('--',i):
            j=s.find('\n',i);i=len(s) if j<0 else j
        else:out.append(s[i]);i+=1
    return ''.join(out)
lock=obj(DOC+'FULL_SOURCE_CHECKPOINT.json')
check('full-source-lock-counts',lock['proof_module_count']==19 and len(lock['files'])==23)
files={}
for x in lock['files']:
    b=read(COMMIT,x['path']);files[x['path']]=sha(b)
    check('immutable-lock-hash:'+x['path'],sha(b)==x['sha256'] and len(b)==x['bytes'])
    dest=OUT/'snapshots'/x['path'];dest.parent.mkdir(parents=True,exist_ok=True)
    if dest.exists():check('initial-reviewed-snapshot-exact:'+x['path'],dest.read_bytes()==b)
    else:dest.write_bytes(b)
paths=git('ls-tree','-r','--name-only',COMMIT,PREFIX).decode().splitlines()
check('exact-nineteen-proof-module-set',len(paths)==19 and set(paths)=={p for p in files if p.startswith(PREFIX)})
declarations={}
module_paths={p.removeprefix('lean-statements/').removesuffix('.lean').replace('/','.'):p for p in files}
imports={}
for p in paths:
    s=without_comments(read(COMMIT,p).decode())
    check('no-admission-axiom-unsafe-native:'+p,not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b',s))
    check('no-Challenge-import:'+p,not re.search(r'^\s*import\s+.*\bChallenge\b',s,re.M))
    check('explicit-kernel-mode:'+p,'set_option leancert.trust "kernel"' in s)
    declarations[p]=re.findall(r'^\s*(?:@\[[^\n]*\]\s*)?(?:theorem|lemma|def|abbrev|structure)\s+(\w+)',s,re.M)
for m,p in module_paths.items():
    imports[m]=re.findall(r'^\s*import\s+([\w.]+)',without_comments(read(COMMIT,p).decode()),re.M)
seen=set()
def visit(m):
    if m in seen:return
    seen.add(m)
    for child in imports[m]:
        if child.startswith('NLA.'):
            assert child in module_paths,(m,child)
            visit(child)
visit('NLA.Proofs.IE22.Final')
check('actual-final-closure-covers-all-nineteen-proof-modules',len([m for m in seen if m.startswith('NLA.Proofs.IE22.')])==19)
oldpaths=git('ls-tree','-r','--name-only',LOWER,PREFIX).decode().splitlines()
for p in oldpaths:
    if p!=PREFIX+'SpectralProjection.lean':check('prior-lower-approved-source-byte-unchanged:'+p,read(COMMIT,p)==read(LOWER,p))
delta=git('diff','--name-status',LOWER,COMMIT,'--',PREFIX).decode().splitlines()
expected={('A',PREFIX+n+'.lean') for n in ['Final','GaussianUpperBounds','GaussianUpperRealization','UpperParameters','UniversalUpper']}
expected.add(('M',PREFIX+'SpectralProjection.lean'))
check('exact-reviewed-source-delta',set(tuple(s.split('\t')) for s in delta)==expected)
packet=DOC+'preproof/'
pre=obj(packet+'INPUT_LOCK.json')
for x in pre['reviewed_inputs']:
    b=read(COMMIT,x['path'])
    check('original-and-frozen-preserved:'+x['path'],b==read(BASE,x['path'])==read(COMMIT,packet+'frozen/'+x['path']) and sha(b)==x['sha256'])
for n,h in pre['packet_files'].items():check('approved-preproof-packet:'+n,sha(read(COMMIT,packet+n))==h)
def header(s,n):return re.search(r'\btheorem\s+'+n+r'\b[\s\S]*?\s*:=\s*by',s).group(0)
challenge=read(COMMIT,packet+'Challenge.lean').decode()
headers={}
for n,file in [('uniform_squared_upper','UniversalUpper'),('near_sharp_unit_row_witness','LowerWitness'),('target','Final')]:
    h=header(read(COMMIT,PREFIX+file+'.lean').decode(),n)
    check('approved-exact-theorem-header:'+n,h==header(challenge,n))
    headers[n]=sha(h.encode())
final=without_comments(read(COMMIT,PREFIX+'Final.lean').decode())
check('literal-final-no-extra-binders','theorem target : NLA.Statements.IE22.Target := by' in final)
check('actual-both-endpoints-supplied-to-final','(uniform_squared_upper θ a hθ0 hθ1 ha hquantile)' in final and '(near_sharp_unit_row_witness θ a hθ0 hθ1 ha hquantile)' in final)
for p in ['lean-statements/NLA/Statements/IE22.lean','lean-statements/NLA/Statements/RowDeletion.lean','lean-statements/NLA/Statements/Infrastructure.lean','lean-statements/Reviewed/IE22.lean','problem_ids.json']:
    check('published-exact-boundary:'+p,read(COMMIT,p)==read(BASE,p))
protected=['problem_ids.json','linear-systems-and-elimination/IE-22','lean-statements/NLA/Statements','lean-statements/Reviewed']
changed=git('diff','--name-only',LOWER,COMMIT,'--',*protected).decode().splitlines()
check('canonical-and-statement-sources-unchanged-from-lower',not changed,changed=changed)
otherproof=git('diff','--name-only',LOWER,COMMIT,'--','lean-statements/NLA/Proofs').decode().splitlines()
check('other-problem-proof-sources-untouched',all(p.startswith(PREFIX) for p in otherproof))
check('no-Linux-or-fresh-author-replay-relabeling',lock['canonical_status']=='Solved' and not lock['whole_closure_fresh_replay_claimed'] and not lock['Linux_CI_claimed'])
result=dict(date='2026-10-25',reviewer='/root/inventory',authored_IE22_proof_sources=[],commit=COMMIT,prior_lower_checkpoint=LOWER,published_base=BASE,
 verdict='APPROVE complete unchanged literal IE22 Target source and mathematics; canonical package/fresh replay/Linux acceptance remain separate',
 scope='Non-author full-source/math/quantifier/edge-case review; no new Lean, Comparator or CI replay claim',
 passed=all(x['passed'] for x in checks),check_count=len(checks),checks=checks,locked_input_hashes=files,
 proof_source_count=len(paths),actual_local_final_import_closure=sorted(seen),actual_local_final_closure_count=len(seen),
 lexical_named_declarations=declarations,lexical_declaration_count=sum(map(len,declarations.values())),exact_three_header_hashes=headers,
 source_delta=delta,full_author_lock_sha256=sha(read(COMMIT,DOC+'FULL_SOURCE_CHECKPOINT.json')),
 auditor_sha256=sha(Path(__file__).read_bytes()),repository=str(ROOT),output=str(OUT),
 invocation=[sys.executable,str(Path(__file__).resolve()),'--repo',str(ROOT),'--output',str(OUT)])
(OUT/'SOURCE_REVIEW_INVENTORY.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['passed','check_count','proof_source_count','actual_local_final_closure_count','lexical_declaration_count','verdict']},indent=2))
if not result['passed']:
    print(json.dumps([x for x in checks if not x['passed']],indent=2));raise SystemExit(1)
