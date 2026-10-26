#!/usr/bin/env python3
"""Immutable source/preservation audit only; independent compiler replay is separate."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT=Path('/Users/ajt253/Documents/OpenProblemsInNLA')
OUT=Path(__file__).resolve().parent
COMMIT='7660eae85e1636de38c85a5c103ff0480f971e05'
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
paths=git('ls-tree','-r','--name-only',COMMIT,PREFIX).decode().splitlines()
author=obj(DOC+'AUTHOR_CHECKPOINT.json')
check('exact-fourteen-module-set',len(paths)==14 and set(paths)=={x['path'] for x in author['proof_modules']})
sources={}
declarations={}
for x in author['proof_modules']:
    b=read(COMMIT,x['path']);sources[x['path']]=sha(b)
    check('author-source-hash:'+x['path'],sha(b)==x['sha256'] and len(b)==x['bytes'])
    s=without_comments(b.decode())
    check('no-admission-axiom-unsafe-native:'+x['path'],not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b',s))
    check('no-Challenge-import:'+x['path'],not re.search(r'^\s*import\s+.*\bChallenge\b',s,re.M))
    check('explicit-kernel-mode:'+x['path'],'set_option leancert.trust "kernel"' in s)
    declarations[x['path']]=re.findall(r'^\s*(?:@\[[^\n]*\]\s*)?(?:theorem|lemma|def|abbrev)\s+(\w+)',s,re.M)
packet=DOC+'preproof/'
lock=obj(packet+'INPUT_LOCK.json')
check('published-base-exact',lock['published_base']==BASE)
for x in lock['reviewed_inputs']:
    current=read(COMMIT,x['path']);original=read(BASE,x['path']);frozen=read(COMMIT,packet+'frozen/'+x['path'])
    check('original-and-frozen-unchanged:'+x['path'],current==original==frozen and sha(current)==x['sha256'] and len(current)==x['bytes'])
for n,h in lock['packet_files'].items():
    check('frozen-packet-hash:'+n,sha(read(COMMIT,packet+n))==h)
auth=obj(DOC+'IMPLEMENTATION_AUTHORIZATION.json')
for n,h in auth['hashes'].items():
    check('preproof-review-authorization:'+n,sha(read(COMMIT,packet+n))==h)
def header(s,name):
    return re.search(r'\btheorem\s+'+name+r'\b[\s\S]*?\s*:=\s*by',s).group(0)
name='near_sharp_unit_row_witness'
reference=header(read(COMMIT,packet+'Challenge.lean').decode(),name)
actual=header(read(COMMIT,PREFIX+'LowerWitness.lean').decode(),name)
check('near-sharp-header-byte-exact',actual==reference)
combined='\n'.join(without_comments(read(COMMIT,p).decode()) for p in paths)
check('unproved-upper-not-advertised-as-declaration',not re.search(r'\btheorem\s+(?:uniform_squared_upper|target)\b',combined))
check('checkpoint-scope-truthful',author['full_target_verified'] is False and author['Linux_CI_claimed'] is False and author['canonical_status']=='Solved')
parent=git('rev-parse',COMMIT+'^').decode().strip()
protected=['problem_ids.json','linear-systems-and-elimination/IE-22','lean-statements/NLA/Statements','lean-statements/Reviewed']
delta=git('diff','--name-only',parent,COMMIT,'--',*protected).decode().splitlines()
check('canonical-and-all-statement-sources-unchanged-from-parent',not delta,changed=delta)
otherproof=git('diff','--name-only',parent,COMMIT,'--','lean-statements/NLA/Proofs').decode().splitlines()
check('other-problems-proof-sources-untouched',all(p.startswith(PREFIX) for p in otherproof))
registry=json.loads(read(COMMIT,'problem_ids.json'))
check('all-217-published-id-path-pairs-preserved',len(registry)==217 and registry==json.loads(read(BASE,'problem_ids.json')))
review_inputs=[DOC+'README.md',DOC+'AUTHOR_CHECKPOINT.json',DOC+'IMPLEMENTATION_AUTHORIZATION.json',packet+'Challenge.lean',packet+'CONTRACT.md',packet+'INPUT_LOCK.json',
 'lean-statements/NLA/Statements/IE22.lean','lean-statements/NLA/Statements/RowDeletion.lean','lean-statements/Reviewed/IE22.lean',
 'references/colbrook-recovered-2026-09-11/manuscripts/IE-21-22.tex']
result=dict(date='2026-10-25',reviewer='/root/inventory',authored_IE22_proof_sources=[],commit=COMMIT,parent=parent,published_base=BASE,
 verdict='APPROVE exact lower-witness/support source and mathematics only; full Target/universal upper remain unproved',
 scope='Read-only source/semantic/route/edge-case and byte-preservation review; no new compiler, Comparator, Linux or promotion acceptance claim',
 passed=all(x['passed'] for x in checks),check_count=len(checks),checks=checks,source_hashes=sources,
 lexical_named_declarations=declarations,lexical_declaration_count=sum(map(len,declarations.values())),
 lower_header_sha256=sha(actual.encode()),review_input_hashes={p:sha(read(COMMIT,p)) for p in review_inputs})
(OUT/'SOURCE_REVIEW_INVENTORY.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['passed','check_count','lexical_declaration_count','lower_header_sha256','verdict']},indent=2))
if not result['passed']:
    print(json.dumps([x for x in checks if not x['passed']],indent=2));raise SystemExit(1)
