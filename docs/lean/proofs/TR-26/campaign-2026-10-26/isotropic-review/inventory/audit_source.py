#!/usr/bin/env python3
"""Independent immutable TR26 isotropic statement/source preservation audit."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--repo',type=Path,required=True)
p.add_argument('--output',type=Path,required=True)
a=p.parse_args();a.output.mkdir(parents=True,exist_ok=True)
C='4692336f0e1a50d5e261bba68277875da30fba51';B='5487945e5a72abd952b0c89915915de8cc9b3e65'
P='lean-statements/NLA/Proofs/TR26/';D='docs/lean/proofs/TR-26/campaign-2026-10-26/'
git=lambda *v:subprocess.check_output(['git',*v],cwd=a.repo)
read=lambda c,q:git('show',c+':'+q)
sha=lambda b:hashlib.sha256(b).hexdigest()
checks=[]
def check(n,b,**d):checks.append(dict(name=n,passed=bool(b),**d))
def code(s):
 out=[];i=0;depth=0
 while i<len(s):
  if depth:
   if s.startswith('/-',i):depth+=1;i+=2
   elif s.startswith('-/',i):depth-=1;i+=2
   else:out.append('\n' if s[i]=='\n' else ' ');i+=1
  elif s.startswith('/-',i):depth=1;i+=2
  elif s.startswith('--',i):
   j=s.find('\n',i);i=len(s) if j<0 else j
  elif s[i]=='"':
   out.append(' ');i+=1
   while i<len(s):
    if s[i]=='\\':i+=2
    elif s[i]=='"':i+=1;break
    else:out.append('\n' if s[i]=='\n' else ' ');i+=1
  else:out.append(s[i]);i+=1
 return ''.join(out)
checkpoint=json.loads(read(C,D+'ISOTROPIC_ENDPOINT_CHECKPOINT.json'))
files={};modules={};imports={}
check('checkpoint-scope-explicit-partial-noLinux-noComparator',checkpoint['full_target_proved'] is False and checkpoint['nonisotropic_endpoint_proved'] is False and checkpoint['canonical_status']=='Solved' and checkpoint['Linux_CI_claimed'] is False and checkpoint['Comparator_claimed'] is False)
for x in checkpoint['proof_inputs']:
 q=x['path'];b=read(C,q);files[q]=sha(b);s=code(b.decode())
 check('all33checkpoint-hash-length:'+q,sha(b)==x['sha256'] and len(b)==x['bytes'])
 check('no-admission-custom-axiom-native-unsafe-code:'+q,not re.search(r'\b(?:axiom|sorry|admit|native_decide|unsafe|implemented_by|extern|opaque)\b',s))
 check('explicit-kernel-mode:'+q,'set_option leancert.trust "kernel"' in b.decode())
 check('no-reference-import:'+q,not re.search(r'^\s*import\s+.*(?:Challenge|ReferenceHoles)\b',s,re.M))
 module=q.removeprefix('lean-statements/').removesuffix('.lean').replace('/','.')
 modules[module]=q;imports[module]=re.findall(r'^\s*import\s+([\w.]+)',s,re.M)
check('exact33-authored-source-file-set',len(files)==33 and set(files)==set(git('ls-tree','-r','--name-only',C,P).decode().splitlines()))
pre=json.loads(read(C,D+'preproof/INPUT_LOCK.json'))
for x in pre['reviewed_inputs']:
 b=read(C,x['path']);frozen=read(C,D+'preproof/frozen/'+x['path'])
 check('all24original-inputs-preserved:'+x['path'],b==frozen==read(B,x['path']) and sha(b)==x['sha256'] and len(b)==x['bytes'])
registry=read(C,'problem_ids.json');check('permanent217IDs-paths-preserved',registry==read(B,'problem_ids.json') and len(json.loads(registry))==217)
check('canonical-target-status-original-page-preserved',read(C,'tensor-computations/TR-26/README.md')==read(B,'tensor-computations/TR-26/README.md')==read(C,'docs/lean/statements/TR-26/ORIGINAL.md'))
original_challenge=read(C,D+'preproof/Challenge.lean').decode()
actual=read(C,P+'IsotropicDegree.lean').decode()
header=lambda s:re.sub(r'\s+','',re.search(r'theorem isotropic_degree\b(.*?)\s*:=',s,re.S).group(1))
check('exact-preapproved-isotropic-endpoint-no-new-hypotheses',header(actual)==header(original_challenge))
check('preproof-corehashes-retained',sha(read(C,D+'preproof/INPUT_LOCK.json'))=='59314bd19a35f47dadd9a672517d4f9053682b4454b79c571cb915231342a91c' and sha(read(C,D+'preproof/Challenge.lean'))=='122ad60aaddf59e91dacd627637cf7237b8614d83b6d2eead381a76a698d7aba' and sha(read(C,D+'preproof/CONTRACT.md'))=='26625969b0c33b85d5e6dcb59dd2c3c9f9ca1389fcc92f4b3f1f1facb81d56a0')
all_code='\n'.join(code(read(C,q).decode()) for q in files)
check('no-full-target-or-nonisotropic-theorem-advertised',not re.search(r'\btheorem\s+(?:target|nonisotropic_degree)\b',all_code))
seen=set()
def visit(m):
 if m in seen:return
 seen.add(m)
 for n in imports.get(m,[]):
  if n in modules:visit(n)
visit('NLA.Proofs.TR26.IsotropicDegree')
check('actual-isotropic-support-closure-is-concrete',all(n in modules for n in seen) and 'NLA.Proofs.TR26.ChartIncidence' in seen and 'NLA.Proofs.TR26.IncidenceIdeal' in seen and 'NLA.Proofs.TR26.IsotropicFactor' in seen)
r=dict(scope='Independent immutable statement/source/preservation audit only; mathematical review in REVIEW.md and fresh kernel replay are separate evidence.',reviewer='/root/inventory',commit=C,proof_sources_authored=[],checkpoint_sha256=sha(read(C,D+'ISOTROPIC_ENDPOINT_CHECKPOINT.json')),all33_proof_source_sha256=files,actual_isotropic_authored_import_closure=sorted(seen),actual_isotropic_authored_import_count=len(seen),checks=checks,check_count=len(checks),passed=all(x['passed'] for x in checks),auditor_sha256=sha(Path(__file__).read_bytes()))
(a.output/'SOURCE_REVIEW.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({k:r[k] for k in ['passed','check_count','actual_isotropic_authored_import_count']},indent=2))
raise SystemExit(0 if r['passed'] else 1)
