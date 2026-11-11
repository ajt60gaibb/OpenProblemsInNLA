#!/usr/bin/env python3
"""Portable independent audit of immutable full TR26 source checkpoint; read-only Git."""
import argparse,hashlib,json,re,subprocess
from pathlib import Path
p=argparse.ArgumentParser(description=__doc__);p.add_argument('--repo',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();a.output.mkdir(parents=True,exist_ok=True)
C='ecc597cb68b65b473aecce9ac635e27d35c09694';B='5487945e5a72abd952b0c89915915de8cc9b3e65';I='4692336f0e1a50d5e261bba68277875da30fba51';P='6c607ab14af2b8b2b8075f0b3f1798e037c10899';D='docs/lean/proofs/TR-26/campaign-2026-10-26/';K='tensor-computations/TR-26/lean/'
sha=lambda b:hashlib.sha256(b).hexdigest();read=lambda q,c=C:subprocess.check_output(['git','show',c+':'+q],cwd=a.repo)
checks=[]
def check(n,b):checks.append(dict(name=n,passed=bool(b)));assert b,n
freeze=read(D+'FULL_TARGET_SOURCE_FREEZE.json');f=json.loads(freeze)
check('frozen-source-lock',sha(freeze)=='30259d66f399459826180f682b02ac5c8766e1df80d277f6c633f56650bc0805')
check('77proof3shared1audit',len(f['proof_inputs'])==77 and len(f['shared_inputs'])==3)
check('previous53new24',sum(x['previous_checkpoint'] for x in f['proof_inputs'])==53)
files={};headers={}
def uncomment(s):
 out='';i=0;depth=0
 while i<len(s):
  if s[i:i+2]=='/-':depth+=1;i+=2
  elif depth and s[i:i+2]=='-/':depth-=1;i+=2
  elif depth:i+=1
  elif s[i:i+2]=='--':
   z=s.find('\n',i);i=len(s) if z<0 else z
  else:out+=s[i];i+=1
 return out
for x in f['proof_inputs']+f['shared_inputs']+[f['audit_input']]:
 b=read(x['path']);check('sourcehash:'+x['path'],sha(b)==x['sha256'] and ('bytes' not in x or len(b)==x['bytes']));files[x['path']]=dict(sha256=sha(b),bytes=len(b))
 if x in f['proof_inputs']:
  s=uncomment(b.decode());check('kernel-mode:'+x['path'],'set_option leancert.trust "kernel"' in s)
  check('no-added-trust-oracle:'+x['path'],not re.search(r'\b(sorry|admit|axiom|unsafe)\b|set_option\s+(?:debug\.skipKernelTC|leancert\.trust)\s+(?:true|"(?:none|native|trust)")',s))
  headers[x['path']]=re.findall(r'^(?:theorem|lemma)\s+[^\n]+',s,re.M)
  if x['previous_checkpoint']:check('previous53bytes:'+x['path'],b==read(x['path'],f['parent_commit']))
  if not x['previous_checkpoint']:
   r=read(x['accepted_receipt']);check('exact-author-receipt-retained:'+x['path'],sha(r)==x['accepted_receipt_sha256'])
pre=read(D+'preproof/INPUT_LOCK.json');check('original24lock',sha(pre)=='59314bd19a35f47dadd9a672517d4f9053682b4454b79c571cb915231342a91c')
for x in json.loads(pre)['reviewed_inputs']:
 b=read(x['path']);check('original24:'+x['path'],sha(b)==x['sha256'] and len(b)==x['bytes'] and b==read(D+'preproof/frozen/'+x['path']))
for n,expected in [('Challenge.lean','122ad60aaddf59e91dacd627637cf7237b8614d83b6d2eead381a76a698d7aba'),('CONTRACT.md','26625969b0c33b85d5e6dcb59dd2c3c9f9ca1389fcc92f4b3f1f1facb81d56a0')]:check('approved-preproof:'+n,sha(read(D+'preproof/'+n))==expected)
for q in ['lean-statements/NLA/Statements/TR26.lean','lean-statements/Reviewed/TR26.lean','tensor-computations/TR-26/README.md','problem_ids.json']:
 check('unchanged-published:'+q,read(q)==read(q,B))
check('217IDs',len(json.loads(read('problem_ids.json')))==217)
# The immutable canonical package is a separate, unchanged partial milestone.
lock=json.loads(read(K+'PACKAGE_LOCK.json',P));check('same-partial-package-lock',read(K+'PACKAGE_LOCK.json')==read(K+'PACKAGE_LOCK.json',P))
items=lock.get('files',lock.get('inputs'))
if isinstance(items,dict):items=[dict(path=k,**v) if isinstance(v,dict) else dict(path=k,sha256=v) for k,v in items.items()]
for x in items:
 q=K+x['path'];check('353partialpackageunchanged:'+x['path'],read(q)==read(q,P))
check('353lockedpartialinputs',len(items)==353)
iso=json.loads(read(D+'ISOTROPIC_ENDPOINT_CHECKPOINT.json',I))
for x in iso['proof_inputs']:check('all33approvedisotropicsourcesunchanged:'+x['path'],read(x['path'])==read(x['path'],I))
for n in ['nonisotropic_degree','isotropic_degree','target']:
 found=[q for q in files if re.search(r'^theorem '+n+r'\b',uncomment(read(q).decode()),re.M)];check('singleactualtheorem:'+n,len(found)==1)
for q in files:
 if q.startswith('lean-statements/'):
  for m in re.findall(r'^import\s+(\S+)',read(q).decode(),re.M):
   if m.startswith(('NLA.','Reviewed.')):check('closedlocalimport:'+q+':'+m,'lean-statements/'+m.replace('.','/')+'.lean' in files)
check('canonical-unpromoted',b'**Status:** Solved' in read('tensor-computations/TR-26/README.md'))
result=dict(reviewer='/root/inventory',authored_proof_sources=[],commit=C,proof_modules=77,shared_modules=3,original_inputs_preserved=24,IDs_paths_preserved=217,full_canonical_package=False,Linux_claim=False,source_files=files,selected_headers=headers,checks=checks,check_count=len(checks),passed=all(x['passed'] for x in checks),auditor_sha256=sha(Path(__file__).read_bytes()))
(a.output/'SOURCE_REVIEW.json').write_text(json.dumps(result,indent=2)+'\n');print('PASS',len(checks),'checks')
