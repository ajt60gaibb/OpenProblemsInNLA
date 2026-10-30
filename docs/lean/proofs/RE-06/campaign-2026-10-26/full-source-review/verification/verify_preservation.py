#!/usr/bin/env python3
"""Check all permanent IDs and all canonical mathematical text at the source epoch."""
import argparse, hashlib, json, subprocess
from pathlib import Path
REF='181c365dc426875aaa61984c901478b1b7c696e6'
BASE='099805ef1ce7347d373e47cccc3b2d7cf580a99e'
def sha(x):return hashlib.sha256(x).hexdigest()
def main():
 p=argparse.ArgumentParser();p.add_argument('--repo',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
 def blob(r,f):return subprocess.check_output(['git','-C',str(a.repo),'show',r+':'+f])
 idsraw=blob(REF,'problem_ids.json');ids=json.loads(idsraw);checks=[{'check':'all217_registry_bytes_identical_to_published_base','pass':idsraw==blob(BASE,'problem_ids.json') and len(ids)==217,'sha256':sha(idsraw)}];changed=[]
 for key,path in ids.items():
  x=blob(REF,path);y=blob(BASE,path);mode='entire README unchanged'
  same=x==y
  if not same:
   changed.append(key);i=x.find(b'## Problem statement');j=y.find(b'## Problem statement');same=i>=0 and j>=0 and x[i:]==y[j:];mode='entire suffix beginning ## Problem statement unchanged'
  checks.append({'check':'published_target:'+key,'path':path,'pass':same,'mode':mode,'source_sha256':sha(x),'base_sha256':sha(y)})
 checks.append({'check':'only_previous_approved_canonical_proof_promotions_differ','pass':set(changed)=={'IE-22','TR-04','TR-06','TR-26'},'changed':changed})
 r={'pass':all(c['pass'] for c in checks),'reviewer':'/root/verification','source_commit':REF,'published_base':BASE,'checks':checks,'script_sha256':sha(Path(__file__).read_bytes())};a.output.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'pass':r['pass'],'checks':len(checks)}));assert r['pass']
if __name__=='__main__':main()
