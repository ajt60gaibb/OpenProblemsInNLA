#!/usr/bin/env python3
"""Retain actual complete GitHub small-tree responses for one accepted PR merge."""
import argparse,json,re,subprocess
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--evidence',type=Path,required=True);a=p.parse_args();e=a.evidence
r=json.loads(next((e/'artifact').rglob('result.json')).read_text());merge=r['repository_commit'];assert re.fullmatch('[0-9a-f]{40}',merge)
trees=e/'merge-source-trees';trees.mkdir(exist_ok=True)
def get(endpoint,dest):
 data=subprocess.check_output(['gh','api','--method','GET','repos/ajt60gaibb/OpenProblemsInNLA/'+endpoint]);dest.write_bytes(data);return json.loads(data)
c=get('git/commits/'+merge,e/'merge-commit.json');records=[]
for prefix in ['nonnegative-and-positive-factorizations/PF-05/lean','tools/lean','.github/workflows']:
 t=c['tree']['sha']
 for part in prefix.split('/'):
  f=trees/(t+'.json');j=json.loads(f.read_text()) if f.exists() else get('git/trees/'+t,f)
  assert not j.get('truncated') and j['sha']==t
  row=next(x for x in j['tree'] if x['path']==part);assert row['type']=='tree';t=row['sha']
 f=trees/(t+'-recursive.json');j=get('git/trees/'+t+'?recursive=1',f);assert not j.get('truncated') and j['sha']==t
 records.append({'prefix':prefix,'tree_sha':t,'entries':j['tree']});print(prefix,len(j['tree']),flush=True)
(e/'merge-source-subtrees.json').write_text(json.dumps(records,indent=2)+'\n')
