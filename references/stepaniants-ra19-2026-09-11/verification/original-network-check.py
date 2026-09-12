"""Bounded read-only RA-19 public-branch and discussion eligibility check."""
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from datetime import datetime, timezone
import base64
import hashlib
import json
import os
import re
import shutil
import subprocess
import urllib.parse

GH=os.environ.get('GH') or shutil.which('gh')
if not GH: raise SystemExit('Set GH to GitHub CLI.')
ROOT='ajt60gaibb/OpenProblemsInNLA'
CAN='randomized-and-low-rank-approximation/RA-19/README.md'
HERE=Path(__file__).resolve().parent

def api(path,paged=False):
    cmd=[GH,'api',path]
    if paged: cmd+=['--paginate','--slurp']
    value=json.loads(subprocess.check_output(cmd,text=True,timeout=45))
    return [x for batch in value for x in batch] if paged else value

repos={ROOT}
queue=[ROOT]
while queue:
    repo=queue.pop()
    for item in api('repos/'+repo+'/forks?per_page=100',True):
        if item['full_name'] not in repos:
            repos.add(item['full_name']); queue.append(item['full_name'])

def branches(repo):
    return [{'repo':repo,'branch':b['name'],'sha':b['commit']['sha']}
            for b in api('repos/'+repo+'/branches?per_page=100',True)]
with ThreadPoolExecutor(max_workers=5) as pool:
    heads=[h for batch in pool.map(branches,sorted(repos)) for h in batch]
unique={h['sha']:h for h in heads}

def read_head(head):
    tree=api('repos/'+head['repo']+'/git/trees/'+head['sha']+'?recursive=1')
    assert not tree.get('truncated')
    selected=[x for x in tree['tree'] if x['type']=='blob' and
              (x['path']==CAN or re.search(r'RA[-_]?19|corank.one',x['path'],re.I))
              and x['path'].endswith(('.md','.tex','.txt','.py'))]
    return head['sha'],{'repo':head['repo'],'files':selected}
with ThreadPoolExecutor(max_workers=5) as pool:
    trees=dict(pool.map(read_head,unique.values()))
objects={f['sha']:(tree['repo'],f['sha']) for tree in trees.values() for f in tree['files']}
def read_blob(item):
    repo,sha=item
    obj=api('repos/'+repo+'/git/blobs/'+sha)
    data=base64.b64decode(obj['content'])
    assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==sha
    return sha,data.decode()
with ThreadPoolExecutor(max_workers=5) as pool:
    contents=dict(pool.map(read_blob,objects.values()))
for h in heads:
    row=next((x for x in trees[h['sha']]['files'] if x['path']==CAN),None)
    h['canonical_status']='Not yet present on this historical head' if row is None else next(
        (line for line in contents[row['sha']].splitlines() if '**Status:**' in line),'No status found')

def discussions(repo):
    q=urllib.parse.quote('"RA-19" repo:'+repo+' in:title,body')
    rows=api('search/issues?q='+q+'&per_page=100')['items']
    matches=[]
    for row in rows:
        entry={'repo':repo,'number':row['number'],'url':row['html_url'],'title':row['title'],
               'state':row['state'],'body':row.get('body')}
        entry['comments']=api('repos/'+repo+'/issues/'+str(row['number'])+'/comments?per_page=100',True)
        if 'pull_request' in row:
            entry['reviews']=api('repos/'+repo+'/pulls/'+str(row['number'])+'/reviews?per_page=100',True)
        matches.append(entry)
    return matches
with ThreadPoolExecutor(max_workers=5) as pool:
    discussion=[row for batch in pool.map(discussions,sorted(repos)) for row in batch]
record={'checked_utc':datetime.now(timezone.utc).isoformat(),'repositories':sorted(repos),
        'branches':heads,'trees':trees,'contents':contents,'discussion_matches':discussion,
        'scope':'All recursively returned public forks and branch heads; every canonical or RA19/corank-one-named text file; RA-19-matching issue/PR titles and bodies plus their full comments/reviews. Bounded public check; private, deleted, unpublished, and unidentifiably named work excluded.'}
out=HERE/'public-network.json';out.write_text(json.dumps(record,indent=2)+'\n')
print(record['checked_utc'],len(repos),'repos',len(heads),'heads',len(contents),'distinct text files')
print('Statuses:',sorted({h['canonical_status'] for h in heads}))
print('Discussions:',[(x['url'],x['title']) for x in discussion])
print('SHA256',hashlib.sha256(out.read_bytes()).hexdigest())
