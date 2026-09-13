from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,os,re,subprocess
repo=Path('/tmp/nla-lean-ie23-worktree');prefix='linear-systems-and-elimination/IE-23/lean/';project=repo/prefix
review=project/'verification/root-publication-2026-09-12';preflight=project/'verification/publication-preflight-2026-09-12'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();git=lambda *a:subprocess.check_output(['git',*a],cwd=repo)
assert git('rev-parse','HEAD').decode().strip()=='ec703a43cd3343d02ad327ae6d682b04935bafac'
assert sha(review/'INDEPENDENT-REVIEW.md')=='aee432a75cea558910070cd84ab468714264510446882d365f0df9e2b2bf5dea'
assert sha(review/'ROOT-CHECKS.json')=='04115ec07ad8ffc9b7687e02d08cc9a8cf2bb5f83df70c4c8ae2a6a66a34dc2b'
assert sha(review/'EVIDENCE-MANIFEST.json')=='593cc6e599fe1655afe9b937390fb80791e57a4090ef4a092699b8d58561fcba'
r=json.loads((review/'ROOT-CHECKS.json').read_text())
for rel,h in r['publication_sha256'].items():assert sha(repo/rel)==h,rel
for rel,h in r['unchanged_nonwrapper_inputs'].items():assert sha(project/rel)==h,rel
for rel,h in r['all_retained_evidence'].items():assert sha(project/rel)==h,rel
own=json.loads((review/'EVIDENCE-MANIFEST.json').read_text())['files']
assert set(own)=={p.relative_to(review).as_posix() for p in review.rglob('*') if p.is_file() and p.name!='EVIDENCE-MANIFEST.json'}
for rel,v in own.items():assert sha(review/rel)==v['sha256'] and (review/rel).stat().st_size==v['bytes'],rel
directories=[prefix+'verification/'+s for s in ['linux-2026-09-12','root-operational-2026-09-12','publication-2026-09-12','root-publication-2026-09-12']]
subprocess.run(['git','add','--',*r['publication_sha256'],*directories],cwd=repo,check=True)
staged=git('diff','--cached','--name-only').decode().splitlines()
for path in staged:assert path in r['publication_sha256'] or any(path.startswith(d+'/') for d in directories),path
check=subprocess.run(['git','diff','--cached','--check'],cwd=repo,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
excluded={}
if check.returncode:
    for line in check.stdout.decode().splitlines():
        m=re.match(r'^(.+):\d+: (?:trailing whitespace\.|new blank line at EOF\.)$',line)
        if m:
            path=m.group(1);rel=path.removeprefix(prefix)
            assert path.startswith(prefix) and rel in r['all_retained_evidence'],path
            assert sha(repo/path)==r['all_retained_evidence'][rel],path
            excluded[path]=dict(sha256=sha(repo/path),reason='Exact already-reviewed immutable historical execution evidence; preserve original bytes')
    assert excluded,check.stdout.decode()
args=['git','diff','--cached','--check','--','.']+[':(exclude)'+path for path in sorted(excluded)]
check2=subprocess.run(args,cwd=repo,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
assert check2.returncode==0,check2.stdout.decode()
assert not preflight.exists();preflight.mkdir()
(preflight/'CHECKS.json').write_text(json.dumps(dict(utc=datetime.now(timezone.utc).isoformat(),result='PASS exact staged publication scope and whitespace checks',review_sha256=sha(review/'INDEPENDENT-REVIEW.md'),approval_checks_sha256=sha(review/'ROOT-CHECKS.json'),only_exact_preserved_paths_excluded=excluded,command=args,exit_code=0),indent=2)+'\n')
(preflight/'commit_ie23_publication.py').write_bytes(Path(__file__).read_bytes())
outer=preflight/'EVIDENCE-MANIFEST.json';files={p.name:dict(sha256=sha(p),bytes=p.stat().st_size) for p in preflight.iterdir() if p.is_file() and p!=outer}
outer.write_text(json.dumps(dict(file_count=len(files),files=files,inventory_rule='All files except exact outer manifest; nested manifests retained'),indent=2)+'\n')
subprocess.run(['git','add','--',str(preflight.relative_to(repo))],cwd=repo,check=True)
subprocess.run(args,cwd=repo,check=True)
env=dict(os.environ,GIT_AUTHOR_NAME='George Stepaniants',GIT_COMMITTER_NAME='George Stepaniants',GIT_AUTHOR_EMAIL='',GIT_COMMITTER_EMAIL='')
done=subprocess.run(['git','-c','user.name=George Stepaniants','-c','user.email=','-c','commit.gpgsign=false','commit','-m','Publish Linux-verified IE-23 formalization and reviewed evidence'],cwd=repo,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
assert done.returncode==0,done.stdout.decode()
assert git('show','-s','--format=%ae%x00%ce','HEAD').rstrip(b'\n')==b'\0'
assert not git('status','--porcelain')
receipt=dict(commit=git('rev-parse','HEAD').decode().strip(),blank_author_and_committer_emails=True,worktree_clean=True,review_sha256=sha(review/'INDEPENDENT-REVIEW.md'),immutable_whitespace_exclusions=len(excluded))
Path('/tmp/nla-lean-formalization/IE-23-publication-commit.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
