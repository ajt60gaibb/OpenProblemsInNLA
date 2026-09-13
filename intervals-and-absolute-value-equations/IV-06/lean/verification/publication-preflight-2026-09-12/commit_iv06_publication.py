from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,os,re,subprocess
repo=Path('/tmp/nla-lean-iv06-worktree');prefix='intervals-and-absolute-value-equations/IV-06/lean/';project=repo/prefix
pub=project/'verification/publication-2026-09-12';review=project/'reviews/publication-referee-1-evidence';report=project/'reviews/publication-referee-1.md'
preflight=project/'verification/publication-preflight-2026-09-12'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();git=lambda *a:subprocess.check_output(['git',*a],cwd=repo)
assert git('rev-parse','HEAD').decode().strip()=='4c075f14209e85ef867eea90eacbea1e05e13a61'
assert sha(report)=='af973dd6fba63ab898090864b1fc3d40762ccf03c698b59eacd37559e6b918fc'
assert sha(review/'EVIDENCE-MANIFEST.json')=='a20c8ae9e409a3d0fe2f41fb6c0c35a336f3aeba1b99b971b8f695453a753441'
assert sha(pub/'INTEGRITY-CHECKS.json')=='71232a29a9150ef51a28dfba398b361d982e3540af31470b085ef02727676beb'
assert sha(pub/'EVIDENCE-MANIFEST.json')=='ab90352bc400a56881643a7f5896a5c6417a6474b6eddfc35cb895abc410b113'
r=json.loads((pub/'INTEGRITY-CHECKS.json').read_text())
for rel,h in r['publication_sha256'].items():assert sha(repo/rel)==h,rel
for rel,h in r['unchanged_nonwrapper_sha256'].items():assert sha(project/rel)==h,rel
retained=dict(r['all_retained_operational_sha256'])
for rel,h in retained.items():assert sha(project/rel)==h,rel
for directory,external,total in [(pub,set(),23),(review,{'../publication-referee-1.md'},13)]:
    outer=directory/'EVIDENCE-MANIFEST.json';files=json.loads(outer.read_text())['files'];assert len(files)==total
    actual={p.relative_to(directory).as_posix() for p in directory.rglob('*') if p.is_file() and p!=outer}
    assert actual==set(files)-external
    for rel,v in files.items():assert sha(directory/rel)==v['sha256'] and (directory/rel).stat().st_size==v['bytes'],rel
    retained.update({p.relative_to(project).as_posix():sha(p) for p in directory.rglob('*') if p.is_file()})
retained[report.relative_to(project).as_posix()]=sha(report)
directories=[prefix+'verification/'+s for s in ['linux-2026-09-12','root-operational-2026-09-12','publication-2026-09-12']]+[prefix+'reviews/publication-referee-1-evidence']
reportpath=report.relative_to(repo).as_posix()
subprocess.run(['git','add','--',*r['publication_sha256'],*directories,reportpath],cwd=repo,check=True)
for path in git('diff','--cached','--name-only').decode().splitlines():assert path in r['publication_sha256'] or path==reportpath or any(path.startswith(d+'/') for d in directories),path
first=subprocess.run(['git','diff','--cached','--check'],cwd=repo,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);excluded={}
if first.returncode:
    for line in first.stdout.decode().splitlines():
        m=re.match(r'^(.+):\d+: (?:trailing whitespace\.|new blank line at EOF\.)$',line)
        if m:
            path=m.group(1);rel=path.removeprefix(prefix);assert path.startswith(prefix) and rel in retained,path
            assert sha(repo/path)==retained[rel],path
            excluded[path]=dict(sha256=sha(repo/path),reason='Exact independently-reviewed immutable historical execution or review evidence; preserve original bytes')
    assert excluded,first.stdout.decode()
args=['git','diff','--cached','--check','--','.']+[':(exclude)'+path for path in sorted(excluded)]
check=subprocess.run(args,cwd=repo,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);assert check.returncode==0,check.stdout.decode()
assert not preflight.exists();preflight.mkdir()
acceptance=dict(utc=datetime.now(timezone.utc).isoformat(),status='Root accepts independent publication APPROVE after reading full report and verifying every sealed review/preparer/output identity; commit and push authorized by user',
    root_role='Publication preparer, prior independent mathematical referee2; independent publication reviewer leancert_examples authored neither proof nor publication',
    independent_review_sha256=sha(report),independent_evidence_sha256=sha(review/'EVIDENCE-MANIFEST.json'),preparer_sha256=sha(pub/'EVIDENCE-MANIFEST.json'),
    publication_sha256=r['publication_sha256'],unchanged_candidate_inputs=198,retained_operational_files=355,only_exact_preserved_paths_excluded=excluded,command=args,exit_code=0,
    root_visual='All three exact PDF pages individually displayed and inspected, matching independent publication review; no defects',
    original_target='Full original universal negative answer; genuine topology and Cardinal component counts, all eight exact exports retained',
    candidate='18b5ef3127da0ae4f68e09289f60fd4f6e3d9bcb',actual_Ubuntu_run=34725713519)
(preflight/'ROOT-ACCEPTANCE.json').write_text(json.dumps(acceptance,indent=2)+'\n')
(preflight/'commit_iv06_publication.py').write_bytes(Path(__file__).read_bytes())
outer=preflight/'EVIDENCE-MANIFEST.json';files={p.relative_to(preflight).as_posix():dict(sha256=sha(p),bytes=p.stat().st_size) for p in preflight.rglob('*') if p.is_file() and p!=outer}
outer.write_text(json.dumps(dict(file_count=len(files),files=files,inventory_rule='Every internal file except only this exact outer manifest; every nested manifest retained'),indent=2)+'\n')
subprocess.run(['git','add','--',str(preflight.relative_to(repo))],cwd=repo,check=True);subprocess.run(args,cwd=repo,check=True)
env=dict(os.environ,GIT_AUTHOR_NAME='George Stepaniants',GIT_COMMITTER_NAME='George Stepaniants',GIT_AUTHOR_EMAIL='',GIT_COMMITTER_EMAIL='')
done=subprocess.run(['git','-c','user.name=George Stepaniants','-c','user.email=','-c','commit.gpgsign=false','commit','-m','Publish Linux-verified IV-06 formalization and reviewed evidence'],cwd=repo,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
assert done.returncode==0,done.stdout.decode()
assert git('show','-s','--format=%ae%x00%ce','HEAD').rstrip(b'\n')==b'\0' and not git('status','--porcelain')
receipt=dict(commit=git('rev-parse','HEAD').decode().strip(),blank_author_and_committer_emails=True,worktree_clean=True,review_sha256=sha(report),root_acceptance_sha256=sha(preflight/'ROOT-ACCEPTANCE.json'),immutable_whitespace_exclusions=len(excluded))
Path('/tmp/nla-lean-formalization/IV-06-publication-commit.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
