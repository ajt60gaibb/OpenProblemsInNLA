from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re, subprocess, os

R=Path('/tmp/nla-lean-ra09-worktree');prefix='randomized-and-low-rank-approximation/RA-09/lean/';P=R/prefix
D=P/'verification/linux-candidate-2026-09-13';V=P/'verification/candidate-packaging-referee-2026-09-13'
O=P/'verification/root-candidate-2026-09-13';assert not O.exists()
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();git=lambda *a:subprocess.check_output(['git',*a],cwd=R)
assert git('rev-parse','HEAD').decode().strip()=='5830ed4fb06da0659414a3deb2a40ad327aca052'
assert not git('diff','--name-only') and not git('diff','--cached','--name-only')
report=P/'reviews/candidate-packaging-referee-2026-09-13.md'
assert h(report)=='9d74a02767975969022abd594e813bfde0c0c5b2a26f28f79623cffecde01d47'
assert h(V/'EVIDENCE-MANIFEST.json')=='596b608ad8c3344b8f5a7adf8a68aedfb30f7ba751d16d08f3a7b1e4bba4c02c'
assert h(P/'README.md')=='8607a0ff43d23a301775c5db62bcdbeb7af474aef2e3aeac559c4a11c08f02c3'
assert h(P/'formalization.yaml')=='8dc23f21024b4789f470f40d9a43c5de9489f6a0eb8b212d326c7cb1ce9046be'
install=json.loads((D/'INSTALLATION.json').read_text());retained={}
for r,v in install['baseline'].items():
    rel=install['archive_mapping'].get(r,r);assert h(P/rel)==v['sha256'],r;retained[prefix+rel]=v['sha256']
inventories={}
for directory in [D,V]:
    outer=directory/'EVIDENCE-MANIFEST.json';m=json.loads(outer.read_text());actual=set()
    for r,v in m['files'].items():
        p=directory/r;value=v if isinstance(v,str) else v['sha256'];assert h(p)==value,(outer,r)
        if isinstance(v,dict) and 'bytes' in v:assert p.stat().st_size==v['bytes']
        assert p.resolve().is_relative_to(P.resolve());retained[str(p.resolve().relative_to(R.resolve()))]=value
        if not r.startswith('../'):actual.add(r)
    assert actual=={str(p.relative_to(directory)) for p in directory.rglob('*') if p.is_file() and p!=outer}
    retained[str(outer.relative_to(R))]=h(outer);inventories[str(outer.relative_to(P))]=dict(sha256=h(outer),bound_files=len(m['files']))
F=json.loads((P/'verification/proof-freeze.json').read_text())
for r,v in F['source_files'].items():
    assert h(R/r)==v and hashlib.sha256(git('show',F['base']+':'+r)).hexdigest()==v,r
for r,v in F['files'].items():assert h(P/('verification/pre-candidate-README.md' if r=='README.md' else r))==v,r
assert '**Status:** Solved' in (P.parent/'README.md').read_text()
assert len(json.loads((R/'problem_ids.json').read_text()))==217
for path in [P/'README.md',P/'formalization.yaml']:
    assert not re.search(r'[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}',path.read_text())
before={str(p.relative_to(P)):h(p) for p in sorted(P.rglob('*')) if p.is_file()}
assert set(before)=={r.removeprefix(prefix) for r in git('ls-files','--others','--exclude-standard','--',prefix).decode().splitlines()}
subprocess.run(['git','add','--',prefix],cwd=R,check=True)
assert all(r.startswith(prefix) for r in git('diff','--cached','--name-only').decode().splitlines())
first=subprocess.run(['git','diff','--cached','--check'],cwd=R,stdout=subprocess.PIPE,stderr=subprocess.PIPE);assert not first.stderr
exceptions={}
if first.returncode:
    for line in first.stdout.decode().splitlines():
        m=re.match(r'^(.+):\d+: (?:trailing whitespace\.|new blank line at EOF\.)$',line)
        if m:
            path=m.group(1);assert path in retained and h(R/path)==retained[path],path
            exceptions[path]=dict(sha256=retained[path],reason='Exact already sealed source or raw historical evidence; no normalization')
        elif re.match(r'^.+:\d+: ',line):raise AssertionError(line)
    assert exceptions,first.stdout.decode()
O.mkdir();raw=O/'git-diff-check-initial.log';raw.write_bytes(first.stdout)
if any(x.endswith((b' ',b'\t')) for x in first.stdout.splitlines()) or first.stdout.endswith(b'\n\n'):
    exceptions[str(raw.relative_to(R))]=dict(sha256=h(raw),reason='Exact raw output of the preceding staged whitespace check')
cmd=['git','diff','--cached','--check','--','.']+[':(exclude)'+p for p in sorted(exceptions)]
c=subprocess.run(cmd,cwd=R,stdout=subprocess.PIPE,stderr=subprocess.PIPE);assert c.returncode==0,c.stdout.decode()+c.stderr.decode()
record=dict(utc=datetime.now(timezone.utc).isoformat(),status='Root accepts concrete independent packaging approval; commit and fork push for actual Linux authorized',root_role='Disclosed proof contributor and factual wrapper installer; not independent final mathematical or packaging reviewer',independent_packaging_report_sha256=h(report),independent_packaging_evidence_sha256=h(V/'EVIDENCE-MANIFEST.json'),root_read_complete_live_README_YAML_and_report=True,prior_inputs=before,prior_input_count=len(before),installation_sha256=h(D/'INSTALLATION.json'),final_review_gate_sha256=h(P/'verification/final-review-acceptance.json'),complete_package_inventories=inventories,proof_inputs_preserved=len(F['files']),original_source_Git_blobs_preserved=len(F['source_files']),archive_mapping=install['archive_mapping'],all_217_IDs_and_original_target_preserved=True,exact_hash_bound_whitespace_exceptions=exceptions,successful_whitespace_command=cmd,canonical_status='Solved, unchanged',actual_Linux_Comparator_default_kernel_controls='pending; this commit is submitted for their first authoritative run',new_local_proof_or_dependency_build=False)
(O/'ROOT-CHECKS.json').write_text(json.dumps(record,indent=2)+'\n');(O/'commit_candidate.py').write_bytes(Path(__file__).read_bytes())
outer=O/'EVIDENCE-MANIFEST.json';files={str(p.relative_to(O)):dict(sha256=h(p),bytes=p.stat().st_size) for p in sorted(O.rglob('*')) if p.is_file()};outer.write_text(json.dumps({'scope':'All files in this directory, exact outer self exclusion only','files':files},indent=2)+'\n')
subprocess.run(['git','add','--',str(O.relative_to(R))],cwd=R,check=True);subprocess.run(cmd,cwd=R,check=True)
for row in git('diff','--cached','--raw','--no-abbrev').decode().splitlines():
    metadata,path=row.split('\t',1);fields=metadata.split();assert fields[1] in ['100644','100755'];assert hashlib.sha256(git('cat-file','blob',fields[3])).hexdigest()==h(R/path),path
env=dict(os.environ,GIT_AUTHOR_NAME='George Stepaniants',GIT_COMMITTER_NAME='George Stepaniants',GIT_AUTHOR_EMAIL='',GIT_COMMITTER_EMAIL='')
c=subprocess.run(['git','-c','user.name=George Stepaniants','-c','user.email=','-c','commit.gpgsign=false','commit','-m','Add reviewed RA-09 Lean candidate for authoritative Linux verification'],cwd=R,env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE);assert c.returncode==0,c.stdout.decode()+c.stderr.decode()
assert git('show','-s','--format=%ae%x00%ce','HEAD').rstrip(b'\n')==b'\0' and not git('status','--porcelain')
receipt=dict(problem='RA-09',candidate=git('rev-parse','HEAD').decode().strip(),candidate_inputs=len(before)+len(files)+1,blank_author_and_committer_emails=True,worktree_clean=True,root_candidate_sha256=h(O/'ROOT-CHECKS.json'),root_evidence_sha256=h(outer),exact_whitespace_exceptions=len(exceptions),canonical_status='Solved, unchanged',actual_Linux='pending')
Path('/tmp/nla-lean-formalization/RA-09-candidate-commit.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
