from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, os, re, subprocess, sys

ID=sys.argv[1]
settings={
 'MF-16':('mf16','matrix-functions-and-stability','12','-2','be5ba151839f7b89a38ec751a7e4a3a37e485205','4e24448897a088ca9e7458379add1014c5d11e0c',34735259429,'b55a5d5f63786e89672987db1bee6b3cb2a0b4b779f94e33e0b7349f630b6ed0','3dcf29724bbbc5181250a8009f42eb056d7808a4a7e3bce1f4cfb02e4a1357db'),
 'RA-08':('ra08','randomized-and-low-rank-approximation','13','','de6513d726e3f66d20730fdaef5ba99318ee7e8b','de6513d726e3f66d20730fdaef5ba99318ee7e8b',34735273999,'dec3aa545d22def70f1b38453f64f2aa8d905d4ba88f80da63eb5a2b43a046cb','6959afee28e870677542bface5421eace9325c5d385e35765fc9349a46882bda')}
short,cat,day,suffix,head,candidate,run,report_sha,review_outer_sha=settings[ID]
R=Path('/tmp/nla-lean-'+short+'-worktree');P=R/cat/ID/'lean';prefix=str(P.relative_to(R))+'/'
D=P/'verification/canonical-reproduction-addendum-2026-09-13'
V=P/('verification/canonical-reproduction-referee'+suffix+'-2026-09-13')
report=P/('reviews/canonical-reproduction-referee'+suffix+'-2026-09-13.md')
F=P/'verification/final-publication-preflight-2026-09-13';assert not F.exists()
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
git=lambda *a:subprocess.check_output(['git',*a],cwd=R)
assert git('rev-parse','HEAD').decode().strip()==head
assert not git('diff','--cached','--name-only')
assert h(report)==report_sha and h(V/'EVIDENCE-MANIFEST.json')==review_outer_sha
a=json.loads((D/'ADDENDUM.json').read_text());outputs=a['current_publication_files']
for r,v in outputs.items():assert h(R/r)==v,r
for r,v in a['all_existing_project_files_preserved'].items():assert h(P/r)==v,r
retained={};inventories={}
dirs=[D,V]
if ID=='RA-08':dirs += [P/('verification/'+x) for x in ['linux-2026-09-12','root-operational-2026-09-12','publication-2026-09-13','publication-referee-2026-09-13']]
for directory in dirs:
    outer=directory/'EVIDENCE-MANIFEST.json';m=json.loads(outer.read_text());actual=set()
    for r,v in m['files'].items():
        f=directory/r;value=v if isinstance(v,str) else v['sha256'];assert h(f)==value,(outer,r)
        if isinstance(v,dict) and 'bytes' in v:assert f.stat().st_size==v['bytes']
        assert f.resolve().is_relative_to(P.resolve())
        retained[str(f.resolve().relative_to(R.resolve()))]=value
        if not r.startswith('../'):actual.add(r)
    assert actual=={str(f.relative_to(directory)) for f in directory.rglob('*') if f.is_file() and f!=outer}
    retained[str(outer.relative_to(R))]=h(outer)
    inventories[str(outer.relative_to(P))]=dict(sha256=h(outer),bound_files=len(m['files']))
assert '**Status:** Lean verified' in (P.parent/'README.md').read_text()
marker='## Problem statement' if ID=='MF-16' else 'Let $`n\\ge2`$'
t=(P.parent/'README.md').read_text();assert hashlib.sha256(t[t.index(marker):].encode()).hexdigest()==a['original_target_suffix_sha256']
before=json.loads((P/f'verification/publication-2026-09-{day}/before.json').read_text())
assert h(R/'problem_ids.json')==before['registry_sha256'] and len(json.loads((R/'problem_ids.json').read_text()))==217
for r,v in before['immutable_operational_files'].items():assert h(P/r)==v,r
for r,v in before['project_inputs'].items():
    if r not in ['README.md','formalization.yaml']:assert h(P/r)==v,r
expected_tracked=set(a['after_canonical_files']) if ID=='MF-16' else set(outputs)
assert set(git('diff','--name-only').decode().splitlines())==expected_tracked
extra_reports=[report]
if ID=='RA-08':extra_reports.append(P/'reviews/publication-referee-2026-09-13.md')
stage=[*sorted(expected_tracked),*[str(p.relative_to(R)) for p in dirs+extra_reports]]
subprocess.run(['git','add','--',*stage],cwd=R,check=True)
staged=git('diff','--cached','--name-only').decode().splitlines()
assert all(p in expected_tracked or any(p==s or p.startswith(s+'/') for s in stage) for p in staged)
first=subprocess.run(['git','diff','--cached','--check'],cwd=R,stdout=subprocess.PIPE,stderr=subprocess.PIPE);assert not first.stderr
exceptions={}
if first.returncode:
    for line in first.stdout.decode().splitlines():
        m=re.match(r'^(.+):\d+: (?:trailing whitespace\.|new blank line at EOF\.)$',line)
        if m:
            p=m.group(1);assert p in retained and h(R/p)==retained[p],p
            exceptions[p]=dict(sha256=retained[p],reason='Exact sealed historical raw evidence; not normalized')
        elif re.match(r'^.+:\d+: ',line):raise AssertionError(line)
    assert exceptions,first.stdout.decode()
F.mkdir();raw=F/'git-diff-check-initial.log';raw.write_bytes(first.stdout)
if any(x.endswith((b' ',b'\t')) for x in first.stdout.splitlines()) or first.stdout.endswith(b'\n\n'):
    exceptions[str(raw.relative_to(R))]=dict(sha256=h(raw),reason='Exact raw output of the preceding staged whitespace check')
cmd=['git','diff','--cached','--check','--','.']+[':(exclude)'+p for p in sorted(exceptions)]
check=subprocess.run(cmd,cwd=R,stdout=subprocess.PIPE,stderr=subprocess.PIPE);assert check.returncode==0,check.stdout.decode()+check.stderr.decode()
accept=dict(utc=datetime.now(timezone.utc).isoformat(),status='Root accepts final separate publication addendum approval; ordinary commit/push/new upstream main PR authorized by user',problem=ID,root_role='Publication preparer and mathematical contributor; this acceptance adds no independent mathematical approval',reviewer='/root/formal_review_standards; independent of publication authoring, mathematical roles disclosed in report',report_sha256=report_sha,review_evidence_sha256=review_outer_sha,root_read_complete_initial_and_final_publication_reports=True,root_actually_viewed_all_three_final_pages=True,accepted_current_publication_files=outputs,prior_project_files_preserved=len(a['all_existing_project_files_preserved']),original_candidate=candidate,actual_Linux_run=run,immutable_operational_files_preserved=len(before['immutable_operational_files']),candidate_nonwrapper_inputs_preserved=len(before['project_inputs'])-2,all_217_IDs_and_original_target_preserved=True,complete_sealed_inventories=inventories,exact_hash_bound_whitespace_exceptions=exceptions,successful_whitespace_command=cmd,no_new_proof_execution_claimed=True)
(F/'ROOT-ACCEPTANCE.json').write_text(json.dumps(accept,indent=2)+'\n')
(F/'commit.py').write_bytes(Path(__file__).read_bytes())
outer=F/'EVIDENCE-MANIFEST.json';files={str(p.relative_to(F)):dict(sha256=h(p),bytes=p.stat().st_size) for p in sorted(F.rglob('*')) if p.is_file()};outer.write_text(json.dumps({'scope':'All files in this directory, exact outer self exclusion only','files':files},indent=2)+'\n')
subprocess.run(['git','add','--',str(F.relative_to(R))],cwd=R,check=True);subprocess.run(cmd,cwd=R,check=True)
for row in git('diff','--cached','--raw','--no-abbrev').decode().splitlines():
    metadata,path=row.split('\t',1);fields=metadata.split();assert fields[1] in ['100644','100755'];assert hashlib.sha256(git('cat-file','blob',fields[3])).hexdigest()==h(R/path),path
env=dict(os.environ,GIT_AUTHOR_NAME='George Stepaniants',GIT_COMMITTER_NAME='George Stepaniants',GIT_AUTHOR_EMAIL='',GIT_COMMITTER_EMAIL='')
message='Complete MF-16 canonical verification and reproduction documentation' if ID=='MF-16' else 'Publish Linux-verified RA-08 formalization and reviewed evidence'
r=subprocess.run(['git','-c','user.name=George Stepaniants','-c','user.email=','-c','commit.gpgsign=false','commit','-m',message],cwd=R,env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
assert r.returncode==0,r.stdout.decode()+r.stderr.decode()
assert git('show','-s','--format=%ae%x00%ce','HEAD').rstrip(b'\n')==b'\0'
assert not git('status','--porcelain')
receipt=dict(problem=ID,commit=git('rev-parse','HEAD').decode().strip(),candidate=candidate,blank_author_and_committer_emails=True,worktree_clean=True,root_publication_acceptance_sha256=h(F/'ROOT-ACCEPTANCE.json'),root_preflight_manifest_sha256=h(outer),exact_whitespace_exceptions=len(exceptions))
Path('/tmp/nla-lean-formalization/'+ID+'-final-publication-commit.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
