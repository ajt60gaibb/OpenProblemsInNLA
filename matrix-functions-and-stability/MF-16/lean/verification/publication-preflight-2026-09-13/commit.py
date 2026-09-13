from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,re,os
R=Path('/tmp/nla-lean-mf16-worktree');prefix='matrix-functions-and-stability/MF-16/lean/';P=R/prefix;D=P/'verification/publication-2026-09-12';V=P/'verification/publication-referee-2-2026-09-13';report=P/'reviews/publication-referee-2-2026-09-13.md';F=P/'verification/publication-preflight-2026-09-13'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();git=lambda *a:subprocess.check_output(['git',*a],cwd=R)
C='4e24448897a088ca9e7458379add1014c5d11e0c';assert git('rev-parse','HEAD').decode().strip()==C and not F.exists()
assert sha(report)=='874d55d200aa653acefdf5ee7bcbd149915ff28490654f11b0e3afe9944b4cdf';assert sha(V/'EVIDENCE-MANIFEST.json')=='761b48f574fa90d6b751a1af724c2ef3cdabea0c9a32cba721f23b76d537fd1c';assert sha(D/'EVIDENCE-MANIFEST.json')=='602c7b7a3c2dd65fd22b81d0cd710ae8ba7ae196bed7f398df0d49d8093df818'
rec=json.loads((D/'INTEGRITY-CHECKS.json').read_text());before=json.loads((D/'before.json').read_text());outputs=rec['publication_files'];assert len(outputs)==9
for r,h in outputs.items():assert sha(R/r)==h,r
for r,h in before['project_inputs'].items():
 if r not in ['README.md','formalization.yaml']:assert sha(P/r)==h,r
retained={}
for directory,num,external in [(P/'verification/linux-2026-09-12',466,set()),(P/'verification/root-operational-2026-09-12',6,set()),(D,33,set()),(V,16,{'../../reviews/publication-referee-2-2026-09-13.md'})]:
 outer=directory/'EVIDENCE-MANIFEST.json';d=json.loads(outer.read_text());assert len(d['files'])==num
 actual={str(q.relative_to(directory)) for q in directory.rglob('*') if q.is_file() and q!=outer};assert actual==set(d['files'])-external
 for rel,v in d['files'].items():
  q=(directory/rel).resolve();assert q.is_relative_to(P.resolve()) and not q.is_symlink();assert sha(q)==v['sha256'] and q.stat().st_size==v['bytes'];retained[str(q.relative_to(P.resolve()))]=sha(q)
 retained[str(outer.relative_to(P))]=sha(outer)
assert sha(R/'problem_ids.json')==before['registry_sha256']
t=(P.parent/'README.md').read_text();assert hashlib.sha256(t[t.index('## Problem statement'):].encode()).hexdigest()==before['canonical_target_sha256']
remote=json.loads(Path('/tmp/nla-lean-formalization/mf16-ra08-prepublication-remote.json').read_text());assert remote['upstream']==before['base'];assert all(x['state']=='MERGED' for x in remote['MF16_PRs'])
dirs=[prefix+'verification/'+n for n in ['linux-2026-09-12','root-operational-2026-09-12','publication-2026-09-12','publication-referee-2-2026-09-13']];reportpath=str(report.relative_to(R))
subprocess.run(['git','add','--',*outputs,*dirs,reportpath],cwd=R,check=True)
for p in git('diff','--cached','--name-only').decode().splitlines():assert p in outputs or p==reportpath or any(p.startswith(d+'/') for d in dirs),p
first=subprocess.run(['git','diff','--cached','--check'],cwd=R,stdout=subprocess.PIPE,stderr=subprocess.PIPE);assert not first.stderr
excluded={}
if first.returncode:
 for line in first.stdout.decode().splitlines():
  m=re.match(r'^(.+):\d+: (?:trailing whitespace\.|new blank line at EOF\.)$',line)
  if m:
   p=m.group(1);rel=p.removeprefix(prefix);assert p.startswith(prefix) and rel in retained,p;assert sha(R/p)==retained[rel];excluded[p]={'sha256':retained[rel],'reason':'Exact sealed immutable raw historical evidence; no normalization'}
 assert excluded,first.stdout.decode()
F.mkdir();raw=F/'git-diff-check-initial.log';raw.write_bytes(first.stdout)
if any(x.endswith((b' ',b'\t')) for x in first.stdout.splitlines()) or first.stdout.endswith(b'\n\n'):excluded[str(raw.relative_to(R))]={'sha256':sha(raw),'reason':'Exact raw output of the preceding staged whitespace check'}
cmd=['git','diff','--cached','--check','--','.']+[':(exclude)'+p for p in sorted(excluded)]
r=subprocess.run(cmd,cwd=R,stdout=subprocess.PIPE,stderr=subprocess.PIPE);assert r.returncode==0,r.stdout.decode()+r.stderr.decode()
accept={'utc':datetime.now(timezone.utc).isoformat(),'status':'Root accepts independent publication APPROVE; user authorized ordinary commit, push and new upstream main PR','root_role':'Publication preparer and proof-route contributor, not an independent final mathematical referee','independent_publication_reviewer':'/root/formal_review_standards, also original independent final referee2; no new math approval','report_sha256':sha(report),'report_evidence_sha256':sha(V/'EVIDENCE-MANIFEST.json'),'publication_evidence_sha256':sha(D/'EVIDENCE-MANIFEST.json'),'candidate':C,'actual_Linux_run':34735259429,'publication_files':outputs,'candidate_nonwrapper_inputs_unchanged':292,'Linux_and_root_operational_files_unchanged':474,'original_target_suffix_unchanged':True,'all_217_IDs_preserved':True,'root_full_report_read':True,'root_all_three_PDF_pages_actually_viewed':True,'no_new_proof_run_claimed':True,'exact_hash_bound_whitespace_exceptions':excluded,'successful_whitespace_command':cmd,'upstream_remote_check':remote}
(F/'ROOT-ACCEPTANCE.json').write_text(json.dumps(accept,indent=2)+'\n');(F/'commit.py').write_bytes(Path(__file__).read_bytes());outer=F/'EVIDENCE-MANIFEST.json';fm={str(q.relative_to(F)):dict(sha256=sha(q),bytes=q.stat().st_size) for q in F.rglob('*') if q.is_file()};outer.write_text(json.dumps({'files':fm,'file_count':len(fm),'inventory_rule':'Every actual file except this exact outer manifest'},indent=2)+'\n')
subprocess.run(['git','add','--',str(F.relative_to(R))],cwd=R,check=True);subprocess.run(cmd,cwd=R,check=True)
# Verify actual staged blobs before the commit.
for row in git('diff','--cached','--raw','--no-abbrev').decode().splitlines():
 metadata,path=row.split('\t',1);fields=metadata.split();oid=fields[3];assert fields[1] in ['100644','100755'];assert hashlib.sha256(git('cat-file','blob',oid)).hexdigest()==sha(R/path),path
E=dict(os.environ,GIT_AUTHOR_NAME='George Stepaniants',GIT_COMMITTER_NAME='George Stepaniants',GIT_AUTHOR_EMAIL='',GIT_COMMITTER_EMAIL='')
r=subprocess.run(['git','-c','user.name=George Stepaniants','-c','user.email=','-c','commit.gpgsign=false','commit','-m','Publish Linux-verified MF-16 formalization and reviewed evidence'],cwd=R,env=E,stdout=subprocess.PIPE,stderr=subprocess.PIPE);assert r.returncode==0,r.stdout.decode()+r.stderr.decode()
assert git('show','-s','--format=%ae%x00%ce','HEAD').rstrip(b'\n')==b'\0';assert not git('status','--porcelain')
receipt={'problem':'MF-16','commit':git('rev-parse','HEAD').decode().strip(),'candidate':C,'blank_author_and_committer_emails':True,'worktree_clean':True,'root_publication_acceptance_sha256':sha(F/'ROOT-ACCEPTANCE.json'),'root_preflight_manifest_sha256':sha(outer),'exact_whitespace_exceptions':len(excluded)}
Path('/tmp/nla-lean-formalization/MF-16-publication-commit.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
