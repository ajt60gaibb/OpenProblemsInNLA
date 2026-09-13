from pathlib import Path
from datetime import datetime, timezone
import collections,copy,hashlib,json,re,subprocess,yaml
repo=Path('/tmp/nla-lean-ie23-worktree');entry=repo/'linear-systems-and-elimination/IE-23';project=entry/'lean'
pub=project/'verification/publication-2026-09-12'; out=project/'verification/root-publication-2026-09-12'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest(); git=lambda *a:subprocess.check_output(['git',*a],cwd=repo)
head='ec703a43cd3343d02ad327ae6d682b04935bafac';candidate='a40e5608f61dd4086708cb2e03901ffd01e4c0a9';base='5830ed4fb06da0659414a3deb2a40ad327aca052'
assert not out.exists();assert git('rev-parse','HEAD').decode().strip()==head
assert sha(pub/'PUBLICATION-HANDOFF.md')=='f7cdb595ca243dd57434424bed3c9e64fdae27695ae1395b5e9d49b4259fce20'
assert sha(pub/'INTEGRITY-CHECKS.json')=='778bd2cd42058bcb83a0ef39da1939fc5e8b4b900541443151b30bf3c9bbd250'
assert sha(pub/'EVIDENCE-MANIFEST.json')=='5c06734ca949989a1007b7c1d96d1ee794d5ed65f69c3d00a8a5965bee3c60f4'
prefix=project.relative_to(repo).as_posix()+'/'
inputs={r.removeprefix(prefix):hashlib.sha256(git('show',candidate+':'+r)).hexdigest() for r in git('ls-tree','-r','--name-only',candidate,'--',prefix).decode().splitlines()}
assert len(inputs)==190
nonwrappers={r:h for r,h in inputs.items() if r not in ['README.md','formalization.yaml']}
for r,h in nonwrappers.items():assert sha(project/r)==h,r
for r,a in [('README.md','README.linux-candidate.md'),('formalization.yaml','formalization.linux-candidate.yaml')]:
    assert sha(pub/'archive'/a)==inputs[r] and sha(project/r)!=inputs[r]
retained={}
for name,mhash,count in [('linux-2026-09-12','3d4685d019c85ba80681551637f43ecf8bfc428a91dc8c985596405f36178da2',330),('root-operational-2026-09-12','b35250b043bb8ddf2bbbc5c03c20c771b89c15e91f18f2bc5af5495b0f17abe1',6),('publication-2026-09-12','5c06734ca949989a1007b7c1d96d1ee794d5ed65f69c3d00a8a5965bee3c60f4',32)]:
    root=project/'verification'/name;outer=root/'EVIDENCE-MANIFEST.json';assert sha(outer)==mhash
    files=json.loads(outer.read_text())['files'];assert len(files)==count
    actual={p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file() and p!=outer};assert actual==set(files)
    for r,v in files.items():assert sha(root/r)==v['sha256'] and (root/r).stat().st_size==v['bytes'],r
    retained.update({p.relative_to(project).as_posix():sha(p) for p in root.rglob('*') if p.is_file()})
assert len(retained)==371
freeze=json.loads((project/'reviews/proof-freeze.json').read_text());assert len(freeze['files'])==104
for r,v in freeze['files'].items():
    p=project/r if r!='README.md' else project/'verification/linux-candidate-2026-09-12/README.statement.md'
    assert sha(p)==v['sha256'] and p.stat().st_size==v['bytes'],r
assert len(freeze['source_files'])==8
for r,h in freeze['source_files'].items():
    assert sha(project/'verification/linux-2026-09-12/source'/r)==h,r
    assert hashlib.sha256(git('show',freeze['source_commit']+':'+r)).hexdigest()==h,r
    if r not in {entry.relative_to(repo).as_posix()+'/'+s for s in ['README.md','problem.tex','problem.pdf']}:assert sha(repo/r)==h,r
record=json.loads((pub/'INTEGRITY-CHECKS.json').read_text())
expected=set(record['changed_tracked_files']);assert len(expected)==9
assert set(git('diff','--name-only','HEAD').decode().splitlines())==expected
for r,h in record['publication_sha256'].items():assert sha(repo/r)==h,r
preserved={}
for row in git('ls-tree','-rz',base).split(b'\0'):
    if not row:continue
    metadata,raw=row.split(b'\t',1);mode,kind,oid=metadata.split();r=raw.decode()
    if r in expected:continue
    p=repo/r;assert p.is_file() and not p.is_symlink() and mode in [b'100644',b'100755'] and kind==b'blob',r
    b=p.read_bytes();assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==oid.decode(),r
    preserved[r]=oid.decode()
assert len(preserved)==6967
registry=json.loads((repo/'problem_ids.json').read_text());assert len(registry)==217
prior=[]
for i,r in registry.items():
    if i=='IE-23':continue
    assert (repo/r).read_bytes()==git('show',base+':'+r),i
    if '**Status:** Lean verified' in (repo/r).read_text():prior.append(i)
assert len(prior)==16
old=git('show',candidate+':'+entry.relative_to(repo).as_posix()+'/README.md').decode();new=(entry/'README.md').read_text()
assert old[old.index('## Problem statement'):]==new[new.index('## Problem statement'):]
def omit(s):
    a=s.index('### IE-23 - Negative resolution');b=s.index('\n## ',a+1);return s[:a]+s[b:]
assert omit((repo/'RESOLVED.md').read_text())==omit(git('show',base+':RESOLVED.md').decode())
current=yaml.safe_load((project/'formalization.yaml').read_text());original=yaml.safe_load((pub/'archive/formalization.linux-candidate.yaml').read_text());remaining=copy.deepcopy(current)
fields=[('status','scope'),('review','status'),('review','notes'),('review','linux_verification','status'),('review','linux_verification','note')]
for keys in fields:
    a,b=remaining,original
    for key in keys[:-1]:a,b=a[key],b[key]
    assert a[keys[-1]]!=b[keys[-1]],keys
    a[keys[-1]]=b[keys[-1]]
assert remaining==original
config=json.loads((project/'comparator.json').read_text())
assert len(config['theorem_names'])==8 and [x['declaration'] for x in current['status']['main_results']]==config['theorem_names'] and not config.get('definition_names',[])
assert current['project']['authors']==['George Stepaniants'] and current['project']['affiliations']['George Stepaniants']=='Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA'
for kind in ['statement_reports','proof_reports']:
    for r in current['review'][kind]:assert sha(project/r['file'])==r['sha256'],r
counts=collections.Counter(re.search(r'^\*\*Status:\*\*\s+([^\n]+)',(repo/r).read_text(),re.M).group(1).strip() for r in registry.values());assert counts=={'Lean verified':17,'Solved':75,'Open':53,'Partially resolved':72}
added='\n'.join(s[1:] for s in git('diff','--','*.md','*.yaml').decode().splitlines() if s.startswith('+') and not s.startswith('+++'))
assert not re.findall(r'[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}',added)
for doc in [entry/'README.md',project/'README.md']:
    for link in re.findall(r'\]\(([^)]+)\)',doc.read_text()):
        if not re.match(r'[a-z]+:',link):assert (doc.parent/link.split('#')[0]).exists(),(doc,link)
visual=json.loads((pub/'VISUAL-REVIEW.json').read_text())
assert sha(entry/'problem.pdf')==visual['pdf_sha256']=='86af737d7c15ef1456365a3bd17cfda477448d3c00d66303ffcb92859247f126'
assert sha(entry/'problem.tex')==visual['tex_sha256'] and visual['pages']==3
for p,h in visual['images'].items():assert sha(pub/p)==h,p
out.mkdir()
r=subprocess.run(['git','diff','--check','HEAD'],cwd=repo,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);(out/'tracked-diff-check.log').write_bytes(r.stdout);assert r.returncode==0,r.stdout
checks=dict(status='APPROVE publication; ready for blank-email commit, normal fork push and individual upstream PR',utc=datetime.now(timezone.utc).isoformat(),reviewer='/root',
    role='Independent of proof author and publication preparer; previously independent statement/final proof referee 2 and operational acceptance coordinator. This is not an additional mathematical referee.',
    candidate=candidate,run=34725525250,integration=head,upstream=base,reading_scope='Complete canonical page, live guide, entire manifest, IE23 RESOLVED block, handoff and integrity records read; all three exact PDF images displayed and visually inspected. Actual Linux evidence had already been independently accepted and all retained bytes were rehashed here. No proof rerun.',
    candidate_inputs=190,unchanged_nonwrapper_inputs=nonwrappers,all_retained_evidence=retained,
    original_sources=8,proof_freeze_nonREADME_inputs=103,publication_sha256=record['publication_sha256'],
    all_other_canonical_pages=216,permanent_ids=217,prior_Lean_verified_entries=prior,preserved_upstream_files=6967,
    only_changed_manifest_fields=['.'.join(x) for x in fields],status_counts=dict(counts),pdf_pages_individually_viewed=3,
    math_scope='Full original universal complex induced-norm uniqueness conjecture negated by exact p=4 witness with two genuine global minimizers over every complex right inverse; stronger all-p source results expressly outside exports',
    execution_scope='Actual Ubuntu/default kernel/eight Comparator exports, sixteen standard-three reports and both full real controls; no numerical interval certificate for this pure exact LeanCert kernel-audited proof',
    identity_and_roles='George full Caltech CMS affiliation without email; Colbrook mathematics and Dokmanic-Gribonval source credit. Proof author operational inspection separately accepted by root; preparer was final math referee1.',
    visual_findings='No clipping, overlaps, missing glyphs or unreadable formulas. Original complete target together on page 2. Three pages retain every original reference and historical audit. Page1-to-page2 prose continuation is readable.',
    new_Lean_or_Linux_run=False)
(out/'ROOT-CHECKS.json').write_text(json.dumps(checks,indent=2)+'\n')
(out/'INDEPENDENT-REVIEW.md').write_text('''# IE-23 independent publication review

**APPROVE publication of the complete original negative answer.** Reviewer: `/root`, 12 September 2026. Root authored neither the Lean proof nor these publication documents; root previously served as independent statement/final proof referee 2 and separately accepted the actual Linux operational inspection. This publication review is not an extra mathematical referee.

I read the full canonical page, project guide, manifest, exact IE-23 resolution block, handoff and integrity evidence. The public scope agrees with the reviewed original definitions and completed eight-export proof: the unchanged p=4 witness gives two distinct genuine global minimizers over all complex right inverses and refutes the entire universal conjecture. The source's stronger all-p formulas, classifications and higher-dimensional families are explicitly outside the Lean exports. The exact supremum/rank/inverse/real-power and all-competitor semantics remain intact. LeanCert supplies explicit kernel trust auditing of this pure exact proof; no numerical interval certificate is claimed.

I independently compared every candidate input with immutable Git revision a40e5608f61dd4086708cb2e03901ffd01e4c0a9. Only README and the current manifest change among 190 inputs; their exact prior bytes are archived and all other 188 remain unchanged. The metadata differences are exactly five status/review fields. All 103 non-README proof-freeze inputs, the historical README archive, eight original source snapshots, all 331 Linux files and seven root acceptance files remain intact. I also checked the complete 33-file preparer package. Every nested manifest is included. The actual Ubuntu run 34725525250 remains the proof execution record, and this review does not claim a new run over publication metadata.

Actual execution and source identity were already independently accepted in the sealed root operational record. These publication notices accurately report eight Comparator matches, default-kernel replay, sixteen permitted-axiom reports and both real control suites. Ten clean exact dependency clones used 8690 official Mathlib cache files; no full dependency-source rebuild or general sandbox-security theorem is asserted. The nested Bubblewrap UID-map denial is accurately limited to the observed pre-write failure. The proof author's operational role and the separate root acceptance are explicit.

All 217 permanent IDs, all 216 other canonical pages, all sixteen prior verified entries and 6967 unaffected upstream files are byte-identical. The original IE-23 problem/reference/audit suffix remains unchanged; only its existing RESOLVED block changes. Nine tracked publication files change. Branch counts are 17 Lean verified, 75 Solved, 53 Open and 72 Partially resolved. The preparer's origin/upstream validators, seventeen ID tests, catalog regeneration, full math-format check, v0.4 schema and eight-export checks are retained and pass. No change to code or metadata after those checks required another proof run.

I individually displayed all three exact rendered PDF pages. The publication status, original mathematical credit, George's full department/university affiliation, eight exports, source and execution links and commands are readable. The entire original target is on page 2; original references and historical audits are retained on page 3. No clipping, overlap, missing glyph or mathematical rendering defect was found. The minor paragraph continuation across pages is readable and complete.

George Stepaniants receives AI-assisted formalization credit with Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA; no email is added. Matthew J. Colbrook retains mathematical authorship, and Ivan Dokmanić and Rémi Gribonval retain original example/question credit. Publication preparer inventory was final mathematical referee1; root was referee2. These roles remain two mathematical referees. No human peer review, official Tau Ceti endorsement, author endorsement or new priority is claimed.

The exact checks and 371 retained evidence-file hashes are in ROOT-CHECKS.json. Normal blank-email publication commit and fork push, followed by the individual upstream PR requesting main integration, are approved within the user's existing authorization.
''')
(out/'review_ie23_publication.py').write_bytes(Path(__file__).read_bytes())
outer=out/'EVIDENCE-MANIFEST.json';files={p.relative_to(out).as_posix():dict(sha256=sha(p),bytes=p.stat().st_size) for p in sorted(out.rglob('*')) if p.is_file() and p!=outer}
outer.write_text(json.dumps(dict(files=files,file_count=len(files),inventory_rule='Every internal file except this exact outer manifest; nested manifests included'),indent=2)+'\n')
print(json.dumps(dict(approval=checks['status'],review_sha256=sha(out/'INDEPENDENT-REVIEW.md'),checks_sha256=sha(out/'ROOT-CHECKS.json'),manifest_sha256=sha(outer)),indent=2))
