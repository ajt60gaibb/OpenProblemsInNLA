from pathlib import Path
from datetime import datetime, timezone
import collections, copy, hashlib, json, re, subprocess, yaml

repo=Path('/tmp/nla-lean-iv06-worktree'); entry=repo/'intervals-and-absolute-value-equations/IV-06'
project=entry/'lean'; pub=project/'verification/publication-2026-09-12'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
git=lambda *a:subprocess.check_output(['git',*a],cwd=repo)
before=json.loads((pub/'before.json').read_text()); prefix=project.relative_to(repo).as_posix()+'/'
assert git('rev-parse','HEAD').decode().strip()==before['integration']
assert git('show','-s','--format=%ae%x00%ce','HEAD').rstrip(b'\n')==b'\0'
nonwrappers={r:h for r,h in before['candidate_inputs'].items() if r not in ['README.md','formalization.yaml']}
assert len(nonwrappers)==198
for r,h in nonwrappers.items(): assert sha(project/r)==h,r
for r,a in [('README.md','README.linux-candidate.md'),('formalization.yaml','formalization.linux-candidate.yaml')]:
    assert sha(pub/'archive'/a)==before['candidate_inputs'][r] and sha(project/r)!=before['candidate_inputs'][r],r
for r,h in before['operational_evidence'].items():assert sha(project/r)==h,r
freeze=json.loads((project/'verification/proof-freeze.json').read_text())
assert len(freeze['files'])==126
for r,v in freeze['files'].items():
    p=project/r if r!='README.md' else project/'verification/linux-candidate-2026-09-12/README.statement.md'
    assert sha(p)==v['sha256'] and p.stat().st_size==v['bytes'],r
for r,h in freeze['source_files'].items():
    assert sha(project/'verification/linux-2026-09-12/source'/r)==h,r
    assert hashlib.sha256(git('show',freeze['source_commit']+':'+r)).hexdigest()==h,r
    if r not in {entry.relative_to(repo).as_posix()+'/'+x for x in ['README.md','problem.tex','problem.pdf']}:
        assert sha(repo/r)==h,r
assert len(freeze['source_files'])==8
canonical=(entry/'README.md').read_text(); target=canonical[canonical.index('## Problem statement'):]
assert hashlib.sha256(target.encode()).hexdigest()==before['canonical_target_tail_sha256']
registry=json.loads((repo/'problem_ids.json').read_text())
assert len(registry)==217 and sha(repo/'problem_ids.json')==before['problem_ids_sha256']
for ident,h in before['other_canonical'].items():assert sha(repo/registry[ident])==h,ident
expected={'CATALOG.md','README.md','RESOLVED.md','intervals-and-absolute-value-equations/README.md'}
expected|={entry.relative_to(repo).as_posix()+'/'+r for r in ['README.md','problem.tex','problem.pdf','lean/README.md','lean/formalization.yaml']}
assert set(git('diff','--name-only','HEAD').decode().splitlines())==expected
preserved={}
for record in git('ls-tree','-rz',before['upstream']).split(b'\0'):
    if not record:continue
    metadata,raw=record.split(b'\t',1); mode,kind,oid=metadata.split(); r=raw.decode()
    if r in expected:continue
    p=repo/r; assert mode in [b'100644',b'100755'] and kind==b'blob' and p.is_file() and not p.is_symlink(),r
    data=p.read_bytes(); assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==oid.decode(),r
    preserved[r]=oid.decode()
(pub/'preserved-upstream-files.json').write_text(json.dumps(dict(base=before['upstream'],file_count=len(preserved),Git_blobs=preserved),indent=2)+'\n')
def omit(s):
    start=s.index('### IV-06 - Negative resolution'); end=s.index('\n## ',start+1)
    return s[:start]+s[end:]
assert omit((repo/'RESOLVED.md').read_text())==omit(git('show',before['upstream']+':RESOLVED.md').decode())
current=yaml.safe_load((project/'formalization.yaml').read_text()); original=yaml.safe_load((pub/'archive/formalization.linux-candidate.yaml').read_text())
remaining=copy.deepcopy(current)
fields=[('status','scope'),('review','status'),('review','notes'),('review','linux_verification','status'),('review','linux_verification','note')]
for path in fields:
    a,b=remaining,original
    for key in path[:-1]:a,b=a[key],b[key]
    assert a[path[-1]]!=b[path[-1]],path
    a[path[-1]]=b[path[-1]]
assert remaining==original
config=json.loads((project/'comparator.json').read_text())
assert [r['declaration'] for r in current['status']['main_results']]==config['theorem_names'] and len(config['theorem_names'])==8
assert config.get('definition_names',[])==[]
for key in ['statement_reports','proof_reports']:
    for r in current['review'][key]:assert sha(project/r['file'])==r['sha256'],r
assert current['project']['authors']==['George Stepaniants']
assert current['project']['affiliations']['George Stepaniants']=='Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA'
added='\n'.join(s[1:] for s in git('diff','--','*.md','*.yaml').decode().splitlines() if s.startswith('+') and not s.startswith('+++'))
assert not re.findall(r'[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}',added)
counts=collections.Counter(re.search(r'^\*\*Status:\*\*\s+([^\n]+)',(repo/p).read_text(),re.M).group(1).strip() for p in registry.values())
assert counts=={'Lean verified':17,'Solved':75,'Open':53,'Partially resolved':72}
prior=[i for i,p in registry.items() if i!='IV-06' and '**Status:** Lean verified' in (repo/p).read_text()];assert len(prior)==16
for doc in [entry/'README.md',project/'README.md']:
    for link in re.findall(r'\]\(([^)]+)\)',doc.read_text()):
        if not re.match(r'[a-z]+:',link):assert (doc.parent/link.split('#')[0]).exists(),(doc,link)
assert all(r['exit_code']==0 for r in json.loads((pub/'checks.json').read_text()))
assert not re.search(r'Overfull|Missing character',(pub/'render.log').read_text())
pages=list(Path('/tmp/nla-iv06-publication-pages').glob('page-*.png'));assert len(pages)==3
pdftext=subprocess.check_output(['/opt/homebrew/bin/pdftotext','-layout',str(entry/'problem.pdf'),'-']);(pub/'pdf-text.txt').write_bytes(pdftext)
normalized=re.sub(r'\s+',' ',re.sub(r'(?<=\w)-\s*\n\s*(?=\w)','',pdftext.decode()))
for word in ['George Stepaniants','Computing and Mathematical Sciences','California Institute of Technology','34725713519','not_componentBoundConjecture']:
    assert word in normalized,word
visual=dict(reviewer='/root',result='PASS: all three images individually displayed and inspected by the root publication preparer',
    observations='Page 1 shows clear status, source resolution and full author/department credit with all eight exports. Page 2 has Linux evidence, pins, commands and the entire original mathematical target. Page 3 retains original references and dated audits. No clipping, overlap, missing glyphs or unreadable formulas.',
    pdf_sha256=sha(entry/'problem.pdf'),tex_sha256=sha(entry/'problem.tex'),images={str(p):sha(p) for p in pages})
(pub/'VISUAL-REVIEW.json').write_text(json.dumps(visual,indent=2)+'\n')
r=subprocess.run(['git','diff','--check','HEAD'],cwd=repo,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);(pub/'diff-check.log').write_bytes(r.stdout);assert r.returncode==0,r.stdout
record=dict(verdict='PASS: ready for independent publication review; no commit or push',utc=datetime.now(timezone.utc).isoformat(),
    head=before['integration'],candidate=before['candidate'],upstream_base=before['upstream'],verified_input_count=200,
    unchanged_nonwrapper_inputs=198,preserved_nonREADME_proof_inputs=125,exact_prior_wrappers_archived=True,
    Linux_evidence_files_unchanged=348,root_acceptance_evidence_files_unchanged=7,all_nested_manifests_unchanged=True,
    permanent_IDs_preserved=217,other_canonical_pages_unchanged=216,prior_Lean_verified_entries_unchanged=prior,
    canonical_original_target_bytes_unchanged=True,RESOLVED_only_IV06_block_changed=True,
    changed_manifest_fields=['.'.join(p) for p in fields],remaining_manifest_structure_unchanged=True,
    status_counts=dict(counts),preserved_upstream_files=len(preserved),changed_tracked_files=sorted(expected),
    publication_sha256={r:sha(repo/r) for r in sorted(expected)},unchanged_nonwrapper_sha256=nonwrappers,
    all_retained_operational_sha256=before['operational_evidence'],new_Lean_build_or_Linux_execution=False,
    publication_preparer_role='Root authored publication metadata and also served as final mathematical referee 2; independent publication review by another agent is pending')
(pub/'INTEGRITY-CHECKS.json').write_text(json.dumps(record,indent=2)+'\n')
(pub/'PUBLICATION-HANDOFF.md').write_text('''# IV-06 publication handoff — 12 September 2026

**Ready for independent publication review. No publication commit or push.**

The branch integrates upstream `5830ed4fb06da0659414a3deb2a40ad327aca052` normally at `4c075f14209e85ef867eea90eacbea1e05e13a61`. All 200 immutable candidate inputs were preserved by integration. Candidate `18b5ef3127da0ae4f68e09289f60fd4f6e3d9bcb` passed actual Ubuntu run [34725713519](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34725713519), independent operational inspection and independent root acceptance.

The publication notices record the full original negative answer: the unchanged dimension-three independent-entry real box has at least four genuine connected components. Actual eigenvectors, real subset topology and Cardinal component counts are retained, without a finiteness premise. The consumed explicit kernel LeanCert singleton certificate is -18<0. The exact algebra, universal separator bounds and topological/cardinality proof remain unchanged. All eight exports, seventeen standard-three reports, default-kernel replay and both actual control suites passed.

Publication changes nine tracked files: the canonical README/TeX/PDF, two Lean project wrappers, IV-06 RESOLVED block and generated root/category/catalog indexes. Exactly five status/review fields change in formalization.yaml. All 198 other candidate inputs, 125 non-README proof-freeze inputs, archived historical README, eight original source snapshots, 348 Linux evidence files and seven root acceptance files remain byte-identical. Every nested manifest is retained. The exact preceding wrappers are archived.

All 217 IDs, 216 other canonical pages and sixteen prior Lean-verified entries are unchanged. The full original statement/reference/audit suffix is byte-identical; only the existing IV-06 RESOLVED block changes. Branch counts are 17 Lean verified, 75 Solved, 53 Open and 72 Partially resolved. All origin/upstream ID checks, seventeen tests, global math-format check, v0.4 schema and complete eight-export coverage pass. The canonical three-page PDF was rendered and every page individually displayed and inspected; the entire original target is on page 2, with no layout or glyph defect.

George Stepaniants receives AI-assisted formalization credit with Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, without an email. Matthew J. Colbrook retains mathematical counterexample credit; Hladík, Daney and Tsigaridas retain the question. Root prepared publication metadata and previously served as statement referee 1 and final proof referee 2. Standards performed operational inspection and was statement referee 2; inventory authored the proof. These roles do not add mathematical referees. The new independent publication reviewer should read the public wording, inspect the rendered pages and recheck the immutable bindings before root commits/pushes and opens an individual upstream PR.

The actual run remains bound to the candidate, not these metadata wrappers. Fresh Linux clones used ten exact pins and 8690 official Mathlib cache files; no full dependency-source rebuild is claimed. Nested Bubblewrap was denied UID-map creation before its inner write. All original artifact/log bytes are retained. No additional proof execution, external human review, official Tau Ceti endorsement or new priority is claimed by publication preparation.

`INTEGRITY-CHECKS.json`, `before.json`, `preserved-upstream-files.json`, `checks.json` and `VISUAL-REVIEW.json` bind the exact outputs and checks. The publication evidence inventory excludes only its own exact outer-manifest path.
''')
(pub/'seal.py').write_bytes(Path(__file__).read_bytes())
outer=pub/'EVIDENCE-MANIFEST.json'
files={p.relative_to(pub).as_posix():dict(bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(pub.rglob('*')) if p.is_file() and p!=outer}
outer.write_text(json.dumps(dict(file_count=len(files),files=files,inventory_rule='Every file below this directory except this exact outer manifest; all nested manifests included'),indent=2)+'\n')
print(json.dumps(dict(handoff_sha256=sha(pub/'PUBLICATION-HANDOFF.md'),integrity_sha256=sha(pub/'INTEGRITY-CHECKS.json'),manifest_sha256=sha(outer),evidence_files=len(files),pdf_sha256=sha(entry/'problem.pdf'),preserved_upstream_files=len(preserved)),indent=2))
