from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,re,copy,collections,yaml
R=Path('/tmp/nla-lean-ra08-worktree');E=R/'randomized-and-low-rank-approximation/RA-08';P=E/'lean';D=P/'verification/publication-2026-09-13';B=json.loads((D/'before.json').read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();git=lambda *a:subprocess.check_output(['git',*a],cwd=R)
assert git('rev-parse','HEAD').decode().strip()==B['candidate'];assert not (D/'EVIDENCE-MANIFEST.json').exists()
others={r:h for r,h in B['project_inputs'].items() if r not in ['README.md','formalization.yaml']};assert len(others)==611
for r,h in others.items():assert sha(P/r)==h,r
for r,a in [('README.md','README.linux-candidate.md'),('formalization.yaml','formalization.linux-candidate.yaml')]:assert sha(D/'archive'/a)==B['project_inputs'][r]
for r,h in B['immutable_operational_files'].items():assert sha(P/r)==h,r
assert len(B['immutable_operational_files'])==800
for n,count in [('verification/proof-freeze.json',450),('reviews/statement-freeze.json',39)]:
 f=json.loads((P/n).read_text());assert len(f['files'])==count
 for r,h in f['files'].items():assert sha(P/({'README.md':'verification/pre-candidate-README.md','formalization.yaml':'verification/pre-candidate-formalization.yaml'}.get(r,r)))==h,r
 assert len(f['source_files'])==10
 for r,h in f['source_files'].items():
  assert sha(P/'verification/linux-2026-09-12/source'/r)==h,r
  assert hashlib.sha256(git('show',B['base']+':'+r)).hexdigest()==h,r
  if r not in {str(E.relative_to(R)/name) for name in ['README.md','problem.tex','problem.pdf']}:assert sha(R/r)==h,r
canonical=(E/'README.md').read_text();suffix=canonical[canonical.index('Let $`n\\ge2`$'):];assert hashlib.sha256(suffix.encode()).hexdigest()==B['canonical_target_sha256']
reg=json.loads((R/'problem_ids.json').read_text());assert len(reg)==217 and sha(R/'problem_ids.json')==B['registry_sha256']
for ident,r in reg.items():
 if ident!='RA-08':assert (R/r).read_bytes()==git('show',B['base']+':'+r),ident
expected={'CATALOG.md','README.md','RESOLVED.md','randomized-and-low-rank-approximation/README.md'}|{str(E.relative_to(R)/r) for r in ['README.md','problem.tex','problem.pdf','lean/README.md','lean/formalization.yaml']}
assert set(git('diff','--name-only','HEAD').decode().splitlines())==expected
s=(R/'RESOLVED.md').read_text();old=git('show',B['base']+':RESOLVED.md').decode()
def omit(s):
 a=s.index('**RA-08 (');b=s.index('\n\n',a);return s[:a]+s[b:]
assert omit(s)==omit(old)
cur=yaml.safe_load((P/'formalization.yaml').read_text());orig=yaml.safe_load((D/'archive/formalization.linux-candidate.yaml').read_text());rem=copy.deepcopy(cur)
fields=[('status','scope'),('review','status'),('review','notes'),('review','linux_verification','status'),('review','linux_verification','note')]
for path in fields:
 a,b=rem,orig
 for k in path[:-1]:a,b=a[k],b[k]
 assert a[path[-1]]!=b[path[-1]];a[path[-1]]=b[path[-1]]
assert rem==orig
config=json.loads((P/'comparator.json').read_text());assert len(config['theorem_names'])==14 and config['definition_names']==[]
assert [r['declaration'] for r in cur['status']['main_results']]==config['theorem_names']
assert cur['project']['authors']==['George Stepaniants'];assert cur['project']['affiliations']['George Stepaniants']=='Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA'
for kind in ['statement_reports','proof_reports']:
 for rec in cur['review'][kind]:assert sha(P/rec['file'])==rec['sha256']
added='\n'.join(s[1:] for s in git('diff','--','*.md','*.yaml').decode().splitlines() if s.startswith('+') and not s.startswith('+++'));assert not re.search(r'[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}',added)
for doc in [E/'README.md',P/'README.md']:
 for url in re.findall(r'\]\(([^)]+)\)',doc.read_text()):
  if not re.match(r'[a-z]+:',url):assert (doc.parent/url.split('#')[0]).exists(),(doc,url)
counts=collections.Counter(re.search(r'^\*\*Status:\*\*\s+([^\n]+)',(R/r).read_text(),re.M).group(1).strip() for r in reg.values());assert counts=={'Lean verified':17,'Solved':75,'Open':53,'Partially resolved':72}
checks=json.loads((D/'checks.json').read_text());assert len(checks)==9 and all(x['exit_code']==0 for x in checks)
for x in checks:assert sha(D/x['log'])==x['log_sha256']
assert not re.search('Overfull|Missing character',(D/'render.log').read_text())
V=Path('/tmp/nla-lean-formalization/ra08-publication-pages');imgs={p.name:sha(p) for p in sorted(V.glob('page-*.png'))};assert len(imgs)==3
text=subprocess.check_output(['/opt/homebrew/bin/pdftotext','-layout',str(E/'problem.pdf'),'-']);(D/'pdf-text.txt').write_bytes(text)
norm=re.sub(r'\s+',' ',text.decode())
for word in ['George Stepaniants','Computing and Mathematical Sciences','California Institute of Technology','59 standard'] : assert word in norm,word
visual={'reviewer':'/root','role':'Publication preparer and mathematical coauthor, no independent mathematical review','result':'PASS: all three full pages actually displayed and visually inspected','observations':'Page1 complete attribution, dated informal solution and precise separate fourteen-export formal scope. Page2 unchanged original norm implication and shared eigenbasis conventions. Page3 all original references and dated audits. No clipping, glyph defects, overlapping text or unreadable formulas.','pdf_sha256':sha(E/'problem.pdf'),'tex_sha256':sha(E/'problem.tex'),'images':imgs,'marker_scope':'Successful once immediately before initial publication authoring; retained artifact-marker.json.'}
(D/'VISUAL-REVIEW.json').write_text(json.dumps(visual,indent=2)+'\n')
r=subprocess.run(['git','diff','--check','HEAD'],cwd=R,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);(D/'diff-check.log').write_bytes(r.stdout);assert r.returncode==0
record={'verdict':'PASS ready for separate independent publication review; no publication commit or push','utc':datetime.now(timezone.utc).isoformat(),'candidate':B['candidate'],'base':B['base'],'reviewer':'/root','role':'Publication preparer, disclosed mathematical coauthor, no independent mathematical review','candidate_inputs':613,'unchanged_nonwrapper_inputs':611,'exact_two_candidate_wrappers_archived':True,'frozen_proof_inputs':450,'frozen_statement_inputs':39,'original_sources':10,'Linux_evidence_files_unchanged':793,'root_operational_files_unchanged':7,'all_nested_manifests_preserved':True,'original_target_suffix_unchanged':True,'other_216_canonical_pages_unchanged':True,'RESOLVED_only_RA08_paragraph_changed':True,'all_217_permanent_IDs_unchanged':True,'manifest_only_changed_fields':['.'.join(p) for p in fields],'publication_files':{r:sha(R/r) for r in sorted(expected)},'status_counts':dict(counts),'actual_Linux_run':34735273999,'new_Lean_or_Linux_run':False,'independent_publication_review':'pending'}
(D/'INTEGRITY-CHECKS.json').write_text(json.dumps(record,indent=2)+'\n')
(D/'PUBLICATION-HANDOFF.md').write_text("""# RA-08 publication handoff — 13 September 2026

Ready for separate independent publication review, no publication commit or push. Root prepared wrappers as a disclosed proof coauthor, not an independent final mathematical referee. Actual candidate de6513d726e3f66d20730fdaef5ba99318ee7e8b passed Ubuntu run34735273999, both independent final mathematical approvals, independent operational review and root acceptance.

All fourteen exports negate the complete original concave spectral-transfer implication with genuine Euclidean norm/CFC, every original parameter/function and selected eigenbasis, allowing positive f(0). The unchanged six-dimensional witness has exact residual and optimal tails t while transformed error exceeds t. Exact compression, scalar minorant, actual CFC order/Rayleigh and material explicit-kernel LeanCert singleton sign certificate prove the result. Larger source contour ratio, separate Nyström sketch identity and ancillary nuclear results are outside scope. All fourteen exports,59 actual source standard-three/kernel reports, default-kernel replay and both real control suites passed. Local final referee counts61/62 include additional helper/consumer checks.

Nine tracked publication files: canonical README/TeX/PDF, only RA08 RESOLVED paragraph, root/category/catalog indexes and two Lean wrappers. Exactly five YAML status/review fields change. Both candidate wrappers are archived; all611 other candidate inputs,793 Linux files,seven root operational files,450 proof-freeze inputs,39 statement inputs andten original sources remain unchanged through exact historical archives. Every nested manifest is retained. Original mathematical suffix/all216 other canonical pages andall217 permanent IDs are unchanged. Branch counts17 Lean verified,75 Solved,53 Open,72 Partially resolved.

Both permanent-ID validators,17 ID tests,global math-format check,v0.4 schema andcomplete fourteen-export coverage pass. All three final PDF images were actually displayed and visually inspected, withno layout or glyph defect. Original target is onpage2. Artifact marker ran once before initial publication authoring. George Stepaniants receives full Caltech Computing andMathematical Sciences department affiliation andformalization credit,no email. Matthew J.Colbrook retains mathematical authorship andoriginal-question credit is preserved.

Independent final referees are leancert_examples andmf16_final_referee. The latter performed operational audit, the former later prepared candidate documents. Root coauthored proof andprepared publication, not independent mathematical review. Standards is main proof coauthor. Publication review is a separate metadata/preservation check that adds no mathematical approval. Actual Ubuntu evidence binds immutable candidate,not later wrappers; ten freshdependency pins reused8690 official Mathlib cache objects,not a full source rebuild. Nested Bubblewrap denied UID-map setup before inner write. No new local/remote proof check,human peerreview,official TauCeti endorsement or priority claimed by publication.

INTEGRITY-CHECKS.json,before.json,checks.json,VISUAL-REVIEW.json andcomplete exact-self-excluding publication manifest support independent review before normal blank-email commit,push andnew upstreammain PR.
""")
# Readable text only; no change to any mathematical or frozen source.
f=D/'PUBLICATION-HANDOFF.md';t=f.read_text()
for a,b in {'run347':'run 347','exports,59':'exports, 59','counts61/62':'counts 61/62','all611':'all 611','inputs,793':'inputs, 793','files,seven':'files, seven','files,450':'files, 450','inputs,39':'inputs, 39','andten':'and ten','suffix/all216':'suffix/all 216','andall217':'and all 217','counts17':'counts 17',',75':', 75',',53':', 53',',72':', 72',',17':', 17',',global':', global',',v0.4':', v0.4','andcomplete':'and complete','withno':'with no','onpage2':'on page 2','andMathematical':'and Mathematical','andformalization':'and formalization',',no email':', no email','J.Colbrook':'J. Colbrook','andoriginal':'and original','andmf16':'and mf16','andprepared':'and prepared',',not':', not','freshdependency':'fresh dependency','reused8690':'reused 8690',',human':', human',',official':', official','peerreview':'peer review','TauCeti':'Tau Ceti',',before':', before',',checks':', checks',',VISUAL':', VISUAL','andcomplete':'and complete',',push':', push','andnew':'and new','upstreammain':'upstream main'}.items():t=t.replace(a,b)
f.write_text(t)
(D/'seal.py').write_bytes(Path(__file__).read_bytes());outer=D/'EVIDENCE-MANIFEST.json';files={str(p.relative_to(D)):dict(sha256=sha(p),bytes=p.stat().st_size) for p in sorted(D.rglob('*')) if p.is_file() and p!=outer};outer.write_text(json.dumps({'file_count':len(files),'files':files,'inventory_rule':'All recursively present files; exact outer self-exclusion only, no basename exclusions'},indent=2)+'\n')
print(json.dumps({'handoff_sha256':sha(D/'PUBLICATION-HANDOFF.md'),'integrity_sha256':sha(D/'INTEGRITY-CHECKS.json'),'outer_sha256':sha(outer),'bound_files':len(files),'pdf_sha256':sha(E/'problem.pdf')},indent=2))
