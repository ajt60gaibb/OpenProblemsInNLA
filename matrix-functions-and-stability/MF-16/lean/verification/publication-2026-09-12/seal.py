from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,re,copy,collections,yaml
R=Path('/tmp/nla-lean-mf16-worktree');E=R/'matrix-functions-and-stability/MF-16';P=E/'lean';D=P/'verification/publication-2026-09-12';B=json.loads((D/'before.json').read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();git=lambda *a:subprocess.check_output(['git',*a],cwd=R)
assert git('rev-parse','HEAD').decode().strip()==B['candidate'];assert not (D/'EVIDENCE-MANIFEST.json').exists()
others={r:h for r,h in B['project_inputs'].items() if r not in ['README.md','formalization.yaml']};assert len(others)==292
for r,h in others.items():assert sha(P/r)==h,r
for r,a in [('README.md','README.linux-candidate.md'),('formalization.yaml','formalization.linux-candidate.yaml')]:assert sha(D/'archive'/a)==B['project_inputs'][r]
for r,h in B['immutable_operational_files'].items():assert sha(P/r)==h,r
assert len(B['immutable_operational_files'])==474
for n,count in [('verification/proof-freeze.json',182),('reviews/statement-freeze.json',45)]:
 f=json.loads((P/n).read_text());assert len(f['files'])==count
 for r,h in f['files'].items():assert sha(P/('verification/pre-candidate-README.md' if r=='README.md' else r))==h,r
 assert len(f['source_files'])==14
 for r,h in f['source_files'].items():
  assert sha(P/'verification/linux-2026-09-12/source'/r)==h,r
  assert hashlib.sha256(git('show',B['base']+':'+r)).hexdigest()==h,r
  if r not in {str(E.relative_to(R)/name) for name in ['README.md','problem.tex','problem.pdf']}:assert sha(R/r)==h,r
canonical=(E/'README.md').read_text();suffix=canonical[canonical.index('## Problem statement'):];assert hashlib.sha256(suffix.encode()).hexdigest()==B['canonical_target_sha256']
reg=json.loads((R/'problem_ids.json').read_text());assert len(reg)==217 and sha(R/'problem_ids.json')==B['registry_sha256']
for ident,r in reg.items():
 if ident!='MF-16':assert (R/r).read_bytes()==git('show',B['base']+':'+r),ident
expected={'CATALOG.md','README.md','RESOLVED.md','matrix-functions-and-stability/README.md'}|{str(E.relative_to(R)/r) for r in ['README.md','problem.tex','problem.pdf','lean/README.md','lean/formalization.yaml']}
assert set(git('diff','--name-only','HEAD').decode().splitlines())==expected
s=(R/'RESOLVED.md').read_text();old=git('show',B['base']+':RESOLVED.md').decode()
def omit(s):
 a=s.index('**MF-16 (');b=s.index('\n\n',a);return s[:a]+s[b:]
assert omit(s)==omit(old)
cur=yaml.safe_load((P/'formalization.yaml').read_text());orig=yaml.safe_load((D/'archive/formalization.linux-candidate.yaml').read_text());rem=copy.deepcopy(cur)
fields=[('status','scope'),('review','status'),('review','notes'),('review','linux_verification','status'),('review','linux_verification','note')]
for path in fields:
 a,b=rem,orig
 for k in path[:-1]:a,b=a[k],b[k]
 assert a[path[-1]]!=b[path[-1]];a[path[-1]]=b[path[-1]]
assert rem==orig
config=json.loads((P/'comparator.json').read_text());assert len(config['theorem_names'])==9 and config['definition_names']==[]
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
V=Path('/tmp/nla-lean-formalization/mf16-publication-pages');imgs={p.name:sha(p) for p in sorted(V.glob('page-*.png'))};assert len(imgs)==3
pixels=json.loads((D/'spacing-correction/pixel-check.json').read_text());assert pixels['pixels_identical'] and imgs==pixels['before']==pixels['after']
text=subprocess.check_output(['/opt/homebrew/bin/pdftotext','-layout',str(E/'problem.pdf'),'-']);(D/'pdf-text.txt').write_bytes(text)
norm=re.sub(r'\s+',' ',text.decode())
for word in ['George Stepaniants','Computing and Mathematical Sciences','California Institute of Technology','22 standard','Problem statement','complex','two'] : assert word in norm,word
visual={'reviewer':'/root','role':'Publication preparer and disclosed mathematical route contributor; no independent mathematical review','result':'PASS: all three full pages actually displayed and visually inspected','observations':'Page1 full attribution, original informal resolution and separate precise Lean scope; page2 complete unchanged original complex target; page3 all references and historical audits. No clipping, missing glyphs, overlaps or unreadable math. Paragraph-only metadata correction produces identical three PNG byte hashes.','pdf_sha256':sha(E/'problem.pdf'),'tex_sha256':sha(E/'problem.tex'),'images':imgs,'marker_scope':'See spacing-correction/correction.json for honest late-marker notice; marker not claimed before initial authoring.'}
(D/'VISUAL-REVIEW.json').write_text(json.dumps(visual,indent=2)+'\n')
r=subprocess.run(['git','diff','--check','HEAD'],cwd=R,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);(D/'diff-check.log').write_bytes(r.stdout);assert r.returncode==0
record={'verdict':'PASS ready for separate independent publication review; no publication commit or push','utc':datetime.now(timezone.utc).isoformat(),'candidate':B['candidate'],'base':B['base'],'reviewer':'/root','role':'Publication preparer, disclosed proof-route contributor, no independent mathematical review','candidate_inputs':294,'unchanged_nonwrapper_inputs':292,'exact_two_candidate_wrappers_archived':True,'frozen_proof_inputs':182,'frozen_statement_inputs':45,'original_sources':14,'Linux_evidence_files_unchanged':467,'root_operational_files_unchanged':7,'all_nested_manifests_preserved':True,'original_target_suffix_unchanged':True,'other_216_canonical_pages_unchanged':True,'RESOLVED_only_MF16_paragraph_changed':True,'all_217_permanent_IDs_unchanged':True,'manifest_only_changed_fields':['.'.join(p) for p in fields],'publication_files':{r:sha(R/r) for r in sorted(expected)},'status_counts':dict(counts),'actual_Linux_run':34735259429,'new_Lean_or_Linux_run':False,'independent_publication_review':'pending'}
(D/'INTEGRITY-CHECKS.json').write_text(json.dumps(record,indent=2)+'\n')
(D/'PUBLICATION-HANDOFF.md').write_text('''# MF-16 publication handoff

Ready for independent publication review; no publication commit or push. Root prepared this publication and is a disclosed proof-route contributor, not an independent final mathematical referee. Candidate 4e24448897a088ca9e7458379add1014c5d11e0c passed actual Ubuntu run 34735259429, independent operational review and root acceptance. Final mathematical referees are mf16_final_referee and formal_review_standards.

Nine exports refute the entire original all-palindrome/all-complex-positive-definite order-two word-uniqueness conjecture. The unchanged source word and matrices have two distinct actual positive definite solutions, proved using a genuine kernel Krawczyk certificate, Cayley-Hamilton and full complex matrix recovery. Stronger three-root and family claims are expressly outside scope. All nine exports, 22 actual standard-three reports, default-kernel replay and both real control suites passed. The 26-count final referee checks include four additional computational helpers.

Nine tracked publication files changed: root/category/catalog indexes, only the MF-16 RESOLVED paragraph, canonical README/TeX/PDF and two Lean wrappers. Exactly five YAML status/review fields change; original wrappers are archived. All 292 other candidate inputs, 467 Linux evidence files, seven root operational files, 182 frozen proof inputs, 45 statement inputs and fourteen source snapshots are unchanged through exact historical archives. Every nested manifest remains present. The original mathematical suffix is byte-identical; all 216 other canonical pages and all 217 permanent IDs are unchanged.

Both ID validators, seventeen ID tests, global math-format check, schema and nine-export coverage passed. Branch counts are 17 Lean verified,75 Solved,53 Open,72 Partially resolved. The rendered three-page PDF was actually displayed and inspected; no clipping or glyph problems. The full original target is on page2. Root corrected one publication-only workflow link and inherited metadata trailing spaces, preserving initial diagnostics and exact prior sources; final pages are pixel-identical to the viewed pages. The PDF marker was late and is disclosed, not retroactively claimed before first authoring.

George Stepaniants receives formalization credit with Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA and no email. Matthew J. Colbrook retains mathematical authorship; original-question attribution is retained. The actual Linux run verifies the immutable candidate, not these later wrappers. Ten fresh dependency checkouts reused 8690 matching official Mathlib cache files, not a full dependency-source rebuild. Nested Bubblewrap was denied UID-map setup before any inner write. No additional mathematical approval or external human review is claimed.

See before.json, INTEGRITY-CHECKS.json, checks.json and VISUAL-REVIEW.json. The complete publication inventory includes all files except its own exact path. Independent publication review is the remaining gate before normal blank-email commit, fork push and separate upstream main PR.
''')
(D/'seal.py').write_bytes(Path(__file__).read_bytes());outer=D/'EVIDENCE-MANIFEST.json';files={str(p.relative_to(D)):dict(sha256=sha(p),bytes=p.stat().st_size) for p in sorted(D.rglob('*')) if p.is_file() and p!=outer};outer.write_text(json.dumps({'file_count':len(files),'files':files,'inventory_rule':'All recursively present files; exact outer self-exclusion only, no basename exclusions'},indent=2)+'\n')
print(json.dumps({'handoff_sha256':sha(D/'PUBLICATION-HANDOFF.md'),'integrity_sha256':sha(D/'INTEGRITY-CHECKS.json'),'outer_sha256':sha(outer),'bound_files':len(files),'pdf_sha256':sha(E/'problem.pdf')},indent=2))
