from pathlib import Path
import hashlib,json,re,subprocess
repo=Path('/private/tmp/nla-formalization-ie14-20260915');p=repo/'linear-systems-and-elimination/IE-14/lean';s=Path(__file__).parent
seal=json.loads((p/'reviews/statement-submission.json').read_text());base=seal['published_base'];checks=[]
def sha(b):return hashlib.sha256(b).hexdigest()
def ck(n,c):assert c,n;checks.append(n)
def git(*args):return subprocess.check_output(['git','-C',str(repo),*args])
ck('authoritative submission seal',sha((p/'reviews/statement-submission.json').read_bytes())=='9adea8e22570a4da8c3b8363697e66651ebd015ab7828d18b50c74f7ee6598e6')
ck('exact ten submitted boundary files',len(seal['input_sha256'])==10)
for f,h in seal['input_sha256'].items():
 ck('current submitted input '+f,sha((p/f).read_bytes())==h)
 ck('independent snapshot input '+f,sha((s/f).read_bytes())==h)
source=json.loads((p/'reviews/initial/source-hashes.json').read_text())
for f,record in source['files'].items():
 b=(repo/f).read_bytes();ck('complete unmodified source bytes '+f,len(b)==record['bytes'] and sha(b)==record['sha256'])
 ck('source exact published base '+f,b==git('show',base+':'+f))
ck('seven original complete source files',len(source['files'])==7)
ck('historical source identity distinguished from actual packaged source',source['files']['references/colbrook-recovered-2026-09-11/manuscripts/IE-14.tex']['bytes']==7141 and '5,942 bytes' in (p/'NUMERICAL_TARGETS.md').read_text() and '7,141-byte' in (p/'NUMERICAL_TARGETS.md').read_text())
registry=json.loads((repo/'problem_ids.json').read_text());ck('permanent 217 ID registry unchanged',len(registry)==217 and (repo/'problem_ids.json').read_bytes()==git('show',base+':problem_ids.json') and registry['IE-14']=='linear-systems-and-elimination/IE-14/README.md')
ck('canonical remains Solved','**Status:** Solved' in (p.parent/'README.md').read_text())
ck('no proof modules implemented',list((p/'NLA/IE14').glob('*.lean'))==[p/'NLA/IE14/Definitions.lean'])
ck('Solution imports only frozen definitions',[line.strip() for line in (p/'Solution.lean').read_text().splitlines() if line.strip() and not line.strip().startswith('--')]==['import NLA.IE14.Definitions'])
challenge=(p/'Challenge.lean').read_text();defs=(p/'NLA/IE14/Definitions.lean').read_text();config=json.loads((p/'comparator.json').read_text())
names=re.findall(r'^theorem (\w+)',challenge,re.M)
ck('all seven exact Comparator selections',len(names)==7 and config['theorem_names']==['NLA.IE14.'+name for name in names])
ck('seven deliberate Challenge placeholders',len(re.findall(r'\bsorry\b',challenge))==7)
ck('no definition holes or proof admissions in imported definitions',config['definition_names']==[] and re.search(r'\b(sorry|axiom|admit|native_decide|unsafe)\b',defs) is None)
ck('only allowed Comparator axioms',config['permitted_axioms']==['propext','Classical.choice','Quot.sound'])
log=(s/'referee-challenge-build.log').read_text();api=(s/'boundary-audit.log').read_text()
ck('independent fresh typecheck3008jobs7expectedholes','Build completed successfully (3008 jobs).' in log and log.count('declaration uses `sorry`')==7 and 'error:' not in log)
ck('independent actual definition and API inspection compiled','error:' not in api and all('NLA.IE14.'+name in api for name in names) and 'NNReal.instLinearOrder' in api and 'Matrix.det_fromBlocks₁₁' in api)
ck('reviewer API probe implements no proof declarations',re.search(r'^\s*(theorem|lemma|def|example|axiom)\b',(s/'BoundaryAudit.lean').read_text(),re.M) is None)
version=subprocess.check_output(['/private/tmp/nla-campaign-toolchain/lean-4.33.1-darwin_aarch64/bin/lean','--version']).decode().strip();ck('pinned actual compiler','4.33.1' in version and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version)
packages=[]
for dep in json.loads((p/'lake-manifest.json').read_text())['packages']:
 q=s/'.lake/packages'/dep['name'];head=subprocess.check_output(['git','-C',str(q),'rev-parse','HEAD']).decode().strip();dirty=subprocess.check_output(['git','-C',str(q),'status','--porcelain','--untracked-files=no']).decode()
 ck('pinned dependency '+dep['name'],head==dep['rev']);ck('tracked clean dependency '+dep['name'],not dirty);packages.append({'name':dep['name'],'commit':head,'tracked_clean':not dirty})
ck('contributor exact checker replay byte-identical',(s/'submitted-exact-results.json').read_bytes()==(p/'reviews/initial/exact-results.json').read_bytes())
ck('contributor complete source hashes independently replayed',(s/'submitted-source-hashes.json').read_bytes()==(p/'reviews/initial/source-hashes.json').read_bytes())
diagnostic=json.loads((s/'independent-exact.json').read_text());submitted=json.loads((s/'submitted-exact-results.json').read_text())
ck('1652 independently authored rational and complex checks',diagnostic['result']=='PASS' and diagnostic['checks_count']==1652 and diagnostic['contributor_checker_imported_or_executed'] is False)
ck('125 complete admissible complex sample tie paths',diagnostic['total_complete_tie_paths']==125 and len(diagnostic['all_tie_sample_results'])==40)
ck('contributor 27 exact cases all passed',submitted['all_passed'] and submitted['case_count']==27 and all(c['passed'] for c in submitted['cases']))
for own,other in zip(diagnostic['witnesses'],submitted['cases']):
 ck('independent witness comparison n'+str(own['n']),own['n']==other['n'] and own['growth']==other['growth'] and own['pivots']==other['pivot_values'])
api_files=['Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean','Mathlib/LinearAlgebra/Matrix/SchurComplement.lean','Mathlib/Data/Finset/Lattice/Fold.lean','Mathlib/Order/ConditionallyCompleteLattice/Basic.lean','Mathlib/Data/Nat/Fib/Basic.lean']
reference_files=['linear-systems-and-elimination/IE-05/lean/NLA/IE05/GEPP.lean','linear-systems-and-elimination/IE-05/lean/NLA/IE05/LUTrajectory.lean']
result={'reviewer':'OpenAI GPT-6 Codex /root/reference_api_review, independent non-implementing AI','phase':'exact pre-proof statement review','result':'APPROVE','published_base':base,'worktree_HEAD':git('rev-parse','HEAD').decode().strip(),'submission_sha256':sha((p/'reviews/statement-submission.json').read_bytes()),'input_sha256':seal['input_sha256'],'source_hashes':source,'additional_read_preparation_files_sha256':{f:sha((p/f).read_bytes()) for f in ['Solution.lean','reviews/initial/APIProbe.lean','reviews/initial/APIProbe.log']},'checks_count':len(checks),'checks':checks,'actual_compiler':version,'dependencies':packages,'reviewed_mathlib_sha256':{f:sha((s/'.lake/packages/mathlib'/f).read_bytes()) for f in api_files},'reviewed_existing_GEPP_reference_sha256':{f:sha((repo/f).read_bytes()) for f in reference_files},'execution':{'fresh_Challenge_build':{'exit':0,'jobs':3008,'intentional_holes':7},'BoundaryAudit':{'exit':0,'proof_implementation':False},'own_exact_diagnostics':{'exit':0,'checks':1652,'sample_complete_tie_paths':125},'submitted_checker_replay':{'exit':0,'cases':27,'results_and_source_hashes_byte_identical':True}},'primary_source':{'url':'https://pages.stat.wisc.edu/~bwu62/771/hingham2002.pdf','consulted_printed_pages':[193,173],'PDF_page_numbers':[222,202],'date':'2026-09-15','new_literature_completeness_search':False},'limits':['Statement and mathematically valid proof-plan approval only; no target theorem proved.','Finite diagnostics do not prove universal complex/all-tie/all-orders upper bounds.','No Solution proof build, LeanCert execution/consumption, axiom closure, Comparator, Linux or publication approval claimed.','Independent AI review, no external human review or official endorsement.']}
(s/'audit.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'result':'APPROVE','checks':len(checks),'input_count':10}))
