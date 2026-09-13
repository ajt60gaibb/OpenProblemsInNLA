"""Independent RA09 source/API/rubric audit, adapted from this referee's RA08
input-identity infrastructure. All comparisons and searches are executed afresh.
"""
from pathlib import Path
import hashlib,json,subprocess
E=Path(__file__).resolve().parent
P=E.parents[1];R=P.parents[2]
D=Path('/tmp/nla-lean-mi22-worktree/matrix-inequalities-and-norms/MI-22/lean/.lake/packages')
S=Path('/tmp/nla-lean-formalization/standards')
sha=lambda b:hashlib.sha256(b).hexdigest()
blob=lambda b:hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
git=lambda p,*a:subprocess.check_output(['git','-C',str(p),*a])
apis={}
import re
spec=json.loads((P/'verification/final/primary-api-inputs.json').read_text())
names={}
for key in spec:
 dep,path=key.split('/',1);names.setdefault(dep,[]).append(path)
names['mathlib'].extend(['Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Unital.lean',
 'Mathlib/Analysis/CStarAlgebra/Matrix.lean','Mathlib/Analysis/Matrix/PosDef.lean'])
pins={'leancert':'621a43d7cf21f87872392a01e874f2f1dbddc926','mathlib':'0df444a360eaa60ab8c11dca51a86af692955474'}
for dep,paths in names.items():
 for p in paths:
    raw=(D/dep/p).read_bytes()
    assert raw==git(D/dep,'show',pins[dep]+':'+p)
    apis[dep+'/'+p]={'sha256':sha(raw),'bytes':len(raw),'commit':pins[dep],
      'git_blob':blob(raw),'scope':'Relevant exact Frobenius/CFC/PSD/spectral/concavity definitions and proofs, LeanCert kernel trust classifier, and reuse searches; no complete library audit claimed'}
manifest=json.loads((S/'MANIFEST.json').read_text())
commit=json.loads((S/'TauCetiProject_TauCetiReview-commit.json').read_text())
tree=json.loads((S/'TauCetiProject_TauCetiReview-tree.json').read_text())
assert commit['sha']=='afb424eda89e8ac96d9eb69f6a88972055a4cd1b'
assert tree['sha']==commit['sha'] and not tree['truncated']
def verify_tree(directory,expected):
    children=[r for r in tree['tree'] if r['path'].rpartition('/')[0]==directory]
    def order(r):
        return (r['path'].rpartition('/')[2]+('/' if r['type']=='tree' else '')).encode()
    raw=b''.join((str(int(r['mode']))+' '+r['path'].rpartition('/')[2]).encode()+
       b'\0'+bytes.fromhex(r['sha']) for r in sorted(children,key=order))
    computed=hashlib.sha1(b'tree '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
    assert computed==expected,(directory,computed,expected)
    for r in children:
        if r['type']=='tree':verify_tree(r['path'],r['sha'])
verify_tree('',commit['commit']['tree']['sha'])
blobs={r['path']:r['sha'] for r in tree['tree'] if r['type']=='blob'}
rubrics={}
for f in sorted((S/'sources/TauCetiProject/TauCetiReview/rubrics').glob('*.md')):
 raw=f.read_bytes();rel=str(f.relative_to(S))
 assert sha(raw)==manifest[rel]['sha256'] and blob(raw)==blobs['rubrics/'+f.name]
 rubrics['rubrics/'+f.name]={'sha256':sha(raw),'bytes':len(raw),'git_blob':blob(raw)}
assert len(rubrics)==12
protocol={}
for p in ['AGENTS.md','docs/lean/REVIEW.md','docs/lean/README.md','tools/lean/HARNESS.md']:
 raw=(R/p).read_bytes();assert raw==git(R,'show','5830ed4fb06da0659414a3deb2a40ad327aca052:'+p)
 protocol[p]={'sha256':sha(raw),'bytes':len(raw),'git_blob':blob(raw)}
assert protocol['docs/lean/REVIEW.md']['sha256']=='d967ddce620d4e754e2f9c25548f30cb537f76f4ddcf8ecf2574945bcd332553'
examples={}
for repo,rev,paths in [
(Path('/Users/georgestepaniants/Research/Forsythe'),'8d1b0c0545a77b40245e84705aa7d273e6c81e62',
 ['lean-proof/Solution.lean','lean-proof/ProofProject/RestartFourRootCollarCertificates.lean','lean-proof/reproduction/README.md']),
(Path('/tmp/nla-lean-formalization/leancert-examples/Schiffer'),'2938e277969c329caf154e48a3d8823f3635c7f1',
 ['Schiffer/Challenge.lean'])]:
 assert git(repo,'rev-parse','HEAD').decode().strip()==rev
 for p in paths:
    raw=(repo/p).read_bytes();assert raw==git(repo,'show',rev+':'+p)
    examples[repo.name+'/'+p]={'sha256':sha(raw),'bytes':len(raw),'commit':rev,
       'git_blob':blob(raw),'scope':'Architecture and relevant kernel-certificate excerpts only, not an independent proof audit or copied implementation'}
result={'result':'PASS','actual_library_inputs':apis,'rubric_commit':commit['sha'],
'rubric_commit_receipt_sha256':sha((S/'TauCetiProject_TauCetiReview-commit.json').read_bytes()),
'rubric_tree_receipt_sha256':sha((S/'TauCetiProject_TauCetiReview-tree.json').read_bytes()),
'rubrics':rubrics,'repository_protocol':protocol,'requested_examples':examples,
'reading_scope':'All 12 complete Tau Ceti rubric files; repository adaptation applies and does not import Tau Ceti roadmap/compatibility policy. Actual scoped APIs and example excerpts read, not a new full-library review. No official service run or endorsement.'}
(E/'primary-and-review-inputs.json').write_text(json.dumps(result,indent=2)+'\n')
queries=[
 ('spectral-cfc-reuse','eigenvalues₀_antitone|spectral_theorem|def eigenvalues |cfcHom_eq_of_continuous_of_map_id|lemma cfc_eq|cfcAux',
 ['Mathlib/Analysis/Matrix/Spectrum.lean','Mathlib/Analysis/Matrix/HermitianFunctionalCalculus.lean','Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus']),
 ('frobenius-order-harmonic-reuse','frobenius_norm_def|trace_conjTranspose_mul_self_eq_zero_iff|trace_mul_cycle|dotProduct_mulVec_nonneg|harmonic|rankOne|mul_mul_conjTranspose_same|nonneg_iff_eq_star_mul_self',
 ['Mathlib/Analysis/Matrix','Mathlib/LinearAlgebra/Matrix','Mathlib/Analysis/CStarAlgebra']),
 ('scalar-concavity-reuse','ConcaveOn|div.*antitone|div.*le.*div|subhomogeneous',
 ['Mathlib/Analysis/Convex/Function.lean','Mathlib/Analysis/Convex/Deriv.lean'])]
rows=[]
for name,pattern,paths in queries:
 cmd=['rg','-n',pattern,*paths]
 cp=subprocess.run(cmd,cwd=D/'mathlib',stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 assert cp.returncode in (0,1)
 f=E/(name+'.log');f.write_bytes(cp.stdout)
 rows.append({'command':cmd,'cwd':str(D/'mathlib'),'exit_code':cp.returncode,
   'raw_log':f.name,'sha256':sha(cp.stdout)})
(E/'reuse-searches.json').write_text(json.dumps({'searches':rows,
'conclusion':'Located actual Frobenius norm and trace/PSD identities, arbitrary finite-spectrum CFC through continuous star-algebra homomorphism uniqueness, sorted real spectral theorem and concavity definitions. Those APIs are reused. The selected-basis, rank-one harmonic, scalar normalization and averaging bridges connect the frozen problem boundary to those APIs. No located theorem directly discharges the whole RA09 transfer. Names of existing norm/trace bridges support reuse, not mathematical assumptions. No Schiffer implementation was copied.'},indent=2)+'\n')
ids=git(R,'show','5830ed4fb06da0659414a3deb2a40ad327aca052:problem_ids.json')
assert ids==(R/'problem_ids.json').read_bytes()
registry=json.loads(ids)
assert len(registry)==217
assert registry['RA-09']=='randomized-and-low-rank-approximation/RA-09/README.md'
diff=git(R,'diff','--','problem_ids.json','randomized-and-low-rank-approximation/RA-09/README.md','randomized-and-low-rank-approximation/RA-09/problem.tex')
assert diff==b''
(E/'canonical-diff.log').write_bytes(diff)
(E/'permanent-target-check.json').write_text(json.dumps({'result':'PASS','registry_count':217,
'registry_sha256':sha(ids),'canonical_path':registry['RA-09'],
'canonical_and_TeX_tracked_diff_empty':True,'index_generation_performed':False},indent=2)+'\n')
print(json.dumps({'result':'PASS','API_inputs':len(apis),'rubrics':len(rubrics),'example_inputs':len(examples),'permanent_ids':len(registry)}))

f=json.loads((P/'verification/proof-freeze.json').read_text())
assert sha((P/'verification/proof-freeze.json').read_bytes())=='533f5c328cdaf8c1f23f238f8c71b7b4b2fdabb2f532d58a398d4ab2434ccf7e'
for name,h in f['files'].items():assert sha((P/name).read_bytes())==h,name
nested=[]
for name in f['nested_evidence_manifests_bound']:
 mf=P/name;rows=json.loads(mf.read_text())['files']
 for rel,v in rows.items():
  target=mf.parent/rel;h=v if isinstance(v,str) else v['sha256']
  assert sha(target.read_bytes())==h,(name,rel)
  if isinstance(v,dict) and 'bytes' in v:assert target.stat().st_size==v['bytes']
 internal={str(x.relative_to(mf.parent)) for x in mf.parent.rglob('*') if x.is_file() and x!=mf}
 assert internal=={r for r in rows if not r.startswith('../')},name
 nested.append({'manifest':name,'sha256':sha(mf.read_bytes()),'bound_files':len(rows),
  'complete_internal_inventory':True,'only_exact_self_manifest_excluded':True})
headers=lambda text:dict(re.findall(r'^theorem (\w+)(.*?):= by',text,re.M|re.S))
h=headers((P/'Challenge.lean').read_text());actual=headers((P/'Solution.lean').read_text())
assert h==actual
config=json.loads((P/'comparator.json').read_text())
assert ['NLA.RA09.'+n for n in actual]==config['theorem_names'] and len(h)==17
assert config['definition_names']==[] and config['permitted_axioms']==['propext','Classical.choice','Quot.sound']
code=[P/'Solution.lean',*sorted((P/'NLA/RA09').glob('*.lean'))]
for src in code:
 t=src.read_text()
 assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|run_tac)\b',t),src
 assert not re.search(r'^import\s+Challenge\b',t,re.M),src
 assert not re.search(r'^import\s+NLA\.(?!RA09)',t,re.M),src
assert not re.search(r'[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}', '\n'.join(s.read_text() for s in code))
(E/'source-audit.json').write_text(json.dumps({'verdict':'PASS','proof_freeze_sha256':sha((P/'verification/proof-freeze.json').read_bytes()),
 'frozen_project_inputs':len(f['files']),'original_frozen_sources':len(f['source_files']),
 'exact_textual_contracts':list(actual),'definition_exceptions':[],
 'axiom_allowlist':config['permitted_axioms'],'nested_manifests':nested,
 'implementation_sources':{str(s.relative_to(P)):{'sha256':sha(s.read_bytes()),'bytes':s.stat().st_size} for s in code},
 'implementation_scan':'No admissions, custom axioms, unsafe/partial proof declarations, native_decide, Challenge or other NLA imports found in implementation; actual compiled type/body audit is separately required.',
 'contact_scan':'No email in the sixteen mathematical implementation files.',
 'historical_comment_finding':{'file':'NLA/RA09/OrderedExistence.lean','line':8,'text':'Mathematical counterexample: Matthew J. Colbrook.','severity':'nonblocking documentation typo','reason':'This is the affirmative transfer theorem, as canonical source and all contracts make clear. Frozen bytes preserved.'},
 'formalization_metadata_and_actual_Linux':'later separate gates; not certified by this mathematical review'},indent=2)+'\n')
print('PASS: exact source contract and seven nested inventories')
