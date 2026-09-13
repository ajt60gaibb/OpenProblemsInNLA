"""Independent IS03 statement referee: primary APIs, rubric identity, final freeze.

The rubric identity procedure is reused from this reviewer's IV06/MI03 audits.
Only this review's evidence files are written; all statement inputs are frozen.
"""
from pathlib import Path
import datetime,hashlib,json,subprocess
OUT=Path(__file__).resolve().parent
P=OUT.parents[1]
REPO=P.parents[2]
DEPS=Path('/tmp/nla-lean-mi22-worktree/matrix-inequalities-and-norms/MI-22/lean/.lake/packages')
STANDARDS=Path('/tmp/nla-lean-formalization/standards')
PIN='afb424eda89e8ac96d9eb69f6a88972055a4cd1b'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
save=lambda n,v:(OUT/n).write_text(json.dumps(v,indent=2)+'\n')
commit_path=STANDARDS/'TauCetiProject_TauCetiReview-commit.json'
tree_path=STANDARDS/'TauCetiProject_TauCetiReview-tree.json'
commit=json.loads(commit_path.read_text());tree=json.loads(tree_path.read_text())
assert commit['sha']==PIN and tree['sha']==PIN and not tree['truncated']
assert tree['url'].endswith('/git/trees/'+PIN)
assert sha(commit_path)=='c2b2fca0f074632b787b91de4ff42454b70d1a82c356bf043c397701850f628d'
assert sha(tree_path)=='c75cbe23de0e71326757d5a83844226409e38451207d108a317cb2c902bf59a6'
blobs={x['path']:x['sha'] for x in tree['tree'] if x['type']=='blob'}
rubrics={}
for n in ['correctness','scope','proof-quality','reuse','generality','api-design',
          'naming','placement','documentation','attribution']:
    rel='rubrics/'+n+'.md'
    path=STANDARDS/'sources/TauCetiProject/TauCetiReview'/rel
    raw=path.read_bytes()
    blob=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
    assert blob==blobs[rel]
    rubrics[rel]={'sha256':sha(path),'git_blob':blob,
       'url':f'https://github.com/TauCetiProject/TauCetiReview/blob/{PIN}/{rel}'}
save('rubric-inputs.json',{'pin':PIN,'files':rubrics,
    'commit_record_sha256':sha(commit_path),'tree_record_sha256':sha(tree_path),
    'local_adaptation':'docs/lean/REVIEW.md',
    'local_adaptation_sha256':sha(REPO/'docs/lean/REVIEW.md'),
    'scope':'Independent statement-stage application of the repository adaptation. No official Tau Ceti service or complete proof review.'})

mpin='0df444a360eaa60ab8c11dca51a86af692955474'
lpin='621a43d7cf21f87872392a01e874f2f1dbddc926'
apis={}
for rel,purpose in {
 'Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean':
  'charpoly is det(charmatrix), charmatrix is XI-C(A); actual empty determinant and block polynomial APIs.',
 'Mathlib/LinearAlgebra/Matrix/Charpoly/Eigs.lean':
  'Trace equals the sum of the characteristic-root multiset when split. This alone does not prove the required all-power bridge.',
 'Mathlib/LinearAlgebra/Matrix/Trace.lean':
  'Actual finite diagonal sum, trace_one and empty-index trace.',
 'Mathlib/Data/Matrix/Mul.lean':
  'Actual dot-product matrix multiplication used by Matrix.semiring natural powers.',
 'Mathlib/Algebra/Polynomial/Derivative.lean':
  'Actual formal derivative and coefficient derivative formula.'}.items():
    path=DEPS/'mathlib'/rel
    assert path.read_bytes()==subprocess.check_output(['git','show',mpin+':'+rel],cwd=DEPS/'mathlib')
    apis[rel]={'sha256':sha(path),'purpose':purpose,
        'url':f'https://github.com/leanprover-community/mathlib4/blob/{mpin}/{rel}'}
rel='LeanCert/Tactic/Verification.lean'
path=DEPS/'leancert'/rel
assert path.read_bytes()==subprocess.check_output(['git','show',lpin+':'+rel],cwd=DEPS/'leancert')
apis[rel]={'sha256':sha(path),
    'purpose':'Definition-only kernel trust audit now; later explicit kernel numerical closure must retain a material certificate without native trust.',
    'url':f'https://github.com/alerad/leancert/blob/{lpin}/{rel}'}
save('api-source-inputs.json',{'files':apis,'actual_elaboration':'reviews-statement-referee-1-evidence-Inspect.log',
    'clean_pinned_repositories':'dependency-pins.json','scope':'Definition fidelity and inspected available APIs, not a claim that missing trace-power bridges are already implemented.'})

# The online primary paper was read independently on this review date. We record
# the observed location/scope, without asserting an unretained PDF byte identity.
save('primary-paper-check.json',{
 'url':'https://arxiv.org/pdf/1712.05454',
 'title':'On the realizability of the critical points of a realizable list',
 'authors':['Sarah L. Hoover','Daniel A. McCormick','Pietro Paparella','Amber R. Thrall'],
 'read_date':'2026-09-12','location':'Printed page 2: realizability definition, Conjecture 1.2 and low-order paragraph.',
 'finding':'Realizability uses the same dimension as the eigenvalue list, with multiplicities. Johnson asks whether the derivative critical-point list is realizable. No irreducibility, diagonalizability, symmetry or trace-zero restriction is imposed. The low-order and trace-zero statements describe previously established special cases.',
 'retrieval':'Independent web PDF read. No full PDF artifact or byte hash is asserted here.',
 'scope':'Primary conjecture/hypothesis correspondence only; no new exhaustive status or priority search.'})

diag=json.loads((OUT/'reconstruction.json').read_text())
assert diag['status']=='PASS'
assert diag['definitions_sha256']==sha(P/'NLA/IS03/Definitions.lean')
assert len(diag['moments'])==7 and diag['moments'][-1]=='-8593/823543'
assert diag['companion_power_traces']==diag['moments']
assert diag['q']==diag['companion_charpoly']
save('diagnostic-audit.json',{'status':'PASS','script_sha256':sha(OUT/'reconstruct.py'),
    'result_sha256':sha(OUT/'reconstruction.json'),
    'independent_of_author_checker':True,'standard_library_only':True,
    'scope':'Exact source transcription and finite polynomial/matrix diagnostics. The all-real-B theorem and generic nonnegative powers remain unproved Lean obligations.'})

assert sha(P/'reviews/statement-freeze.json')=='588196a54decb127a814dc4860621505d6874a077295f3e30a782d7f28b8ac6c'
assert sha(P/'reviews/statement-handoff.md')=='3c1d998ba3d3a658a7d9ea706e4357ab3587757050cef70e6f366481affd7c68'
f=json.loads((P/'reviews/statement-freeze.json').read_text())
for rel,digest in f['files'].items():assert sha(P/rel)==digest,rel
for rel,digest in f['source_files'].items():
    raw=subprocess.check_output(['git','show',f['base']+':'+rel],cwd=REPO)
    assert hashlib.sha256(raw).hexdigest()==digest and (REPO/rel).read_bytes()==raw,rel
assert len(f['files'])==34 and len(f['source_files'])==10
assert not (P/'NLA/IS03/Proof.lean').exists() and not (P/'Solution.lean').exists()
save('integrity-final.json',{'status':'PASS','checked_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'statement_freeze_sha256':sha(P/'reviews/statement-freeze.json'),
    'statement_handoff_sha256':sha(P/'reviews/statement-handoff.md'),
    'project_count':34,'original_sources':10,'all_frozen_bytes_unchanged':True,'proof_absent':True})
print('PASS: 34 frozen project inputs, 10 exact original Git sources, 10 pinned rubrics, 6 primary API files, exact diagnostic and proof absence.')
