"""Independent IV06 referee 1: pinned APIs/rubrics and final frozen integrity.

Adapted from this reviewer's earlier MI03 audit; no candidate source is edited.
The exact diagnostic was independently written for IV06, without importing the
informal submission's numerical scripts or the implementer's proof checker.
"""
from pathlib import Path
import datetime, hashlib, json, subprocess

OUT = Path(__file__).resolve().parent
PROJECT = OUT.parents[1]
REPO = PROJECT.parents[2]
DEPS = Path('/tmp/nla-lean-mi22-worktree/matrix-inequalities-and-norms/MI-22/lean/.lake/packages')
STANDARDS = Path('/tmp/nla-lean-formalization/standards')
PIN = 'afb424eda89e8ac96d9eb69f6a88972055a4cd1b'
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
save = lambda n, x: (OUT/n).write_text(json.dumps(x, indent=2)+'\n')

commit_path = STANDARDS/'TauCetiProject_TauCetiReview-commit.json'
tree_path = STANDARDS/'TauCetiProject_TauCetiReview-tree.json'
commit = json.loads(commit_path.read_text())
tree = json.loads(tree_path.read_text())
assert commit['sha'] == PIN and not tree['truncated']
assert sha(commit_path) == 'c2b2fca0f074632b787b91de4ff42454b70d1a82c356bf043c397701850f628d'
assert sha(tree_path) == 'c75cbe23de0e71326757d5a83844226409e38451207d108a317cb2c902bf59a6'
# The retained API response labels its root with the requested commit ID.
assert tree['sha'] == PIN and tree['url'].endswith('/git/trees/'+PIN)
blobs = {x['path']:x['sha'] for x in tree['tree'] if x['type']=='blob'}
rubrics = {}
for name in ['correctness','scope','proof-quality','reuse','generality',
             'api-design','naming','placement','documentation','attribution']:
    rel = 'rubrics/'+name+'.md'
    p = STANDARDS/'sources/TauCetiProject/TauCetiReview'/rel
    raw = p.read_bytes()
    blob = hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
    assert blob == blobs[rel], rel
    rubrics[rel] = {'sha256':sha(p),'git_blob_sha1':blob,
        'url':f'https://github.com/TauCetiProject/TauCetiReview/blob/{PIN}/{rel}'}
assert sha(REPO/'docs/lean/REVIEW.md') == 'd967ddce620d4e754e2f9c25548f30cb537f76f4ddcf8ecf2574945bcd332553'
save('rubric-inputs.json', {'pin':PIN,'commit_record_sha256':sha(commit_path),
    'tree_record_sha256':sha(tree_path),'files':rubrics,
    'local_adaptation':'docs/lean/REVIEW.md',
    'local_adaptation_sha256':sha(REPO/'docs/lean/REVIEW.md'),
    'scope':'Independent application of the repository adaptation; no official Tau Ceti service run is claimed.'})

mathlib_pin = '0df444a360eaa60ab8c11dca51a86af692955474'
leancert_pin = '621a43d7cf21f87872392a01e874f2f1dbddc926'
api_files = {
 'Mathlib/LinearAlgebra/Matrix/ToLinearEquiv.lean':
  'Actual exists_mulVec_eq_zero_iff with finite index, including the empty index; no dimension-positive premise.',
 'Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean':
  'Actual determinant and det_fin_three expansion, used by the matrix polynomial identity.',
 'Mathlib/Topology/Connected/Basic.lean':
  'connectedComponent is a union of actual preconnected sets; membership, preconnectedness and continuous images.',
 'Mathlib/Topology/Connected/Clopen.lean':
  'ConnectedComponents is the actual connected-component quotient; coe_eq_coe\' identifies its classes.',
 'Mathlib/Topology/Order/IntermediateValue.lean':
  'IsPreconnected.Icc_subset supplies every real intermediate point without a finiteness or closedness premise.',
 'Mathlib/Topology/MetricSpace/Pseudo/Defs.lean':
  'Real.pseudoMetricSpace defines dist x y as abs (x-y); ordinary real topology, not a chosen discrete topology.',
 'Mathlib/Topology/MetricSpace/Pseudo/Constructions.lean':
  'Subtype metric construction is inherited from the ambient metric.',
 'Mathlib/SetTheory/Cardinal/Order.lean':
  'Actual embedding-based Cardinal order, mk_le_of_injective and finite-cardinality conversion.'}
apis = {}
for rel,purpose in api_files.items():
    p = DEPS/'mathlib'/rel
    raw = subprocess.check_output(['git','show',mathlib_pin+':'+rel],cwd=DEPS/'mathlib')
    assert raw == p.read_bytes(), rel
    apis[rel] = {'sha256':sha(p),'purpose':purpose,
        'url':f'https://github.com/leanprover-community/mathlib4/blob/{mathlib_pin}/{rel}'}
for rel,purpose in {
 'LeanCert/Validity/DyadicBounds.lean':
  'Checked strict upper-bound Boolean and its soundness theorem. The actual retained certificate uses kernel reduction.',
 'LeanCert/Tactic/IntervalAuto/PointIneq.lean':
  'Singleton construction, actual checker arguments and explicit trust selection for the strict real scalar inequality.',
 'LeanCert/Tactic/Verification.lean':
  'Kernel closure eagerly validates an auxiliary proof; kernel trust audit rejects additional axioms and native trust.'}.items():
    p = DEPS/'leancert'/rel
    raw = subprocess.check_output(['git','show',leancert_pin+':'+rel],cwd=DEPS/'leancert')
    assert raw == p.read_bytes(), rel
    apis[rel] = {'sha256':sha(p),'purpose':purpose,
        'url':f'https://github.com/alerad/leancert/blob/{leancert_pin}/{rel}'}
lean_rel = 'src/Lean/Elab/Tactic/Decide.lean'
lean_source = Path('/Users/georgestepaniants/.elan/toolchains/leanprover--lean4---v4.33.1/src/lean/Lean/Elab/Tactic/Decide.lean')
apis[lean_rel] = {'sha256':sha(lean_source),
    'purpose':'The +kernel branch invokes mkAuxLemma with asynchronous elaboration disabled; it is separate from +native.',
    'url':'https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/'+lean_rel}
save('api-source-inputs.json', {'actual_consumption':'actual-dependencies.json',
    'source_pins_checked_clean':'dependency-pins.json','files':apis})

certificate = json.loads((OUT/'certificate-check.json').read_text())
assert certificate['exit_code'] == 0
assert certificate['source_sha256'] == sha(OUT/'Certificate.lean')
assert certificate['log_sha256'] == sha(OUT/'Certificate.log')
actual = (OUT/'Certificate.log').read_text()
assert 'of_decide_eq_true' in actual and '@Eq.refl.{1} Bool Bool.true' in actual
assert 'verify_strict_upper_bound_dyadic_checked' in (OUT/'reviews-proof-referee-1-evidence-Inspect.log').read_text()
assert 'numerical_separator_margin._proof_1_7' in actual
assert 'depends on axioms: [propext, Classical.choice, Quot.sound]' in actual
save('certificate-audit.json', {'status':'PASS',
 'actual_private_declaration':'NLA.IV06.numerical_separator_margin._proof_1_7',
 'actual_boolean':'checkStrictUpperBoundDyadicChecked (Expr.const 18).neg 0 0 (le_refl 0) 0 (-53) 10 = true',
 'actual_rationals':'Rat.divInt with denominator 1; exact arguments retained in Certificate.lean and Certificate.log.',
 'retained_term':'of_decide_eq_true applied to id (Eq.refl true), checked by the kernel.',
 'strict_result':'(-18 : Real) < 0', 'domain':'[0,0]',
 'actual_consumer_chain':['numerical_separator_margin','witness_separators_proved',
     'four_components_proved','counterexample_proved','not_componentBoundConjecture'],
 'fresh_checker_repeat':'decide +kernel, same exact Rat.divInt arguments, exit 0.',
 'candidate_axiom_audit_count':17,'additional_actual_private_audit':1,
 'standard_three_only':True,'native_execution_trust':False,
 'auxiliary_diagnostics':'Archived first helper attempts used rfl or plain decide and failed reduction; explicit kernel reduction passed. An initial unanchored source-signature parser and a manuscript final-row parser were corrected. These were reviewer diagnostics, not candidate proof failures or changes.',
 'source_sha256':sha(OUT/'Certificate.lean'),'log_sha256':sha(OUT/'Certificate.log')})

reconstruction = json.loads((OUT/'reconstruction.json').read_text())
assert reconstruction['status'] == 'PASS'
assert reconstruction['definitions_sha256'] == sha(PROJECT/'NLA/IV06/Definitions.lean')
assert len(reconstruction['witnesses']) == 4
assert len(reconstruction['separator_bounds']) == 3
assert len(reconstruction['all_six_pairwise_separations']) == 6
save('diagnostic-audit.json', {'status':'PASS',
    'script_sha256':sha(OUT/'reconstruct.py'),'result_sha256':sha(OUT/'reconstruction.json'),
    'independent':True,'imports_submission_checker':False,
    'scope':'Exact transcription and universal affine distance identities supplement the independently compiled full Lean proof. No finite test is substituted for topology or cardinality.'})

freeze = json.loads((PROJECT/'verification/proof-freeze.json').read_text())
assert sha(PROJECT/'verification/proof-freeze.json') == '5bc8cfd590e82a27807ad5f6832c0cc5d634832979241f80eb30d8d76eaaa673'
for rel,entry in freeze['files'].items():
    assert sha(PROJECT/rel) == entry['sha256'] and (PROJECT/rel).stat().st_size == entry['bytes'], rel
for rel,digest in freeze['source_files'].items():
    raw = subprocess.check_output(['git','show',freeze['source_commit']+':'+rel],cwd=REPO)
    assert hashlib.sha256(raw).hexdigest() == digest and raw == (REPO/rel).read_bytes(), rel
statement = json.loads((PROJECT/'reviews/statement-freeze.json').read_text())
for rel,digest in statement['files'].items():
    if isinstance(digest,dict): digest = digest['sha256']
    assert sha(PROJECT/rel) == digest, rel
for rel,digest in freeze['statement_approvals'].items():
    assert sha(PROJECT/rel) == digest, rel
save('integrity-final.json', {'status':'PASS','checked_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'proof_freeze_sha256':sha(PROJECT/'verification/proof-freeze.json'),
    'proof_completion_sha256':sha(PROJECT/'reviews/proof-completion.md'),
    'project_count':len(freeze['files']),'source_count':len(freeze['source_files']),
    'statement_count':len(statement['files']),'statement_approvals':freeze['statement_approvals'],
    'source_commit':freeze['source_commit'],'all_inputs_unchanged':True})
print('PASS: 10 pinned rubrics, 12 primary API files, actual kernel checker and independent diagnostics; all 126+8 proof inputs and 32 statements unchanged.')
