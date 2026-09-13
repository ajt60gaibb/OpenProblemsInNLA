"""RA-09 statement gate: exact original bytes, actual instances and clean pins.

Adapted from the campaign MF-16 input audit. This performs no implementation,
dependency copy/download, Lake build, publication or canonical mutation.
"""
from pathlib import Path
import datetime, hashlib, json, re, subprocess
P = Path(__file__).resolve().parents[2]
E = Path(__file__).resolve().parent
W = P.parents[2]
BASE = '5830ed4fb06da0659414a3deb2a40ad327aca052'
C = Path('/tmp/nla-lean-mi22-worktree/matrix-inequalities-and-norms/MI-22/lean/.lake/packages')
def sha(data): return hashlib.sha256(data).hexdigest()
def git(*args): return subprocess.check_output(['git','-C',str(W),*args])
assert git('rev-parse','HEAD').decode().strip() == BASE
assert git('branch','--show-current').decode().strip() == 'codex/lean-ra09-concave-frobenius-transfer'
assert not git('diff','--name-only') and not git('diff','--cached','--name-only')
assert not (P/'Solution.lean').exists() and not (P/'NLA/RA09/Proof.lean').exists()
assert not (P/'.lake').exists()
challenge = (P/'Challenge.lean').read_text()
names = re.findall(r'^theorem ([A-Za-z0-9_]+)',challenge,re.M)
assert len(names) == 17 and challenge.count('\n  sorry\n') == 17
config = json.loads((P/'comparator.json').read_text())
assert config == {'challenge_module':'Challenge','solution_module':'Solution',
    'theorem_names':['NLA.RA09.'+n for n in names],'definition_names':[],
    'permitted_axioms':['propext','Classical.choice','Quot.sound']}
assert 'defaultTargets = ["Challenge"]' in (P/'lakefile.toml').read_text()
assert 'name = "Solution"' in (P/'lakefile.toml').read_text()
defs = (P/'NLA/RA09/Definitions.lean').read_text()
assert not re.search(r'\b(sorry|admit|native_decide|unsafe|axiom)\b',re.sub(r'/\-.*?\-/','',defs,flags=re.S))
latest = json.loads((E/'latest.json').read_text()); run = Path(latest['attempt'])
checks = json.loads((run/'result.json').read_text())
assert checks['verdict'] == 'PASS: statement typechecking only' and checks['pins_rechecked_after']
assert len(checks['commands']) == 3
for row in checks['commands']:
    assert row['exit_code'] == 0 and sha((P/row['source']).read_bytes()) == row['source_sha256']
    assert sha((run/row['log']).read_bytes()) == row['log_sha256']
assert (run/'Challenge.log').read_text().count('declaration uses `sorry`') == 17
assert 'warning:' not in (run/'NLA-RA09-Definitions.log').read_text()
inspect = (run/'reviews-statement-evidence-Inspect.log').read_text()
assert 'error:' not in inspect and 'warning:' not in inspect
assert '@Matrix.frobeniusNormedAddCommGroup' in inspect
assert '@cfc Real (NLA.RA09.RealMatrix n)' in inspect
assert 'A ≤ B ↔ (B - A).PosSemidef' in inspect
assert 'Antitone self.eigenvalues' in inspect and 'ContinuousOn f (Set.Ici 0)' in inspect
axs = re.findall(r"'([^'\n]+)' depends on axioms: \[([^\]]*)\]",inspect)
empty = re.findall(r"'([^'\n]+)' does not depend on any axioms",inspect)
assert len(axs)+len(empty) == 17
for _, values in axs:
    assert set(a.strip() for a in values.split(',')) <= set(config['permitted_axioms'])
reconstruction = json.loads((E/'exact-reconstruction.json').read_text())
assert reconstruction['verdict'] == 'PASS exact diagnostics only; no universal Lean proof'
for rel, digest in reconstruction['input_sha256'].items(): assert sha((P/rel).read_bytes()) == digest
R = 'references/colbrook-transfer-2026-09-11/'
source_paths = ['randomized-and-low-rank-approximation/RA-09/README.md',
 'randomized-and-low-rank-approximation/RA-09/problem.tex',
 R+'manuscripts/02_frobenius_function_transfer.tex',R+'manuscripts/02_frobenius_function_transfer.md',
 R+'original/manuscripts/02_frobenius_function_transfer.tex',
 R+'reviewed-sources/02_frobenius_function_transfer.tex',R+'reviewed-sources/common_preamble.tex',
 R+'verification/reviews/RA-09-review.md',R+'verification/verify_frobenius_transfer.py',
 R+'verification/verify_relaxed_transfer.py',R+'results/frobenius_transfer_verification.json',
 R+'results/relaxed_transfer_verification.json',R+'README.md',
 'AGENTS.md','CONTRIBUTING.md','tools/lean/HARNESS.md','tools/lean/source-lock.json']
sources, blobs = {}, {}
for rel in source_paths:
    data = git('show',BASE+':'+rel)
    assert data == (W/rel).read_bytes()
    sources[rel] = sha(data); blobs[rel] = git('rev-parse',BASE+':'+rel).decode().strip()
assert '**Status:** Solved' in (W/source_paths[0]).read_text()
(E/'source-inputs.json').write_text(json.dumps({'base':BASE,'source_count':len(sources),
 'sources':sources,'git_blobs':blobs,
 'read_scope':'Complete canonical statement, full authored/original/reviewed manuscript, original informal review and diagnostic programs, source attribution and repository policies. No mathematical claim from an outside source is assumed as an axiom. Source status and current worktree equality are local fixed-snapshot checks, not a current exhaustive network audit.'},indent=2)+'\n')
api_names = {'leancert':['LeanCert/Tactic/Verification.lean'],
 'mathlib':['Mathlib/Analysis/Matrix/Normed.lean','Mathlib/LinearAlgebra/Matrix/Trace.lean',
  'Mathlib/LinearAlgebra/Matrix/PosDef.lean','Mathlib/Analysis/Matrix/Order.lean',
  'Mathlib/Analysis/Matrix/HermitianFunctionalCalculus.lean','Mathlib/Analysis/Matrix/Spectrum.lean',
  'Mathlib/Analysis/InnerProductSpace/PiL2.lean','Mathlib/Analysis/Convex/Function.lean']}
manifest = json.loads((P/'lake-manifest.json').read_text()); pins = {x['name']:x for x in manifest['packages']}
api = {}
for pkg, rels in api_names.items():
    for rel in rels:
        path = C/pkg/rel; data = path.read_bytes(); rev = pins[pkg]['rev']
        assert data == subprocess.check_output(['git','-C',str(C/pkg),'show',rev+':'+rel])
        api[pkg+'/'+rel] = {'sha256':sha(data),'bytes':len(data),'commit':rev,'local_path':str(path.resolve())}
(E/'primary-api-inputs.json').write_text(json.dumps({'sources':api,
 'scope':'Actual Frobenius norm, finite CFC/ordered spectral semantics, PSD/order/trace/orthogonality and concavity definitions/API; LeanCert kernel trust. Missing universal scalar/harmonic/overlap/transfer glue is an explicit proof obligation, not a supplied premise.'},indent=2)+'\n')
reused = {}
for name, original in [('RA-09-feasibility.md','/tmp/nla-lean-formalization/RA-09-next-statements.md'),
 ('RA08-Definitions.lean.txt','/tmp/nla-lean-ra08-worktree/randomized-and-low-rank-approximation/RA-08/lean/NLA/RA08/Definitions.lean'),
 ('source-worktree.json','/tmp/nla-lean-formalization/RA-09-source-worktree.json')]:
    copied = E/'inputs'/name
    assert copied.read_bytes() == Path(original).read_bytes()
    reused[name] = {'source':original,'snapshot_sha256':sha(copied.read_bytes())}
record = {'status':'PASS exact statement-only preparation; no proof or approval claimed',
 'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'base':BASE,
 'branch':'codex/lean-ra09-concave-frobenius-transfer','canonical_status':'Solved, unchanged',
 'mathematical_author':'Matthew J. Colbrook',
 'formalization_author':'George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA; AI-assisted',
 'statement_author':'/root/leancert_examples',
 'required_independent_statement_reviewers':['/root','/root/formal_review_standards'],
 'completed_contracts':0,'intentional_Challenge_placeholders':17,
 'statement_contracts':config['theorem_names'],'statement_commands':checks['commands'],
 'statement_run_sha256':sha((run/'result.json').read_bytes()),
 'actual_semantic_inspection_sha256':sha((run/'reviews-statement-evidence-Inspect.log').read_bytes()),
 'structural_trust':{n:[a.strip() for a in v.split(',')] for n,v in axs}|{n:[] for n in empty},
 'exact_reconstruction_sha256':sha((E/'exact-reconstruction.json').read_bytes()),
 'source_files':sources,'source_git_blobs':blobs,'reused_drafts_and_ownership':reused,
 'ten_readonly_pins':checks['pins'],'old_RA09_and_MI22_project_objects_excluded':True,
 'no_dependency_copy_download_Lake_or_proof':True,
 'numerical_scope':'Pure exact unbounded algebra; no interval subdivision, numerical singleton or proof certificate is needed. The 500 rational diagnostics and two small matrices are supplementary tests only. Explicit LeanCert kernel trust and actual dependency audits are required for the eventual full proof.',
 'scope_exclusions':'No unordered factor-two result, optimality, larger function class, complex extension or exhaustive public-source audit. No target weakening, f0=0 assumption, substitute residual premise or preferred basis.'}
(E/'input-audit.json').write_text(json.dumps(record,indent=2)+'\n')
print('PASS: 17 exact contracts; 3 fresh commands; 17 standard-three structural kernel audits; '+
      str(len(sources))+' original Git sources/policies; 9 pinned primary API files; 10 clean read-only dependency pins.')
