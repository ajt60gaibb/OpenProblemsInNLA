"""MF-16 statement-stage identities, approved trust boundary and source scope.

Read-only Git/pinned dependency checks; writes only new local review evidence.
No theorem proof, status change, Lake build, dependency copy or download.
"""
from pathlib import Path
import json,hashlib,re,subprocess,datetime
P=Path(__file__).resolve().parents[2];E=Path(__file__).resolve().parent
W=P.parents[2];BASE='5830ed4fb06da0659414a3deb2a40ad327aca052'
C=Path('/tmp/nla-lean-mi22-worktree/matrix-inequalities-and-norms/MI-22/lean/.lake/packages')
def sha(b):return hashlib.sha256(b).hexdigest()
def git(*args):return subprocess.check_output(['git','-C',str(W),*args])
assert git('rev-parse','HEAD').decode().strip()==BASE
assert git('branch','--show-current').decode().strip()=='codex/lean-mf16-word-equation-nonuniqueness'
assert not git('diff','--name-only') and not git('diff','--cached','--name-only')
assert not (P/'Solution.lean').exists() and not (P/'NLA/MF16/Proof.lean').exists()
assert not (P/'.lake').exists()
config=json.loads((P/'comparator.json').read_text())
names=re.findall(r'^theorem ([A-Za-z0-9_]+)',(P/'Challenge.lean').read_text(),re.M)
assert len(names)==9 and (P/'Challenge.lean').read_text().count('\n  sorry\n')==9
assert config=={'challenge_module':'Challenge','solution_module':'Solution','theorem_names':['NLA.MF16.'+n for n in names],'definition_names':[],'permitted_axioms':['propext','Classical.choice','Quot.sound']}
assert 'defaultTargets = ["Challenge"]' in (P/'lakefile.toml').read_text()
assert 'name = "Solution"' in (P/'lakefile.toml').read_text()
defs=(P/'NLA/MF16/Definitions.lean').read_text()
assert not re.search(r'\b(sorry|admit|native_decide|unsafe)\b',re.sub(r'/\-.*?\-/','',defs,flags=re.S))
latest=json.loads((E/'latest.json').read_text());run=Path(latest['attempt'])
checks=json.loads((run/'result.json').read_text())
assert checks['verdict']=='PASS: statement typechecking only' and checks['pins_rechecked_after']
assert len(checks['commands'])==3
for row in checks['commands']:
    assert row['exit_code']==0 and sha((P/row['source']).read_bytes())==row['source_sha256']
    assert sha((run/row['log']).read_bytes())==row['log_sha256']
assert (run/'Challenge.log').read_text().count('declaration uses `sorry`')==9
assert 'warning:' not in (run/'NLA-MF16-Definitions.log').read_text()
assert 'error' not in (run/'reviews-statement-evidence-Inspect.log').read_text().lower()
inspect=(run/'reviews-statement-evidence-Inspect.log').read_text()
assert '\ntrue\ntrue\n' in inspect
axiom_records=re.findall(r"'([^'\n]+)' depends on axioms: \[([^\]]*)\]",inspect)
empty_axiom_records=re.findall(r"'([^'\n]+)' does not depend on any axioms",inspect)
assert len(axiom_records)+len(empty_axiom_records)==10
for _,axs in axiom_records:assert set(a.strip() for a in axs.split(','))<=set(config['permitted_axioms'])
assert any(n=='LeanCert.Engine.krawczykCheck_sound' for n,_ in axiom_records)
reconstruction=json.loads((E/'exact-reconstruction.json').read_text())
assert reconstruction['verdict'].startswith('PASS')
for rel,d in reconstruction['input_sha256'].items():assert sha((P/rel).read_bytes())==d
R='references/colbrook-matrix-functions-2026-09-11/'
source_paths=['matrix-functions-and-stability/MF-16/README.md','matrix-functions-and-stability/MF-16/problem.tex',
 R+'manuscripts/MF-16.tex',R+'manuscripts/MF-16.md',R+'original/manuscripts/MF-16.tex',R+'reviewed-sources/MF-16.tex',
 R+'verification/reviews/MF-16-review.md',R+'code/word_equation_certificate.py',R+'code/word_equation_interval_certificate.py',
 R+'code/word_equation_interval_independent.py',R+'results/word_equation_certificate.json',R+'results/word_equation_interval_certificate.json',
 R+'results/word_equation_interval_independent_certificate.json',R+'README.md']
sources={};blobs={}
for rel in source_paths:
    data=git('show',BASE+':'+rel)
    assert data==(W/rel).read_bytes()
    sources[rel]=sha(data);blobs[rel]=git('rev-parse',BASE+':'+rel).decode().strip()
assert '**Status:** Solved' in (W/source_paths[0]).read_text()
(E/'source-inputs.json').write_text(json.dumps({'base':BASE,'source_count':len(sources),'sources':sources,'git_blobs':blobs,'read_scope':'Complete canonical statement, full authored/original/reviewed source, source informal review, all three verifier implementations and recorded exact/interval outputs. No outside source theorem is assumed; inherited source-author email stays in unchanged originals, no George contact email added.'},indent=2)+'\n')
api_names={
 'leancert':['LeanCert/Engine/RootFinding/Krawczyk.lean','LeanCert/Core/Support.lean','LeanCert/Core/Expr.lean','LeanCert/Core/IntervalRat/Basic.lean','LeanCert/Engine/AD/Computable.lean','LeanCert/Engine/AD/Eval.lean','LeanCert/Engine/Optimization/Gradient.lean','LeanCert/Validity/Krawczyk.lean','LeanCert/Examples/Krawczyk.lean','LeanCert/Tactic/Verification.lean'],
 'mathlib':['Mathlib/LinearAlgebra/Matrix/PosDef.lean','Mathlib/Analysis/Complex/Order.lean','Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean','Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean','Mathlib/Topology/MetricSpace/Contracting.lean']}
manifest=json.loads((P/'lake-manifest.json').read_text());pins={x['name']:x for x in manifest['packages']}
api={}
for pkg,rels in api_names.items():
    for rel in rels:
        path=C/pkg/rel;data=path.read_bytes();rev=pins[pkg]['rev']
        assert data==subprocess.check_output(['git','-C',str(C/pkg),'show',rev+':'+rel])
        api[pkg+'/'+rel]={'sha256':sha(data),'bytes':len(data),'commit':rev,'local_path':str(path.resolve())}
(E/'primary-api-inputs.json').write_text(json.dumps({'sources':api,'reuse_scope':'Actual LeanCert differentiability, Jacobian, complete-box contraction, invertibility/zero and Boolean soundness; real/complex PD and genuine matrix CH. Example architecture read, native_decide examples are not copied. Planned project proof has only explicit kernel trust.'},indent=2)+'\n')
record={'status':'PASS exact statement-only preparation, no approval or proof claim','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'base':BASE,'branch':'codex/lean-mf16-word-equation-nonuniqueness','canonical_status':'Solved, unchanged','mathematical_author':'Matthew J. Colbrook','formalization_author':'George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA; AI-assisted','statement_author':'/root/leancert_examples','independent_reviewers_required':['/root/solved_statement_inventory','/root'],'completed_contracts':0,'intentional_Challenge_placeholders':9,'statement_contracts':config['theorem_names'],'statement_commands':checks['commands'],'statement_run_sha256':sha((run/'result.json').read_bytes()),'newest_semantic_inspection_sha256':sha((run/'reviews-statement-evidence-Inspect.log').read_bytes()),'machine_diagnostics':'Actual krawczykCheck=true and contractionBound<27/1000 observed; ten structural/library kernel-trust checks only. Machine evaluation is not a kernel certificate.','diagnostic_trust_declarations':{n:[a.strip() for a in ax.split(',')] for n,ax in axiom_records}|{n:[] for n in empty_axiom_records},'exact_reconstruction_sha256':sha((E/'exact-reconstruction.json').read_bytes()),'source_files':sources,'source_git_blobs':blobs,'ten_readonly_pins':checks['pins'],'old_target_and_MI22_project_objects_excluded':True,'no_dependency_copy_download_Lake_or_proof':True,'definition_preparation_correction':'Initial Definitions lacked the actual ComplexOrder instance. Added its primary import and open scoped ComplexOrder before freezing. The failed exact source/log is retained in attempt-51snjhmf; no theorem was implemented.','numerical_optimization':'One 3D rational radius1e-7 box; ten-decimal center/preconditioner; actual checker bound<0.027. No inverse AST, precision search, subdivision or degree theorem.','scope_exclusions':'No all-three-roots claim, family threshold, degree theorem, shortest counterexample or priority certification.'}
(E/'input-audit.json').write_text(json.dumps(record,indent=2)+'\n')
print('PASS: nine exact contracts, three fresh commands, actual checker diagnostic, ten standard-three structural/library audits, fourteen original Git sources, fifteen pinned primary API files, ten clean read-only dependency pins; no proof or canonical edit.')
