"""Read-only source/API/policy binding for independent RA09 statement review."""
from pathlib import Path
import datetime,hashlib,json,re,subprocess
E=Path(__file__).resolve().parent;P=E.parents[1];W=P.parents[2]
D=Path('/tmp/nla-lean-mi22-worktree/matrix-inequalities-and-norms/MI-22/lean/.lake/packages')
S=Path('/tmp/nla-lean-formalization/standards')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
sources={
 'mathlib':['Mathlib/Analysis/Matrix/Normed.lean','Mathlib/Analysis/Matrix/Order.lean',
 'Mathlib/LinearAlgebra/Matrix/PosDef.lean','Mathlib/LinearAlgebra/Matrix/Trace.lean',
 'Mathlib/Analysis/Matrix/Spectrum.lean','Mathlib/Analysis/Matrix/HermitianFunctionalCalculus.lean',
 'Mathlib/Analysis/Convex/Function.lean','Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Unital.lean',
 'Mathlib/LinearAlgebra/UnitaryGroup.lean'],
 'leancert':['LeanCert/Tactic/Verification.lean']}
api=[]
for pkg,names in sources.items():
    rev=subprocess.check_output(['git','rev-parse','HEAD'],cwd=D/pkg).decode().strip()
    for name in names:
        data=(D/pkg/name).read_bytes();raw=subprocess.check_output(['git','show',rev+':'+name],cwd=D/pkg)
        assert data==raw,name
        api.append({'package':pkg,'revision':rev,'path':name,'sha256':sha(D/pkg/name),
          'git_blob':subprocess.check_output(['git','rev-parse',rev+':'+name],cwd=D/pkg).decode().strip(),
          'scope':'Primary definition/API file; relevant sections inspected, not a claim to review every library proof.'})
tree=json.loads((S/'TauCetiProject_TauCetiReview-tree.json').read_text())
assert tree['sha']=='afb424eda89e8ac96d9eb69f6a88972055a4cd1b'
rubrics={}
for name in ['correctness','scope','proof-quality','reuse','generality','api-design','naming','placement','documentation','attribution']:
    path='rubrics/'+name+'.md';data=(S/'sources/TauCetiProject/TauCetiReview'/path).read_bytes()
    blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
    assert blob==next(x['sha'] for x in tree['tree'] if x['path']==path)
    rubrics[name]={'path':path,'git_blob':blob,'sha256':hashlib.sha256(data).hexdigest()}
defs=(P/'NLA/RA09/Definitions.lean').read_text()
code=re.sub(r'/\-[\s\S]*?\-/','',defs);code=re.sub(r'--[^\n]*','',code)
for tok in ['axiom','sorry','admit','opaque','unsafe','native_decide','run_tac','elab','macro']:
    assert not re.search(r'\b'+tok+r'\b',code),tok
assert re.findall(r'^import (.+)$',code,re.M)==[
 'Mathlib.Analysis.Matrix.Order','Mathlib.Analysis.Matrix.HermitianFunctionalCalculus',
 'Mathlib.Analysis.Matrix.Normed','Mathlib.Analysis.InnerProductSpace.PiL2',
 'Mathlib.Analysis.Convex.Function','Mathlib.LinearAlgebra.UnitaryGroup',
 'Mathlib.LinearAlgebra.Matrix.Notation']
assert 'import Challenge' not in defs and 'import NLA.RA08' not in defs
challenge=(P/'Challenge.lean').read_text()
assert re.findall(r'^import (.+)$',challenge,re.M)==['NLA.RA09.Definitions']
assert len(re.findall(r'^\s+sorry\s*$',challenge,re.M))==17
registry=W/'problem_ids.json';base=json.loads((P/'reviews/statement-freeze.json').read_text())['base']
assert registry.read_bytes()==subprocess.check_output(['git','show',base+':problem_ids.json'],cwd=W)
cmd=['python3','tools/validate_problem_ids.py','--base-ref',base]
r=subprocess.run(cmd,cwd=W,capture_output=True);(E/'permanent-ids.log').write_bytes(r.stdout+r.stderr)
assert r.returncode==0
record={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'primary_APIs':api,
 'Tau_Ceti_revision':tree['sha'],'ten_rubric_sources':rubrics,
 'local_review_protocol_sha256':sha(W/'docs/lean/REVIEW.md'),
 'structural_safety':{'Definitions_no_holes_or_custom_axioms_or_execution_extensions':True,
   'Challenge_only_Definitions_import':True,'Challenge_placeholders':17,
   'no_RA08_implementation_import':True,'no_Solution_or_Proof_present':not(P/'Solution.lean').exists() and not list((P/'NLA').rglob('Proof.lean'))},
 'registry':{'count':len(json.loads(registry.read_text())),'sha256':sha(registry),
   'unchanged_from_base':base,'command':cmd,'exit_code':r.returncode,
   'validator_sha256':sha(W/'tools/validate_problem_ids.py'),'log_sha256':sha(E/'permanent-ids.log')},
 'review_scope':'Statement phase; no implementation or authoritative Linux verification claimed.',
 'verdict':'PASS'}
(E/'source-api-audit.json').write_text(json.dumps(record,indent=2)+'\n')
print('SOURCE/API/REGISTRY PASS',record['registry']['count'])
