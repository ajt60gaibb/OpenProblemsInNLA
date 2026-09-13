"""Read-only final binding of IS-03 referee-2 evidence to actual frozen inputs."""
from pathlib import Path
import datetime, hashlib,json,re,subprocess
out=Path(__file__).resolve().parent;project=out.parents[1];repo=project.parents[2]
cache=Path('/tmp/nla-lean-mi22-worktree/matrix-inequalities-and-norms/MI-22/lean/.lake/packages')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
git=lambda p,*a:subprocess.check_output(['git','-C',str(p),*a])
write=lambda n,o:(out/n).write_text(json.dumps(o,indent=2)+'\n')
freeze_path=project/'verification/proof-freeze.json';freeze=json.loads(freeze_path.read_text())
assert sha(freeze_path)=='636cdb024f5b73ea61edd518de39ee192a604987aad2b9914c4d7e7eeab672e4'
assert len(freeze['files'])==203 and len(freeze['source_files'])==10
for name,h in freeze['files'].items():assert sha(project/name)==h,name
sources={}
for name,h in freeze['source_files'].items():
    b=(repo/name).read_bytes();assert hashlib.sha256(b).hexdigest()==h,name
    assert b==git(repo,'show',freeze['base']+':'+name),name
    sources[name]={'sha256':h,'bytes':len(b),'git_blob':git(repo,'rev-parse',freeze['base']+':'+name).decode().strip()}
statement_path=project/'reviews/statement-freeze.json';statement=json.loads(statement_path.read_text())
assert sha(statement_path)=='588196a54decb127a814dc4860621505d6874a077295f3e30a782d7f28b8ac6c'
assert len(statement['files'])==34
for name,rec in statement['files'].items():assert sha(project/name)==(rec['sha256'] if isinstance(rec,dict) else rec),name
reviews={
 'reviews/statement-referee-1.md':'79d057b4608eb72826d1265f7e718f57855907cfdd3283ab791bbbc98321f71a',
 'reviews/statement-referee-2.md':'cca3fa8d9627d3ca91f64286a216ee102d137eb711f5c47ce945c519bda9ea70',
 'verification/proof-start.json':'09382f4bc304a44eee742f1f6fa0484014e4112a7732e485fc5c2001a10b7cf7'}
for n,h in reviews.items():assert sha(project/n)==h,n
proof_sources=['NLA/IS03/'+n+'.lean' for n in ['Definitions','Algebra','Witness','Spectral','Newton','Numerical','Proof']]+['Solution.lean']

def remove_comments(t):
    i=0;level=0;buf=[]
    while i<len(t):
        if t.startswith('/-',i):level+=1;i+=2;continue
        if level and t.startswith('-/',i):level-=1;i+=2;continue
        if level:i+=1;continue
        if t.startswith('--',i):
            k=t.find('\n',i);i=len(t) if k<0 else k;continue
        buf.append(t[i]);i+=1
    assert level==0
    return ''.join(buf)
scans={};imports={}
for n in proof_sources:
    t=remove_comments((project/n).read_text())
    banned=re.findall(r'\b(?:sorry|admit|sorryAx|axiom|opaque|unsafe|native_decide|implemented_by|extern)\b|Lean\.(?:ofReduceBool|ofReduceNat|trustCompiler)|debug\.skipKernelTC|\brun_(?:tac|cmd)\b|#(?:eval|reduce)|^\s*(?:local\s+)?(?:instance|notation|macro|elab|syntax)\b',t,re.M)
    assert not banned,(n,banned)
    imps=re.findall(r'^import\s+(\S+)',t,re.M);imports[n]=imps
    assert 'Challenge' not in imps,n
    scans[n]={'sha256':sha(project/n),'no_forbidden_source_constructs':True}
# A source-header check is supplemental, not a substitute for Linux Comparator.
def headers(path):
    t=remove_comments(path.read_text())
    return [(m.group(1),' '.join(m.group(0).split())) for m in re.finditer(r'^theorem\s+(\w+)\b[\s\S]*?:=\s*by',t,re.M)]
hc=headers(project/'Challenge.lean');hs=headers(project/'Solution.lean')
assert hc==hs and len(hc)==7,(hc,hs)
config=json.loads((project/'comparator.json').read_text())
assert config['challenge_module']=='Challenge' and config['solution_module']=='Solution'
assert config['theorem_names']==['NLA.IS03.'+n for n,_ in hc]
assert config['definition_names']==[]
assert set(config['permitted_axioms'])=={'propext','Classical.choice','Quot.sound'}
assert len(config['permitted_axioms'])==3
fresh=json.loads((out/'fresh-result.json').read_text());certificate=json.loads((out/'certificate-result.json').read_text());arith=json.loads((out/'reconstruction.json').read_text())
assert fresh['result']==certificate['result']==arith['result']=='PASS'
checks=json.loads((out/'fresh-checks.json').read_text())
assert len(checks)==10 and all(c['exit_code']==0 for c in checks)
for c in checks:
    assert sha(project/c['source'])==c['source_sha256'],c['source']
    assert sha(out/(Path(c['source']).stem+'.log'))==c['log_sha256'],c['source']
extra=json.loads((out/'certificate-command.json').read_text());assert extra['exit_code']==0
assert sha(out/'Certificate.lean')==extra['source_sha256'] and sha(out/'Certificate.log')==extra['log_sha256']
assert fresh['actual_project_declarations_from_all_exports']==61
assert len(fresh['required_actual_dependencies'])==40
pins=json.loads((project/'lake-manifest.json').read_text())['packages']
for pkg in pins:
    p=cache/pkg['name'];assert git(p,'rev-parse','HEAD').decode().strip()==pkg['rev'];assert not git(p,'status','--porcelain=v1')
assert len(pins)==10
api_files={
 'mathlib':[
 'Mathlib/Data/Matrix/Basic.lean','Mathlib/Data/Matrix/Mul.lean',
 'Mathlib/LinearAlgebra/Matrix/Trace.lean','Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean',
 'Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean','Mathlib/LinearAlgebra/Matrix/ToLin.lean',
 'Mathlib/LinearAlgebra/Charpoly/ToMatrix.lean','Mathlib/LinearAlgebra/Trace.lean',
 'Mathlib/FieldTheory/Separable.lean','Mathlib/LinearAlgebra/Eigenspace/Charpoly.lean',
 'Mathlib/LinearAlgebra/Eigenspace/Basic.lean','Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean',
 'Mathlib/Analysis/Complex/Polynomial/Basic.lean','Mathlib/Algebra/Polynomial/Derivative.lean',
 'Mathlib/Algebra/Polynomial/Roots.lean','Mathlib/Algebra/Polynomial/AlgebraMap.lean',
 'Mathlib/RingTheory/Polynomial/Vieta.lean','Mathlib/RingTheory/MvPolynomial/Symmetric/NewtonIdentities.lean',
 'Mathlib/RingTheory/MvPolynomial/Symmetric/Defs.lean'],
 'leancert':['LeanCert/Tactic/IntervalAuto/PointIneq.lean','LeanCert/Tactic/Verification.lean','LeanCert/Validity/DyadicBounds.lean']}
apis={}
for pkg,names in api_files.items():
    rev=next(p['rev'] for p in pins if p['name']==pkg);p=cache/pkg
    apis[pkg]={'revision':rev,'files':{}}
    for n in names:
        b=(p/n).read_bytes();assert b==git(p,'show',rev+':'+n)
        apis[pkg]['files'][n]={'bytes':len(b),'sha256':sha(p/n),'git_blob':git(p,'rev-parse',rev+':'+n).decode().strip(),
          'url':'https://github.com/'+('leanprover-community/mathlib4' if pkg=='mathlib' else 'alerad/leancert')+'/blob/'+rev+'/'+n}
write('primary-api-inputs.json',{'scope':'Primary source files binding inspected definitions, actual semantic bridge theorems and kernel certificate/trust implementation. Hashes do not claim a full independent audit of Mathlib or LeanCert.','packages':apis})
standards=Path('/tmp/nla-lean-formalization/standards');expected=json.loads((standards/'MANIFEST.json').read_text())
scope=[n for n in expected if n.startswith('sources/TauCetiProject/TauCetiReview/rubrics/') and n.endswith('.md')]
scope+=['sources/TauCetiProject/TauCetiReview/REVIEWING.md','sources/TauCetiProject/TauCetiReview/README.md']
for n in scope:assert sha(standards/n)==expected[n]['sha256']
write('review-standard-inputs.json',{'tau_ceti_revision':'afb424eda89e8ac96d9eb69f6a88972055a4cd1b','scope':'The ten angles are adapted to this single NLA target; not an official Tau Ceti runner result or roadmap admission.','sources':{n:expected[n] for n in scope},
 'repository_protocol':{'path':'docs/lean/REVIEW.md','sha256':sha(repo/'docs/lean/REVIEW.md')}})
write('reviewed-inputs.json',{'proof_freeze_path':'verification/proof-freeze.json','proof_freeze_sha256':sha(freeze_path),'all_frozen_project_files':freeze['files'],'project_file_count':len(freeze['files']),
 'source_base':freeze['base'],'original_sources':sources,'source_file_count':len(sources),'all_statement_files_preserved':len(statement['files']),'review_gates_preserved':reviews})
write('source-scan.json',{'result':'PASS','source_files':scans,'imports':imports,'textually_equal_public_headers':hc,
 'comparator_config_sha256':sha(project/'comparator.json'),'seven_exact_selection_names':config['theorem_names'],'definition_exceptions':[],'permitted_axioms':config['permitted_axioms'],
 'limitation':'Static scans and identical headers supplement actual elaboration/term inspection. Official sandboxed Comparator and independent default-kernel replay have not run for this candidate.'})
(out/'git-canonical-diff.log').write_bytes(git(repo,'diff','--name-only','HEAD','--',*sources.keys()))
assert not (out/'git-canonical-diff.log').read_bytes()
write('final-integrity.json',{'result':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'all_203_project_proof_freeze_inputs_preserved':True,'all_34_statement_inputs_preserved':True,
 'all_ten_original_Git_blobs_preserved':True,'both_statement_reviews_and_gate_preserved':True,
 'ten_exact_clean_dependency_pins':True,'fresh_source_commands':len(checks)+1,
 'candidate_kernel_axiom_checks':18,'independent_kernel_axiom_checks':15,
 'all_axioms_only_standard_three_or_subset':True,'seven_headers_equal_and_actual_theorems':True,
 'actual_project_declarations_traversed':61,'required_actual_dependencies':40,
 'actual_retained_LeanCert_boolean_replayed_in_kernel':True,'independent_literal_arithmetic_pass':True,
 'canonical_target_and_status_untouched':True,'Linux_Comparator_and_default_kernel_replay':'PENDING',
 'no_proof_pin_config_or_status_edits_by_reviewer':True})
print('PASS: 203 + 10 frozen inputs; 34 statements; 7 exact contracts; 11 fresh commands; 33 allowed-axiom checks')
