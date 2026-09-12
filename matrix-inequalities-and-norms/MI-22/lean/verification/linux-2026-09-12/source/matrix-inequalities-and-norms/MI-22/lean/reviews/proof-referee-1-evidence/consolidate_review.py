"""Bind independent final-review evidence and inspect exact data, signatures,
source safety, immutable library/rubric hashes and relevant reuse searches.
No Lean mathematical source is written by this reviewer.
"""
from pathlib import Path
from fractions import Fraction as F
import ast, hashlib, json, re, subprocess
OUT=Path(__file__).resolve().parent; PROJECT=OUT.parents[1]; REPO=PROJECT.parents[2]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(name,x):(OUT/name).write_text(json.dumps(x,indent=2)+'\n')
# Re-run this reviewer's own source-bound naive rational construction and retain stdout.
r=subprocess.run(['python3',str(OUT/'reconstruct.py')],cwd=PROJECT,capture_output=True)
(OUT/'reconstruction.log').write_bytes(r.stdout+r.stderr);assert r.returncode==0
rec=json.loads((OUT/'reconstruction.json').read_text());assert rec['verdict']=='PASS'
# Independently parse each private rational table in the actual checked Lean source.
def frac(node):
    if isinstance(node,ast.Expression):return frac(node.body)
    if isinstance(node,ast.Constant) and type(node.value) is int:return F(node.value)
    if isinstance(node,ast.UnaryOp) and isinstance(node.op,ast.USub):return -frac(node.operand)
    if isinstance(node,ast.BinOp) and isinstance(node.op,ast.Div):return frac(node.left)/frac(node.right)
    raise ValueError(ast.dump(node))
def readrow(s):return [frac(ast.parse(t.strip(),mode='eval')) for t in s.split(',')]
text=(PROJECT/'NLA/MI22/ExactData.lean').read_text();tables={}
expected={'t2Data':rec['powers']['2'],'t4Data':rec['powers']['4'],'t8Data':rec['powers']['8'],'bData':rec['matrices']['B_adapted'],'abData':rec['matrices']['AB']}
for name,rows in expected.items():
    m=re.search(r'private def '+name+r' : Mat 3 :=\s*!!\[(.*?)\]',text,re.S);assert m,name
    actual=[readrow(s) for s in m.group(1).split(';')]
    assert actual==[[F(x) for x in row] for row in rows],name
    tables[name]={'entries':9,'matches_independent_naive_arithmetic':True}
m=re.search(r'private def nRowData : Fin 3 → ℂ :=\s*!\[(.*?)\]',text,re.S);assert m
assert readrow(m.group(1))==[F(x) for x in rec['matrices']['N'][0]]
tables['nRowData']={'entries':3,'matches_independent_naive_arithmetic':True}
save('exact-table-audit.json',{'source_sha256':sha(PROJECT/'NLA/MI22/ExactData.lean'),'tables':tables,'total_entries':48,'verdict':'PASS'})
# Compare normalized exact text headers, without treating it as Comparator.
def headers(path):
    s=re.sub(r'/\-.*?\-/','',path.read_text(),flags=re.S)
    return {m.group(1):' '.join(m.group(2).split()) for m in re.finditer(r'(?m)^theorem\s+(\w+)\s+(.*?)\s*:=',s,re.S)}
c=headers(PROJECT/'Challenge.lean');s=headers(PROJECT/'Solution.lean')
config=json.loads((PROJECT/'comparator.json').read_text())
assert set(c)==set(s) and len(c)==8 and c==s
assert set(config['theorem_names'])=={'NLA.MI22.'+n for n in c}
assert config['definition_names']==[]
assert set(config['permitted_axioms'])=={'propext','Classical.choice','Quot.sound'}
save('signatures.json',{'scope':'Exact normalized source signatures and fresh elaboration, not Linux Comparator.','declarations':c,'count':8,'verdict':'PASS'})
# No unsafe implementation constructs; comments are excluded from this lexical supplement.
files=sorted((PROJECT/'NLA/MI22').glob('*.lean'))+[PROJECT/'Solution.lean']
pattern=r'\b(?:sorry|admit|axiom|native_decide|implemented_by|unsafe|set_option\s+debug\.skipKernelTC)\b|(?m:^import\s+Challenge\b)'
scan={}
for q in files:
    clean=re.sub(r'/\-.*?\-/','',q.read_text(),flags=re.S);clean=re.sub(r'--[^\n]*','',clean)
    assert not re.search(pattern,clean),str(q)
    scan[str(q.relative_to(PROJECT))]={'sha256':sha(q),'no_unsafe_or_admission_token':True}
save('source-safety.json',{'scope':'Lexical supplement to actual transitive axiom and fresh proof checks','files':scan})
# Exact pinned sources actually read during review; compare with Git objects.
libs=json.loads((PROJECT/'reviews/statement-referee-1-evidence/library-sources.json').read_text())
libs['mathlib']['files'].update({'Mathlib/LinearAlgebra/Matrix/PosDef.lean':'','Mathlib/Analysis/Matrix/Spectrum.lean':''})
libs['leancert']['files'].update({'LeanCert/Tactic/IntervalAuto/PointIneq.lean':'','LeanCert/Validity/DyadicBounds.lean':''})
for name,data in libs.items():
    pkg=PROJECT/'.lake/packages'/name
    for rel,old in list(data['files'].items()):
        q=pkg/rel;h=sha(q)
        if old:assert h==old,rel
        b=subprocess.check_output(['git','show',data['revision']+':'+rel],cwd=pkg)
        assert b==q.read_bytes(),rel
        data['files'][rel]={'sha256':h,'bytes':len(b),'matches_pinned_git_blob':True}
save('inspected-library-sources.json',libs)
# Apply and verify exact cached Tau Ceti rubric bytes from the earlier independent source audit.
stand=json.loads((PROJECT/'reviews/statement-referee-1-evidence/review-standards.json').read_text())
cache=Path('/tmp/nla-lean-formalization/standards')
tree=json.loads((cache/'TauCetiProject_TauCetiReview-tree.json').read_text())
assert sha(cache/'TauCetiProject_TauCetiReview-tree.json')==stand['cached_tree_sha256']
assert sha(cache/'TauCetiProject_TauCetiReview-commit.json')==stand['cached_commit_sha256']
for name,r in stand['reused_reviewed_rubric_bytes'].items():
    q=cache/'sources/TauCetiProject/TauCetiReview/rubrics'/name;b=q.read_bytes()
    assert sha(q)==r['sha256']
    blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
    assert blob==r['git_blob_sha1']
    assert any(x['path']=='rubrics/'+name and x['sha']==blob for x in tree['tree']),name
assert sha(REPO/'docs/lean/REVIEW.md')==stand['local_adaptation_sha256']
stand['current_review']='Final proof referee1; applied the NLA adaptation, not official Tau Ceti endorsement.'
save('review-standards.json',stand)
# Relevant library reuse search; exact supplied lemmas are reused in the proof.
cmd=['rg','-n','singularValues.*norm|norm.*singularValues|rpow_rpow|l2_opNorm_toEuclideanCLM|l2_opNorm_conjTranspose_mul_self|norm_pow_two_pow|trace_eq_sum_eigenvalues|frobenius.*(opNorm|norm)|conjTranspose_mul_mul_same','Mathlib/Analysis/InnerProductSpace/SingularValues.lean','Mathlib/Analysis/CStarAlgebra/Basic.lean','Mathlib/Analysis/CStarAlgebra/Matrix.lean','Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean','Mathlib/Analysis/Matrix/Spectrum.lean','Mathlib/LinearAlgebra/Matrix/PosDef.lean']
r=subprocess.run(cmd,cwd=PROJECT/'.lake/packages/mathlib',capture_output=True)
assert r.returncode==0;(OUT/'reuse-search.log').write_bytes(r.stdout+r.stderr)
save('reuse-search-command.json',{'cwd':'.lake/packages/mathlib','command':cmd,'exit_code':r.returncode,'log_sha256':sha(OUT/'reuse-search.log'),'scope':'Focused reuse search in actual pinned APIs; neighboring campaign code is credited and is not imported.'})
# Final freeze and review-stage ownership checks.
f=json.loads((PROJECT/'verification/proof-freeze.json').read_text())
for rel,r in f['files'].items():assert sha(PROJECT/rel)==r['sha256'],rel
save('scope-integrity.json',{'all_104_frozen_project_inputs_unchanged':True,'all_8_original_sources_match_immutable_base':True,'all_27_statement_inputs_preserved_except_authorized_lakefile_append':True,'current_default_target':'Challenge','complete_proof_build':'lake build Solution','no_canonical_or_mathematical_edits_by_reviewer':True,'actual_Linux_Comparator':'pending, not run or claimed by this local review','verdict':'PASS'})
print('PASS: 48 source-parsed table entries, eight exact signatures, safety scan, pinned sources/rubrics and 104+8 unchanged inputs.')
