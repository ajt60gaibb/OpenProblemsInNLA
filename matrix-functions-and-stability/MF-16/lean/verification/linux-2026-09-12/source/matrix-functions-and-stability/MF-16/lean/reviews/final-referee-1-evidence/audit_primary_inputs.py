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
names={
'leancert':[
'LeanCert/Engine/RootFinding/Krawczyk.lean',
'LeanCert/Core/Support.lean','LeanCert/Core/Expr.lean','LeanCert/Core/IntervalRat/Basic.lean',
'LeanCert/Tactic/Verification.lean','LeanCert/Examples/Krawczyk.lean'],
'mathlib':[
'Mathlib/LinearAlgebra/Matrix/PosDef.lean','Mathlib/Analysis/Complex/Order.lean',
'Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean','Mathlib/LinearAlgebra/Matrix/Charpoly/Coeff.lean',
'Mathlib/Data/Matrix/Basic.lean','Mathlib/Data/Matrix/Mul.lean']}
pins={'leancert':'621a43d7cf21f87872392a01e874f2f1dbddc926','mathlib':'0df444a360eaa60ab8c11dca51a86af692955474'}
for dep,paths in names.items():
 for p in paths:
    raw=(D/dep/p).read_bytes()
    assert raw==git(D/dep,'show',pins[dep]+':'+p)
    apis[dep+'/'+p]={'sha256':sha(raw),'bytes':len(raw),'commit':pins[dep],
      'git_blob':blob(raw),'scope':'Relevant actual definitions/proofs and API search; Krawczyk module read completely'}
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
('positive-definite-reuse',r'posDef.*fin_two|posDef.*det|posDef.*ofReal|PosDef.*ofReal|posDef.*two_by_two|posDef.*twoByTwo|posDef.*map|posDef_iff.*minor|Sylvester.*criterion',
 ['Mathlib/LinearAlgebra/Matrix','Mathlib/Analysis/Matrix']),
('matrix-bridges-and-CH',r'aeval_self_charpoly|charpoly_fin_two|map_mul|map_pow',
 ['Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean','Mathlib/LinearAlgebra/Matrix/Charpoly/Coeff.lean','Mathlib/Data/Matrix/Basic.lean','Mathlib/Data/Matrix/Mul.lean'])]
rows=[]
for name,pattern,paths in queries:
 cmd=['rg','-n',pattern,*paths]
 cp=subprocess.run(cmd,cwd=D/'mathlib',stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 assert cp.returncode in (0,1)
 f=E/(name+'.log');f.write_bytes(cp.stdout)
 rows.append({'command':cmd,'cwd':str(D/'mathlib'),'exit_code':cp.returncode,
   'raw_log':f.name,'sha256':sha(cp.stdout)})
(E/'reuse-searches.json').write_text(json.dumps({'searches':rows,
'conclusion':'Located and reused Mathlib actual CH, matrix homomorphisms and PD congruence APIs; no direct existing complex 2x2 leading-minor lemma located. Thin complexify helpers characterize the new map and are consumed by the full word bridge. No source-implementation copy from Schiffer.'},indent=2)+'\n')
ids=git(R,'show','5830ed4fb06da0659414a3deb2a40ad327aca052:problem_ids.json')
assert ids==(R/'problem_ids.json').read_bytes()
registry=json.loads(ids)
assert len(registry)==217
assert registry['MF-16']=='matrix-functions-and-stability/MF-16/README.md'
diff=git(R,'diff','--','problem_ids.json','matrix-functions-and-stability/MF-16/README.md','matrix-functions-and-stability/MF-16/problem.tex')
assert diff==b''
(E/'canonical-diff.log').write_bytes(diff)
(E/'permanent-target-check.json').write_text(json.dumps({'result':'PASS','registry_count':217,
'registry_sha256':sha(ids),'canonical_path':registry['MF-16'],
'canonical_and_TeX_tracked_diff_empty':True,'index_generation_performed':False},indent=2)+'\n')
print(json.dumps({'result':'PASS','API_inputs':len(apis),'rubrics':len(rubrics),'example_inputs':len(examples),'permanent_ids':len(registry)}))
