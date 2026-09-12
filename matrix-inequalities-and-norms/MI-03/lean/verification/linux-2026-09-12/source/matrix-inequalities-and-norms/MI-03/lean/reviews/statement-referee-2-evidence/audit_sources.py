"""Bind this independent review's original, library and rubric inputs."""
from pathlib import Path
import hashlib,json,subprocess
OUT=Path(__file__).resolve().parent;P=OUT.parents[1];REPO=P.parents[2]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def put(name,x):(OUT/name).write_text(json.dumps(x,indent=2)+'\n')
frozen=json.loads((P/'reviews/statement-freeze.json').read_text())
for label,base in [('files',P),('source_files',REPO)]:
 for name,h in frozen[label].items():assert sha(base/name)==h,name
assert not (P/'Solution.lean').exists()
assert list((P/'NLA/MI03').glob('*.lean'))==[P/'NLA/MI03/Definitions.lean']
initial=json.loads((OUT/'integrity-before.json').read_text())
for key,rec in initial['identity'].items():
 base=P if key.startswith('files:') else REPO
 assert sha(base/rec['path'])==rec['sha256'],key
put('integrity-after.json',{'status':'PASS','all_27_project_and_8_original_inputs_unchanged':True,'proof_absent':True,'identity':initial['identity']})
M=P/'.lake/packages/mathlib'
paths=['Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean',
 'Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Isometric.lean',
 'Mathlib/Analysis/CStarAlgebra/Matrix.lean','Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Order.lean',
 'Mathlib/Analysis/Matrix/Order.lean','Mathlib/LinearAlgebra/Matrix/PosDef.lean',
 'Mathlib/Analysis/InnerProductSpace/PiL2.lean','Mathlib/Analysis/Normed/Lp/PiLp.lean',
 'Mathlib/RingTheory/RootsOfUnity/Complex.lean','Mathlib/RingTheory/RootsOfUnity/PrimitiveRoots.lean',
 'Mathlib/Order/ConditionallyCompletePartialOrder/Basic.lean']
library={}
for name in paths:
 raw=subprocess.run(['git','show','0df444a360eaa60ab8c11dca51a86af692955474:'+name],cwd=M,stdout=subprocess.PIPE,check=True).stdout
 h=sha(M/name);assert hashlib.sha256(raw).hexdigest()==h
 library[name]={'sha256':h,'matches_pinned_git_blob':True}
put('library-inputs.json',{'pin':'0df444a360eaa60ab8c11dca51a86af692955474','scope':'Read the relevant actual definitions, theorem statements and implementation passages; not a full Mathlib audit','files':library})
S=Path('/tmp/nla-lean-formalization/standards');commit=json.loads((S/'TauCetiProject_TauCetiReview-commit.json').read_text());tree=json.loads((S/'TauCetiProject_TauCetiReview-tree.json').read_text())
assert commit['sha']==tree['sha']=='afb424eda89e8ac96d9eb69f6a88972055a4cd1b' and not tree['truncated']
lookup={x['path']:x for x in tree['tree']};rubrics={}
for name in ['correctness','scope','generality','reuse','attribution']:
 path='rubrics/'+name+'.md';p=S/'sources/TauCetiProject/TauCetiReview'/path;b=p.read_bytes()
 blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();assert blob==lookup[path]['sha'],name
 rubrics[path]={'sha256':sha(p),'git_blob_sha1':blob,'matches_archived_pinned_tree':True}
put('rubric-inputs.json',{'pin':commit['sha'],'commit_record_sha256':sha(S/'TauCetiProject_TauCetiReview-commit.json'),'tree_record_sha256':sha(S/'TauCetiProject_TauCetiReview-tree.json'),'files':rubrics,'local_adaptation':'../../../docs/lean/REVIEW.md','local_adaptation_sha256':sha(REPO/'docs/lean/REVIEW.md')})
print('PASS: all frozen bytes remain unchanged; eleven actual Mathlib source blobs and five adapted rubric blobs match pinned trees; no proof exists')
