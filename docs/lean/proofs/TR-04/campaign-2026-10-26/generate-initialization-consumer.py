#!/usr/bin/env python3
"""Copy exact public theorem headers into a literal initializer consumer."""
import argparse,re
from pathlib import Path
BASE=Path(__file__).resolve().parent
REPO=BASE.parents[4]
FILES=['MachineTTInitializationScalar','MachineTTHeaderCalls','MachineTTInitializationTrace','MachineTTInitialShape','MachineTTInitialization','MachineTTInitializationFull']
text='import NLA.Proofs.TR04.MachineTTInitializationFull\nset_option leancert.trust "kernel"\nset_option backward.isDefEq.respectTransparency false\nnoncomputable section\nopen NLA.Computation.SVDMachine NLA.Computation.TensorTrainApproximation NLA.Proofs.TR04 NLA.Proofs.TR04.TTMemoryLayout\n'
count=0
for file in FILES:
 source=(REPO/'lean-statements/NLA/Proofs/TR04'/(file+'.lean')).read_text()
 for match in re.finditer(r'^theorem ([A-Za-z0-9_]+)\s*',source,re.M):
  end=re.search(r' :=(?: by)?\n',source[match.end():]);assert end,match[1]
  header=source[match.end():match.end()+end.start()].strip()
  depth=0;colon=None
  for i,c in enumerate(header):
   if c in '({[':depth+=1
   if c in ')}]':depth-=1
   if c==':' and depth==0:colon=i;break
  assert colon is not None,(file,match[1])
  binders,typ=header[:colon].strip(),header[colon+1:].strip()
  forall=('∀ '+binders+',\n  ')if binders else''
  text+='\n-- Literal public theorem header from '+file+'.lean: '+match[1]+'\nexample : '+forall+'(\n    '+typ+'\n  ) := @NLA.Proofs.TR04.'+match[1]+'\n'
  count+=1
EXTRAS='-- Composed original-input endpoint: actual first SVD readiness entails the\n-- actual allocated U/sigma/V pointers and retained original dense input.\nexample (S : Shape) (r : Ranks S) (A : Tensor S) (trace : Trace ttProgram)\n    (ht : LegalTrace ttProgram (Start ttProgram S r A) trace) :\n    ∃ time : ℕ,time≤102*(Size S r+1) ∧\n      (trace.state time).label=167 ∧ (trace.state time).status=.running ∧\n      (trace.state time).memory=InputMemory S r A ∧\n      (trace.state time).natural 72=(ofShape S).firstU ∧\n      (trace.state time).natural 73=(ofShape S).firstSigma ∧\n      (trace.state time).natural 74=(ofShape S).firstV ∧\n      (trace.state time).natural 76=0 ∧\n      CostThrough ttProgram trace time≤102*(Size S r+1) := by\n  obtain ⟨n,_,h,htime,hcost⟩ := ttInitial_svd_ready S r A trace ht\n  exact ⟨ttFirstRankEntryTime S r+n,htime,h.label,h.status,h.memory,\n    h.allocation.firstU,h.allocation.firstSigma,h.allocation.firstV,h.candidateZero,hcost⟩\n\n-- Requested rank zero is still read literally; this support theorem does not\n-- silently narrow the header domain to consistent or positive ranks.\nexample (S : Shape) (A : Tensor S) (trace : Trace ttProgram)\n    (ht : LegalTrace ttProgram (Start ttProgram S (fun _ => 0) A) trace) :\n    ∃ time : ℕ,(trace.state time).label=167 ∧ (trace.state time).natural 80=0 ∧\n      (trace.state time).natural 106=0 := by\n  obtain ⟨n,_,h,_,_⟩ := ttInitial_svd_ready S (fun _ => 0) A trace ht\n  refine ⟨ttFirstRankEntryTime S (fun _ => 0)+n,h.label,?_,?_⟩\n  · exact h.rank\n  · simpa only [ttFirstRankValue,Nat.zero_min] using h.cap\n'
text+='\n'+EXTRAS
parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--check',action='store_true');args=parser.parse_args()
path=BASE/'TTInitializationConsumer.lean.txt'
if args.check:assert path.read_text()==text
else:path.write_text(text)
print({'verbatim_headers':count,'additional_examples':2,'check':args.check})
