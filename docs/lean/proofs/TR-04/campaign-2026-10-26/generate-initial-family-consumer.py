#!/usr/bin/env python3
"""Copy exact public theorem headers into a literal initializer consumer."""
import argparse,re
from pathlib import Path
BASE=Path(__file__).resolve().parent
REPO=BASE.parents[4]
FILES=['MachineTTReadOnly', 'MachineTTInitialMemory', 'MachineTTInitialFamily', 'MachineTTStageProtection']
text='import NLA.Proofs.TR04.MachineTTInitialFamily\nimport NLA.Proofs.TR04.MachineTTStageProtection\nset_option leancert.trust "kernel"\nset_option backward.isDefEq.respectTransparency false\nnoncomputable section\nopen NLA.Computation.SVDMachine NLA.Computation.TensorTrainApproximation NLA.Proofs.TR04 NLA.Proofs.TR04.TTMemoryLayout\n'
count=0
for file in FILES:
 source=(REPO/'lean-statements/NLA/Proofs/TR04'/(file+'.lean')).read_text()
 for match in re.finditer(r'^theorem ([A-Za-z0-9_.]+)\s*',source,re.M):
  end=re.search(r' :=(?: by[^\n]*)?\n',source[match.end():]);assert end,match[1]
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
EXTRAS='-- Actual original-input first-family endpoint, without a preloaded header,\n-- optimizer, SVD basis or evaluation result.\nexample (S : Shape) (r : Ranks S) (A : Tensor S) (hr : ∀ j,1≤r j)\n    (trace : Trace ttProgram) (ht : LegalTrace ttProgram (Start ttProgram S r A) trace) :\n    ∃ time : ℕ,time≤1024*(Size S r+1)^3 ∧\n      (trace.state time).label=189 ∧ (trace.state time).status=.running ∧\n      TTAllocationRegisters (ofShape S) (trace.state time) ∧\n      (trace.state time).natural 76=0 ∧ 0<(trace.state time).natural 75 ∧\n      (∀ a,a<(ofShape S).firstU → (trace.state time).memory a=InputMemory S r A a) ∧\n      CostThrough ttProgram trace time≤1024*(Size S r+1)^3 := by\n  obtain ⟨offset,n,R,_,⟨hi,hphase⟩,_,ha,hj,hcount,hmem,_,_,_,htime,hcost⟩ :=\n    ttInitial_explicit_family S r A hr trace ht\n  exact ⟨offset+n,htime,hphase.1,hphase.2.1,ha,hj,hcount,hmem,hcost⟩\n\n-- The order register is protected by all literal code, including arbitrary\n-- fullSVD replies and every stopped-state continuation.\nexample (S : Shape) (r : Ranks S) (A : Tensor S) (trace : Trace ttProgram)\n    (ht : LegalTrace ttProgram (Start ttProgram S r A) trace) (n : ℕ) :\n    (trace.state n).natural 0=S.order := ttProgram_trace_order S r A trace ht n\n'
text+='\n'+EXTRAS
parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--check',action='store_true');args=parser.parse_args()
path=BASE/'TTInitialFamilyConsumer.lean.txt'
if args.check:assert path.read_text()==text
else:path.write_text(text)
print({'verbatim_headers':count,'additional_examples':2,'check':args.check})
