#!/usr/bin/env python3
"""Emit only static finite TR-04 caller syntax. This is not a correctness proof."""
import argparse,json
from pathlib import Path

repo=Path(__file__).resolve().parents[6]
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check',action='store_true',help='check exact reproduction without writing files')
args=parser.parse_args()
out=repo/'lean-statements/NLA/Proofs/TR04/MachineTTProgram.lean'
regs={'D':0,'hc':1,'hp':2,'hz':3,'N':64,'N2':66,'frames':67,'meta':68,
      'workA':69,'workB':70,'store':71,'U':72,'sigma':73,'V':74,'K':75,'j':76,
      'h':77,'t':78,'s':79,'r':80,'m0':81,'l0':82,'output':83,'level':84,
      'm':85,'q':86,'l':87,'stride':88,'current':89,'next':90,'input':92,
      'mp':93,'frame':94,'tag':97,'previousRank':100,'childSigma':103,
      'childV':104,'p':105,'firstRank':106,'forwardTag':108,'mode':109,
      'lastLevel':110,'address':122,'tmp':123,'four':125,'one':126,'zero':127}
body=[];labels={}
def reg(x):return regs[x] if isinstance(x,str) else x
def mark(name):
    assert name not in labels
    labels[name]=119+len(body)
def ins(op,*args,next=None):
    body.append({'op':op,'operands':[reg(x) for x in args],
                 'successors':[next] if next is not None else [119+len(body)+1]})
def branch(op,a,b,yes,no):body.append({'op':op,'operands':[reg(a),reg(b)],'successors':[yes,no]})
def jump(to):body.append({'op':'jump','operands':[],'successors':[to]})
def svd(rows,cols,src,u,s,v,to):body.append({'op':'svd','operands':list(map(reg,[rows,cols,src,u,s,v])),'successors':[to]})
def single(address,tag):
    ins('read',0,address);ins('copyNat','hc','D');ins('natural','hp',1)
    ins('natural','hz',0);ins('natural','tag',tag);jump(5)
def suffix(cursor,tag,increment=False):
    ins('copyNat','hc',cursor)
    if increment:ins('increment','hc')
    ins('natural','hp',1);ins('natural','hz',0);ins('natural','tag',tag);jump(2)
def cap(q,m,l,prefix):
    branch('lessNat',m,q,prefix+'_cap_rows',prefix+'_cap_cols_test')
    mark(prefix+'_cap_rows');ins('copyNat',q,m)
    mark(prefix+'_cap_cols_test');branch('lessNat',l,q,prefix+'_cap_cols',prefix+'_cap_done')
    mark(prefix+'_cap_cols');ins('copyNat',q,l)
    mark(prefix+'_cap_done')
def swap():ins('copyNat','tmp','current');ins('copyNat','current','next');ins('copyNat','next','tmp')
def matrix(reverse):
    for dst,src in [(4,'zero'),(5,'l'),(6,'zero'),(7,'m' if reverse else 'q'),
                    (8,'q' if reverse else 'm'),(9,'l'),(10,'frame'),(11,'current'),
                    (12,'next'),(13,'zero'),(14,'zero'),(15,'next'),(16,'zero'),
                    (17,'stride' if reverse else 'one'),(18,'one' if reverse else 'stride'),
                    (19,'l'),(20,'one')]:ins('copyNat',dst,src)
    if reverse:ins('natural','tag',2)
    else:ins('copyNat','tag','forwardTag')
    jump(11)

mark('startup')
ins('copyNat','N','hp');ins('mulNat','N2','N','N')
ins('natural','one',1);ins('natural','four',4)
ins('addNat','input','D','D');ins('decrement','input')
for dst,a,b in [('U','input','N'),('sigma','U','N2'),('V','sigma','N'),
                ('childSigma','V','N2'),('childV','childSigma','N'),('frames','childV','N2')]:ins('addNat',dst,a,b)
ins('mulNat','tmp','D','N2');ins('addNat','meta','frames','tmp')
ins('mulNat','tmp','four','D');ins('addNat','workA','meta','tmp')
ins('addNat','workB','workA','N');ins('addNat','store','workB','N')
ins('natural','j',0);single('zero',1)
mark('first_mode');ins('copyNat','m0','hp');suffix('one',2)
mark('first_cols');ins('copyNat','l0','hp');single('D',3)
mark('first_rank');ins('copyNat','r','hp');ins('copyNat','p','m0')
branch('lessNat','l0','p','first_p_cols','first_p_done')
mark('first_p_cols');ins('copyNat','p','l0')
mark('first_p_done');ins('copyNat','q','r');cap('q','m0','l0','first')
ins('copyNat','firstRank','q');svd('m0','l0','input','U','sigma','V','first_svd_return')
mark('first_svd_return');branch('lessNat','p','r','prefix','read_threshold')
mark('read_threshold');ins('copyNat','address','r');ins('decrement','address')
ins('addNat','address','sigma','address');ins('read',7,'address');ins('castNat',13,'zero')
branch('lessReal',13,7,'threshold_setup','prefix')
mark('threshold_setup');ins('copyNat',42,'p');ins('copyNat',43,'r');ins('copyNat',44,'sigma');jump(66)
mark('threshold_return');ins('copyNat','h',46);ins('copyNat','t',47);ins('copyNat','s',48)
ins('copyNat','K','t');jump('candidate_loop')
mark('prefix');ins('copyNat','h','firstRank');ins('natural','t',1)
ins('natural','s',0);ins('natural','K',1);jump('candidate_loop')
mark('candidate_loop');branch('lessNat','j','K','gather_setup','best_setup')
mark('gather_setup')
for dst,src in [(27,'m0'),(28,'h'),(29,'t'),(30,'s'),(31,'j'),(32,'U'),(33,'frames')]:ins('copyNat',dst,src)
jump(40)
mark('gather_return');ins('natural','level',0)
for dst,src in [('m','m0'),('q','firstRank'),('l','l0'),('stride','firstRank'),
                ('frame','frames'),('current','input'),('next','workA')]:ins('copyNat',dst,src)
ins('natural','forwardTag',0);jump('write_metadata')
mark('child_start');single('level',4)
mark('child_mode');ins('copyNat','mode','hp');ins('mulNat','m','previousRank','mode');suffix('level',5,True)
mark('child_cols');ins('copyNat','l','hp');ins('addNat','address','D','level');single('address',6)
mark('child_rank');ins('copyNat','q','hp');cap('q','m','l','child')
ins('mulNat','frame','level','N2');ins('addNat','frame','frames','frame')
svd('m','l','current','frame','childSigma','childV','child_svd_return')
mark('child_svd_return');ins('copyNat','stride','m');ins('natural','forwardTag',1);jump('write_metadata')
mark('write_metadata');ins('mulNat','mp','four','level');ins('addNat','mp','meta','mp')
for src in ['m','q','l','stride']:
    ins('castNat',13,src);ins('write','mp',13);ins('increment','mp')
matrix(False)
mark('first_contract_return');ins('copyNat','current','workA');ins('copyNat','next','workB');jump('forward_return')
mark('child_contract_return');swap();jump('forward_return')
mark('forward_return');ins('copyNat','previousRank','q');ins('increment','level')
ins('copyNat','lastLevel','D');ins('decrement','lastLevel')
branch('lessNat','level','lastLevel','child_start','reverse_start')
mark('reverse_start');ins('decrement','level')
mark('reverse_read');ins('mulNat','mp','four','level');ins('addNat','mp','meta','mp');single('mp',7)
mark('reverse_rows');ins('copyNat','m','hp');ins('increment','mp');single('mp',8)
mark('reverse_rank');ins('copyNat','q','hp');ins('increment','mp');single('mp',9)
mark('reverse_cols');ins('copyNat','l','hp');ins('increment','mp');single('mp',10)
mark('reverse_stride');ins('copyNat','stride','hp')
ins('mulNat','frame','level','N2');ins('addNat','frame','frames','frame');matrix(True)
mark('lift_return');swap();branch('equalNat','level','zero','copy_candidate','reverse_decrement')
mark('reverse_decrement');ins('decrement','level');jump('reverse_read')
mark('copy_candidate');ins('mulNat','tmp','j','N');ins('addNat','tmp','store','tmp')
for dst,src in [(21,'zero'),(22,'N'),(23,'current'),(24,'tmp'),(25,'tmp')]:ins('copyNat',dst,src)
jump(33)
mark('copy_return');ins('increment','j');jump('candidate_loop')
mark('best_setup')
for dst,src in [(49,'K'),(50,'N'),(51,'input'),(52,'store'),(53,'zero'),(54,'zero'),
                (55,'store'),(56,'store'),(57,'zero'),(58,'zero'),(59,'zero'),(60,'zero'),(61,'zero')]:ins('copyNat',dst,src)
jump(89)
mark('halt');body.append({'op':'halt','operands':[regs['output']],'successors':[]})
mark('header_dispatch')
for tag,target in enumerate(['startup','first_mode','first_cols','first_rank','child_mode','child_cols',
                             'child_rank','reverse_rows','reverse_rank','reverse_cols','reverse_stride']):
    mark(f'header_tag_{tag}');ins('natural','tmp',tag)
    branch('equalNat','tag','tmp',target,f'header_tag_{tag+1}' if tag<10 else 'halt')

assert 119+len(body)<=512,len(body)
fixed={10:('jump',[],['header_dispatch']),32:('equalNat',[regs['tag'],regs['zero']],['first_contract_return','matrix_dispatch_1']),
       39:('jump',[],['copy_return']),65:('jump',[],['gather_return']),88:('jump',[],['threshold_return']),
       114:('copyNat',[regs['output'],55],['halt'])}
mark('matrix_dispatch_1');branch('equalNat','tag','one','child_contract_return','lift_return')
assert 119+len(body)<=512
def resolve(x):return labels[x] if isinstance(x,str) else x
def line(n,op,args,succ):return f"    | {n} => .{op} "+' '.join(map(str,args+list(map(resolve,succ))))
lines=[line(n,*fixed[n]) for n in sorted(fixed)]
aliases={}
for name,n in labels.items():aliases.setdefault(n,[]).append(name)
for i,item in enumerate(body,119):
    if i in aliases:lines.append('    -- '+', '.join(aliases[i]))
    lines.append(line(i,item['op'],item['operands'],item['successors']))
text='''import NLA.Proofs.TR04.MachineCodeBanks
import NLA.Proofs.TR04.MachineHeaderProduct
import NLA.Proofs.TR04.MachineMatrixMultiply
import NLA.Proofs.TR04.MachineCopy
import NLA.Proofs.TR04.MachineFrameGather
import NLA.Proofs.TR04.MachineThresholdScan
import NLA.Proofs.TR04.MachineBestCandidate

/-! One fixed finite candidate-family TT program, assembled from actual RAM
instruction banks and static caller syntax. Mathematical correctness and the
whole charged-cost bound are proved separately; this file alone claims neither.
Generated by the retained generate-controller.py; no input is compiled in. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

def ttControllerProgram : Program where
  extraLabels := 511
  realRegisters := 16
  extraNatRegisters := 127
  constantCount := 0
  constants := Fin.elim0
  code label := match label.val with
'''+ '\n'.join(lines)+'''
    | _ => .halt 83

'''
banks=[('Header','headerProductProgram',0,0,0),('Matrix','matrixMultiplyProgram',11,2,4),
       ('Copy','copyProgram',33,5,21),('Gather','frameGatherProgram',40,6,26),
       ('Threshold','thresholdScanProgram',66,7,41),('Best','bestCandidateProgram',89,9,49)]
for i,(name,p,base,r,n) in enumerate(banks,1):
    prev='ttControllerProgram' if i==1 else f'ttBankStage{i-1}'
    text+=f'''def tt{name}Registers : BankRegisters {p} {prev} :=
  offsetBankRegisters {p} {prev} {r} {n} (by decide) (by decide) rfl

def ttBankStage{i} : Program := installCodeBank {p} {prev} tt{name}Registers {base} (by decide)

'''
text+='def ttProgram : Program := ttBankStage6\n\n'
for i,(name,p,base,r,n) in enumerate(banks,1):
    prev='ttControllerProgram' if i==1 else f'ttBankStage{i-1}'
    text+=f'''def tt{name}EmbeddingStage{i} : RoutineEmbedding {p} ttBankStage{i} :=
  installedBankEmbedding {p} {prev} tt{name}Registers {base} (by decide)

'''
    for k in range(i+1,7):
        later,lp,lb,lr,ln=banks[k-1]
        text+=f'''def tt{name}EmbeddingStage{k} : RoutineEmbedding {p} ttBankStage{k} :=
  (tt{name}EmbeddingStage{k-1}).throughInstalledBank tt{later}Registers {lb} (by decide) (by
    intro label hn
    change ¬({lb}≤{base}+label.val ∧ {base}+label.val<{lb}+({lp}.extraLabels+1))
    have hlt := label.isLt
    change label.val<{p}.extraLabels+1 at hlt
    norm_num only [{p}, {lp}] at hlt ⊢
    omega)

'''
    text+=f'def tt{name}Embedding : RoutineEmbedding {p} ttProgram := tt{name}EmbeddingStage6\n\n'
for name in ['ttControllerProgram','ttProgram']+[f'tt{x[0]}Embedding' for x in banks]:
    text+=f'#assert_trust kernel {name}\n#print axioms {name}\n'
text+='end NLA.Proofs.TR04\n'
layout=json.dumps({
    'scope':'Static finite caller syntax, not a correctness or complexity theorem',
    'label_count':512,'real_registers':16,'natural_registers':128,'constant_count':0,
    'caller_instructions':len(body),'registers':regs,'labels':labels,'banks':banks,
    'full_TR04_Target_proved':False},indent=2)+'\n'
layout_path=Path(__file__).with_name('controller-layout.json')
if args.check:
    assert out.read_text()==text,'generated finite Lean program differs'
    assert layout_path.read_text()==layout,'generated controller layout differs'
else:
    out.write_text(text);layout_path.write_text(layout)
print(f'{"Checked" if args.check else "Emitted"} {len(body)} caller instructions; final used label {118+len(body)}; {out}')
