"""Independent exact diagnostic reconstruction from frozen RA08 Lean literals.
No external numerical library, oracle, native evaluator, or spectral approximation.
This is supplementary mathematical review; it is not a Lean proof premise."""
from pathlib import Path
from fractions import Fraction as Q
import ast, hashlib, json, re
P=Path(__file__).resolve().parents[2]
E=Path(__file__).resolve().parent
S=(P/'NLA/RA08/Definitions.lean').read_text()
C=(P/'NLA/RA08/Certificate.lean').read_text()
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
F=json.loads((P/'verification/proof-freeze.json').read_text())
for f in ['NLA/RA08/Definitions.lean','NLA/RA08/Certificate.lean','NLA/RA08/Scalar.lean']:
 assert sha(P/f)==F['files'][f]
def body(name,src=S):
 m=re.search(r'^def '+name+r'\b[\s\S]*?:=\s*',src,re.M);assert m,name
 return re.split(r'\n(?:def |theorem |end |#)',src[m.end():],1)[0].split('/--',1)[0].strip()
env={}
def rat(s):
 s=s.strip()
 def run(t):
  if isinstance(t,ast.Constant) and isinstance(t.value,int):return Q(t.value)
  if isinstance(t,ast.Name):return env[t.id]
  if isinstance(t,ast.UnaryOp) and isinstance(t.op,ast.USub):return -run(t.operand)
  if isinstance(t,ast.BinOp):
   a,b=run(t.left),run(t.right)
   if isinstance(t.op,ast.Add):return a+b
   if isinstance(t.op,ast.Sub):return a-b
   if isinstance(t.op,ast.Mult):return a*b
   if isinstance(t.op,ast.Div):return a/b
  raise ValueError(ast.dump(t))
 return run(ast.parse(s,mode='eval').body)
for n in ['witnessT','witnessA','witnessB','minorantCoefficient','witnessGap']:env[n]=rat(body(n))
t,a,b,c,g=[env[n] for n in ['witnessT','witnessA','witnessB','minorantCoefficient','witnessGap']]
def vec(n,src=S):return [rat(x) for x in re.search(r'!\[([\s\S]*?)\]',body(n,src)).group(1).split(',')]
def mat(n):
 s=body(n);factor=rat(re.search(r'\((.*?)\s*:\s*ℝ\)\s*•',s).group(1))
 return [[factor*rat(x) for x in row.split(',')] for row in re.search(r'!!\[([\s\S]*?)\]',s).group(1).split(';')]
def I(n):return [[Q(i==j) for j in range(n)] for i in range(n)]
def tr(A):return list(map(list,zip(*A)))
def mul(A,B):return [[sum(x*y for x,y in zip(r,col)) for col in zip(*B)] for r in A]
def mv(A,x):return [sum(a*b for a,b in zip(r,x)) for r in A]
def sm(r,A):return [[r*x for x in row] for row in A]
def add(A,B):return [[x+y for x,y in zip(ar,br)] for ar,br in zip(A,B)]
def sub(A,B):return add(A,sm(-1,B))
def dot(x,y):return sum(a*b for a,b in zip(x,y))
def diag(v):return [[x if i==j else Q(0) for j in range(len(v))] for i,x in enumerate(v)]
def principal(A,inds):return [[A[i][j] for j in inds] for i in inds]
def ldl(A):
 assert A==tr(A)
 B=[r[:] for r in A]; piv=[]
 for i in range(len(A)):
  d=B[i][i];piv.append(d);assert d>=0,(i,d)
  if d==0:
   assert all(B[i][j]==0 for j in range(i,len(A))),i
  else:
   for j in range(i+1,len(A)):
    for k in range(i+1,len(A)):B[j][k]-=B[j][i]*B[i][k]/d
 return piv
U=mat('witnessU');Fmat=mat('witnessF');d=vec('witnessApproximation')
Ah=diag(d);A=add(Ah,sm(t,Fmat));w=vec('witnessVector');image=diag(vec('witnessApproximationImage'))
assert mul(tr(U),U)==I(2)
assert mul(Fmat,Fmat)==Fmat==tr(Fmat)
Eblock=mul(U,tr(U))
block=[[Q(0) for j in range(6)] for i in range(6)]
for i in range(3):
 for j in range(3):block[i][j]=Q(64,65)*Eblock[i][j]
 for j in range(2):block[i][3+j]=Q(8,65)*U[i][j];block[3+j][i]=block[i][3+j]
for j in range(2):block[3+j][3+j]=Q(1,65)
block[5][5]=1
assert block==Fmat
pA=ldl(A);assert all(x>0 for x in pA)
pF=ldl(Fmat);pFc=ldl(sub(I(6),Fmat))
comp=principal(sub(sm(b+t,I(6)),A),[0,1,3,4,5])
pcomp=ldl(comp);assert all(x>0 for x in pcomp)
assert A[2][2]>=a and 0<t and b+t<1
plow=ldl(principal(sub(A,sm(t,I(6))),[0,1,2,5]))
pupp=ldl(principal(sub(sm(t,I(6)),A),[3,4,5]))
assert mv(Fmat,[Q(i==5) for i in range(6)])==[Q(i==5) for i in range(6)]
v1=mv(sub(A,sm(b,I(6))),w)
v2=mv(sub(A,sm(Q(1,2),I(6))),v1)
v3=mv(A,v2)
assert v1==vec('firstProductVector',C)
assert v2==vec('secondProductVector',C)
assert v3==vec('witnessKVector')
assert dot(w,w)==26 and dot(w,mv(Fmat,w))==Q(14912,585)
assert dot(v3,v3)==Q(1800760572753083906132034496291,1019907849866242673982515970048000)
def pm(p,q):
 r=[Q(0)]*(len(p)+len(q)-1)
 for i,u in enumerate(p):
  for j,v in enumerate(q):r[i+j]+=u*v
 return r
def pa(p,q):
 r=[Q(0)]*max(len(p),len(q))
 for i,v in enumerate(p):r[i]+=v
 for i,v in enumerate(q):r[i]+=v
 return r
def ps(p,r):return [r*x for x in p]
def pe(p,x):return sum(v*x**i for i,v in enumerate(p))
cub=pm(pm([0,1],[-Q(1,2),1]),[-b,1])
h=pa([0,1],ps(pm(cub,cub),-c))
shift=[Q(0)]*7
for i,v in enumerate(h):
 poly=[Q(1)]
 for j in range(i):poly=pm(poly,[a,1])
 shift=pa(shift,ps(poly,-v))
shift[0]+=1
expected=[0,Q(19,17),Q(537952,23409),Q(2069504,23409),Q(288428032,1896129),Q(227540992,1896129),Q(67108864,1896129)]
assert shift==expected and all(v>0 for v in shift[1:])
scalar=(P/'NLA/RA08/Scalar.lean').read_text()
for v in expected[1:]:
 assert f'{v.numerator} / {v.denominator}' in scalar
assert all(x>=0 for x in d)
assert all(x-c*pe(cub,x)**2<=min(x,1) for x in [Q(0),Q(1,2),b,a])
assert all(x-Q(2048,1377)*pe(cub,x)==min(x,1) for x in d)
assert [min(x,1) for x in d]==vec('witnessApproximationImage')
ray=dot(w,mv(sub(A,image),w))-c*dot(v3,v3)
assert ray==26*t*(1+g) and g>0
assert g<Q(334583,15769728)
def data(v):
 if isinstance(v,Q):return str(v.numerator)+'/'+str(v.denominator)
 if isinstance(v,list):return [data(x) for x in v]
 if isinstance(v,dict):return {k:data(x) for k,x in v.items()}
 return v
out={'result':'PASS','scope':'Independent exact diagnostic, not a formal proof premise or a numerical spectrum calculation.',
 'source_sha256':{n:sha(P/n) for n in ['NLA/RA08/Definitions.lean','NLA/RA08/Certificate.lean','NLA/RA08/Scalar.lean']},
 'read_from_actual_frozen_Lean_literals':True,
 'source_block_projection_matches':True,'U_transpose_U_identity':True,'symmetric_projection':True,
 'A_positive_LDL_pivots':pA,'F_PSD_LDL_pivots':pF,'complement_PSD_LDL_pivots':pFc,
 'five_dimensional_compression_upper_LDL_pivots':pcomp,
 'four_dimensional_lower_LDL_pivots':plow,'three_dimensional_upper_LDL_pivots':pupp,
 'first_product':v1,'second_product':v2,'third_product':v3,'Kw_length_squared':dot(v3,v3),
 'minorant_coefficients':h,'one_minus_shift_coefficients':shift,
 'approximation_polynomial_image_matches':True,'rayleigh_value':ray,'gap':g,
 'ratio_weaker_than_source_but_strict':True,'interval_subdivisions':0}
(E/'exact-reconstruction.json').write_text(json.dumps(data(out),indent=2)+'\n')
print('PASS exact source projection, PSD/PD compression and fourth-value forms, three products, minorant and strict rational gap.')
