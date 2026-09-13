"""Independent final RA08 referee 1 exact reconstruction, no numerical oracle.

Parses only arithmetic literals in the actual frozen Lean definitions. Uses
standard-library Fraction, not source verification scripts or numerical spectra.
"""
from pathlib import Path
from fractions import Fraction as F
import ast, datetime, hashlib, json, re
P = Path(__file__).resolve().parents[2]
E = Path(__file__).resolve().parent
W = P.parents[2]
D = (P/'NLA/RA08/Definitions.lean').read_text()
C = (P/'NLA/RA08/Certificate.lean').read_text()
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def block(name, text=D):
    m = re.search(r'^def '+name+r'\b.*?:=\s*(.*?)(?=\n(?:def |theorem |end |/--)|\Z)',text,re.S|re.M)
    assert m, name
    return m[1].strip()
def q(s):
    tree=ast.parse(s.strip(),mode='eval').body
    def visit(t):
        if isinstance(t,ast.Constant) and isinstance(t.value,int): return F(t.value)
        if isinstance(t,ast.UnaryOp) and isinstance(t.op,ast.USub): return -visit(t.operand)
        if isinstance(t,ast.BinOp):
            a,b=visit(t.left),visit(t.right)
            if isinstance(t.op,ast.Add):return a+b
            if isinstance(t.op,ast.Sub):return a-b
            if isinstance(t.op,ast.Mult):return a*b
            if isinstance(t.op,ast.Div):return a/b
        raise ValueError(ast.dump(t))
    return visit(tree)
def vector(name,text=D):
    s=re.search(r'!\[([^]]+)\]',block(name,text),re.S)[1]
    return [q(v) for v in s.replace('\n',' ').split(',')]
def literal_matrix(s):
    raw=re.search(r'!!\[([^]]+)\]',s,re.S)[1]
    return [[q(v) for v in row.replace('\n',' ').split(',')] for row in raw.split(';')]
def mm(A,B):return [[sum((A[i][k]*B[k][j] for k in range(len(B))),F(0)) for j in range(len(B[0]))] for i in range(len(A))]
def mv(A,v):return [sum((x*y for x,y in zip(row,v)),F(0)) for row in A]
def tr(A):return list(map(list,zip(*A)))
def add(A,B):return [[x+y for x,y in zip(a,b)] for a,b in zip(A,B)]
def scale(c,A):return [[c*x for x in row] for row in A]
def sub(A,B):return add(A,scale(-1,B))
def diag(v):return [[v[i] if i==j else F(0) for j in range(len(v))] for i in range(len(v))]
def dot(x,y):return sum((a*b for a,b in zip(x,y)),F(0))
def ldl_pivots(A):
    n=len(A);L=diag([F(1)]*n);out=[]
    for i in range(n):
        d=A[i][i]-sum((L[i][j]**2*out[j] for j in range(i)),F(0));assert d>0
        out.append(d)
        for k in range(i+1,n):L[k][i]=(A[k][i]-sum((L[k][j]*L[i][j]*out[j] for j in range(i)),F(0)))/d
    assert mm(mm(L,diag(out)),tr(L))==A
    return out

t,a,b,c,g=[q(block(n)) for n in ['witnessT','witnessA','witnessB','minorantCoefficient','witnessGap']]
assert t==F(1,65536) and a==F(17,16) and b==F(127,128) and t>0 and b+t<1
assert c==F(67108864,1896129) and g>0
U=scale(F(1,9),literal_matrix(block('witnessU')))
Fl=scale(F(1,5265),literal_matrix(block('witnessF')))
assert mm(tr(U),U)==diag([F(1)]*2)
G=mm(U,tr(U));Fsource=[[F(0) for _ in range(6)] for _ in range(6)]
for i in range(3):
    for j in range(3):Fsource[i][j]=F(64,65)*G[i][j]
    for j in range(2):Fsource[i][j+3]=Fsource[j+3][i]=F(8,65)*U[i][j]
for j in range(2):Fsource[j+3][j+3]=F(1,65)
Fsource[5][5]=F(1)
assert Fl==Fsource
I=diag([F(1)]*6);zero=diag([F(0)]*6)
assert tr(Fl)==Fl and mm(Fl,Fl)==Fl
assert mm(tr(sub(I,Fl)),sub(I,Fl))==sub(I,Fl)
Ah=diag([F(1,2),b,a,F(0),F(0),F(0)]);A=add(Ah,scale(t,Fl))
assert block('witnessMatrix')=='witnessApproximation + witnessT • witnessF'
assert block('witnessApproximation').startswith('Matrix.diagonal ![1 / 2, witnessB, witnessA, 0, 0, 0]')
Apiv=ldl_pivots(A)
sel=[0,1,3,4,5];compression=[[A[i][j] for j in sel] for i in sel]
Cpiv=ldl_pivots(sub(scale(b+t,diag([F(1)]*5)),compression))
e=[F(0)]*5+[F(1)]
assert mv(A,e)==[t*x for x in e] and mv(Fl,e)==e and A[2][2]>=a
w=vector('witnessVector');kw=vector('witnessKVector')
v1=mv(sub(A,scale(b,I)),w);v2=mv(sub(A,scale(F(1,2),I)),v1);v3=mv(A,v2)
assert v1==vector('firstProductVector',C) and v2==vector('secondProductVector',C) and v3==kw
K=mm(mm(A,sub(A,scale(F(1,2),I))),sub(A,scale(b,I)))
assert tr(K)==K and mv(K,w)==kw
Ksquared=dot(kw,kw)
assert Ksquared==F(1800760572753083906132034496291,1019907849866242673982515970048000)
assert dot(w,mv(mm(K,K),w))==Ksquared
assert dot(w,w)==26 and dot(w,mv(Fl,w))==F(14912,585)
image=diag([F(1,2),b,F(1),F(0),F(0),F(0)])
minorant=sub(A,scale(c,mm(K,K)))
quad=dot(w,mv(sub(minorant,image),w))
assert quad==26*t*(1+g) and quad>26*t
assert F(2048,1377)*a*(a-F(1,2))*(a-b)==a-1

# Reconstruct the exact polynomial shift independently with coefficient arrays.
def pa(A,B):
    n=max(len(A),len(B));return [(A[i] if i<len(A) else F(0))+(B[i] if i<len(B) else F(0)) for i in range(n)]
def pm(A,B):
    out=[F(0)]*(len(A)+len(B)-1)
    for i,x in enumerate(A):
        for j,y in enumerate(B):out[i+j]+=x*y
    return out
shift=[a,F(1)];product=[F(1)]
for factor in [shift,[a-F(1,2),F(1)],[a-b,F(1)]]:product=pm(product,pm(factor,factor))
shifted=pa([1-a,F(-1)],[c*x for x in product])
expected=list(map(F,['0','19/17','537952/23409','2069504/23409','288428032/1896129','227540992/1896129','67108864/1896129']))
assert shifted==expected and all(x>0 for x in shifted[1:])
source=W/'references/colbrook-transfer-2026-09-11/manuscripts/03_concave_transfer_counterexamples.tex'
assert r'\frac19\begin{bmatrix}1&8\\8&1\\-4&4\end{bmatrix}' in source.read_text()
record={'verdict':'PASS independent exact rational diagnostics, not a universal proof oracle',
 'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'source_sha256':sha(source),'parsed_Lean_inputs':{str(p.relative_to(P)):sha(p) for p in [P/'NLA/RA08/Definitions.lean',P/'NLA/RA08/Certificate.lean']},
 'unchanged_source_projection':True,'projection_and_complement_Gram_identities':True,
 'positive_actual_witness_LDL_pivots':list(map(str,Apiv)),
 'strict_compression_difference_LDL_pivots':list(map(str,Cpiv)),
 'isolated_actual_eigenpair':str(t),'matvec1':list(map(str,v1)), 'matvec2':list(map(str,v2)),
 'matvec3':list(map(str,v3)),'K_squared_quadratic':str(Ksquared),
 'polynomial_shift_coefficients':list(map(str,shifted)),
 'actual_minorant_quadratic':str(quad),'base_Rayleigh_threshold':str(26*t),'strict_gap':str(g),
 'computed_relative_gap':str(quad/(26*t)-1),
 'scope':'No floating-point spectrum, new matrix, source ratio substitution, interval subdivision or assumed matrix-function value. The genuine spectral/CFC/norm/forall bridges were reviewed separately in Lean.'}
(E/'exact-reconstruction.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2))
