"""Read actual RA-08 draft constants; independent exact Fraction diagnostics.
This is not Lean, a theorem oracle or a numerical eigenvalue computation.
"""
from pathlib import Path
from fractions import Fraction as Q
import ast, hashlib, json, re
P=Path(__file__).resolve().parents[2]
source=(P/'NLA/RA08/Definitions.lean').read_text()

def block(name):
    m=re.search(r'^def '+re.escape(name)+r'\b[\s\S]*?(?=^def |^/--|^end NLA)',source,re.M)
    assert m, name
    return m.group(0)

def num(text,env={}):
    def read(n):
        if isinstance(n,ast.Constant) and type(n.value) is int:return Q(n.value)
        if isinstance(n,ast.Name) and n.id in env:return env[n.id]
        if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.USub):return -read(n.operand)
        if isinstance(n,ast.BinOp):
            a,b=read(n.left),read(n.right)
            if isinstance(n.op,ast.Div):return a/b
            if isinstance(n.op,ast.Add):return a+b
            if isinstance(n.op,ast.Sub):return a-b
            if isinstance(n.op,ast.Mult):return a*b
        raise ValueError(ast.dump(n))
    return read(ast.parse(text.strip(),mode='eval').body)

def scalar(name):return num(block(name).split(':=',1)[1])
def vector(name,env={}):return [num(x,env) for x in re.search(r'!\[([\s\S]*?)\]',block(name)).group(1).split(',')]
def matrix(name):
    s=block(name);factor=Q(1,int(re.search(r'\(1 / (\d+) : ℝ\)',s).group(1)))
    return [[factor*num(x) for x in row.split(',')] for row in re.search(r'!!\[([\s\S]*?)\]',s).group(1).split(';')]
def dot(x,y):return sum(a*b for a,b in zip(x,y))
def T(A):return list(map(list,zip(*A)))
def mm(A,B):return [[dot(r,c) for c in T(B)] for r in A]
def mv(A,x):return [dot(r,x) for r in A]
def eye(n):return [[Q(i==j) for j in range(n)] for i in range(n)]
def diag(v):return [[v[i] if i==j else Q(0) for j in range(len(v))] for i in range(len(v))]
def plus(A,B):return [[a+b for a,b in zip(r,s)] for r,s in zip(A,B)]
def scale(c,A):return [[c*x for x in r] for r in A]
def ldl(A):
    n=len(A);L=eye(n);d=[]
    for j in range(n):
        dj=A[j][j]-sum(L[j][k]**2*d[k] for k in range(j));assert dj>0,(j,dj)
        d.append(dj)
        for i in range(j+1,n):L[i][j]=(A[i][j]-sum(L[i][k]*L[j][k]*d[k] for k in range(j)))/dj
    assert mm(mm(L,diag(d)),T(L))==A
    return d

t=scalar('witnessT');a=scalar('witnessA');b=scalar('witnessB');c=scalar('minorantCoefficient');gap=scalar('witnessGap')
assert (t,a,b,c)==(Q(1,65536),Q(17,16),Q(127,128),Q(67108864,1896129))
U=matrix('witnessU');F=matrix('witnessF');w=vector('witnessVector');kw=vector('witnessKVector')
v=vector('witnessApproximation',{'witnessA':a,'witnessB':b});Ah=diag(v);A=plus(Ah,scale(t,F));I=eye(6)
image=diag(vector('witnessApproximationImage',{'witnessB':b}))
assert U==[[Q(1,9),Q(8,9)],[Q(8,9),Q(1,9)],[Q(-4,9),Q(4,9)]]
E=mm(U,T(U));Fs=[[Q(0) for _ in range(6)] for _ in range(6)]
for i in range(3):
    for j in range(3):Fs[i][j]=Q(64,65)*E[i][j]
    for j in range(2):Fs[i][j+3]=Fs[j+3][i]=Q(8,65)*U[i][j]
for i in range(2):Fs[i+3][i+3]=Q(1,65)
Fs[5][5]=1
assert F==Fs and mm(T(U),U)==eye(2)
assert T(F)==F and mm(F,F)==F and sum(F[i][i] for i in range(6))==3
IF=plus(I,scale(-1,F));assert mm(IF,IF)==IF and T(IF)==IF
assert t>0 and b+t==Q(65025,65536)<1
Apivots=ldl(A)
e6=[Q(0)]*5+[Q(1)];assert mv(A,e6)==[t*x for x in e6]
ids=[0,1,3,4,5];D=[[A[i][j] for j in ids] for i in ids]
compression_pivots=ldl(plus(scale(b+t,eye(5)),scale(-1,D)))
assert A[2][2]>=a
Mb=plus(A,scale(-b,I));Mh=plus(A,scale(Q(-1,2),I))
u1=mv(Mb,w);u2=mv(Mh,u1);u3=mv(A,u2)
assert u3==kw
K=mm(mm(A,Mh),Mb);assert T(K)==K and mv(K,w)==kw
assert dot(w,w)==26 and dot(w,mv(F,w))==Q(14912,585)
assert dot(kw,kw)==Q(1800760572753083906132034496291,1019907849866242673982515970048000)
H=plus(A,scale(-c,mm(K,K)))
actual=dot(w,mv(plus(H,scale(-1,image)),w))
assert actual==26*t*(1+gap)
assert actual==Q(1,16)+t*Q(14912,585)-c*dot(kw,kw)
assert gap==Q(78605142319958855341529309,11432529876841442781954048000)>0
p=[Q(1)]
for r in (a,a,a-Q(1,2),a-Q(1,2),a-b,a-b):
    q=[Q(0)]*(len(p)+1)
    for i,x in enumerate(p):q[i]+=r*x;q[i+1]+=x
    p=q
p=[c*x for x in p];p[0]+=1-a;p[1]-=1
expected=list(map(Q,[0]))+[Q(19,17),Q(537952,23409),Q(2069504,23409),Q(288428032,1896129),Q(227540992,1896129),Q(67108864,1896129)]
assert p==expected and all(x>0 for x in p[1:])
result={'scope':'Exact Fraction diagnostics of actual Lean draft constants; not a proof or an eigenvalue oracle.',
 'definition_sha256':hashlib.sha256((P/'NLA/RA08/Definitions.lean').read_bytes()).hexdigest(),
 'checks':'PASS: original source block F; projection/Gram identities; exact positive LDL of A and compression bound; e6 eigenpair; three matvecs; all certificate equalities; shifted scalar polynomial coefficients.',
 't':str(t),'a':str(a),'b':str(b),'c':str(c),'w_norm_squared':str(dot(w,w)),
 'wFw':str(dot(w,mv(F,w))),'Kw_squared_norm':str(dot(kw,kw)),
 'matvec_stages':[[str(x) for x in u] for u in [u1,u2,u3]],
 'A_positive_LDL_pivots':list(map(str,Apivots)),
 'compression_bound_positive_LDL_pivots':list(map(str,compression_pivots)),
 'minorant_Rayleigh_value':str(actual),'relative_gap':str(gap),
 'one_minus_h_a_plus_z_coefficients':list(map(str,p)),
 'unproved_bridges':['ordered spectral data existence and semantics','actual spectral gap','scalar and genuine CFC order','actual fourth eigenvalue and all selected truncation tails','Euclidean operator norm contradiction','full universal negation']}
(Path(__file__).resolve().parent/'exact-checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(result['checks'])
print('Exact relative gap:',gap)
