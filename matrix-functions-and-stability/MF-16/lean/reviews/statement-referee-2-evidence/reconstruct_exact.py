"""Independent root statement diagnostics. No author checker imports or proof oracle."""
from pathlib import Path
from fractions import Fraction as Q
from math import comb
import hashlib, json, re

E=Path(__file__).resolve().parent
text=(E/'Inspect.log').read_text()
observed={line.split('=',1)[0][5:]:json.loads(line.split('=',1)[1]) for line in text.splitlines() if line.startswith('ROOT_')}

class Interval:
    def __init__(self,lo,hi=None): self.lo=Q(lo);self.hi=Q(lo if hi is None else hi);assert self.lo<=self.hi
    @staticmethod
    def cast(x):return x if isinstance(x,Interval) else Interval(x)
    def __add__(self,b):
        b=self.cast(b);return Interval(self.lo+b.lo,self.hi+b.hi)
    __radd__=__add__
    def __neg__(self):return Interval(-self.hi,-self.lo)
    def __sub__(self,b):return self+-self.cast(b)
    def __rsub__(self,b):return self.cast(b)+-self
    def __mul__(self,b):
        b=self.cast(b);v=[self.lo*b.lo,self.lo*b.hi,self.hi*b.lo,self.hi*b.hi];return Interval(min(v),max(v))
    __rmul__=__mul__
    def __eq__(self,b):return isinstance(b,Interval) and (self.lo,self.hi)==(b.lo,b.hi)
    def data(self):return [str(self.lo),str(self.hi)]

class Dual:
    def __init__(self,v,d):self.v=v;self.d=d
    @staticmethod
    def c(x):return Dual(Interval(x),[Interval(0) for _ in range(3)])
    def __add__(self,b):return Dual(self.v+b.v,[a+c for a,c in zip(self.d,b.d)])
    def __neg__(self):return Dual(-self.v,[-a for a in self.d])
    def __mul__(self,b):return Dual(self.v*b.v,[a*b.v+self.v*c for a,c in zip(self.d,b.d)])

def eval_ast(e,variables,constant):
    tag=e[0]
    if tag=='constant':return constant(Q(e[1]))
    if tag=='variable':assert e[1] in range(3);return variables[e[1]]
    if tag=='negate':return -eval_ast(e[1],variables,constant)
    a,b=(eval_ast(x,variables,constant) for x in e[1:])
    if tag=='add':return a+b
    assert tag=='multiply',tag
    return a*b

center=list(map(Q,observed['CENTER']))
box=[Interval(*v) for v in observed['BOX']]
C=[list(map(Q,row)) for row in observed['C']]
assert center==[Q(17471725533,5000000000),Q(-51638297,156250000),Q(2224465749,2500000000)]
assert C==[[Q(17591641083,500000000),Q(20183,10000000000),Q(-17029,10000000000)],
           [Q(-11575092327,500000000),Q(-2477,2000000000),Q(10667,10000000000)],
           [Q(-21469001731,5000000000),Q(-2797,10000000000),Q(2319,10000000000)]]
radius=Q(1,10000000)
assert all(i.lo==m-radius and i.hi==m+radius for i,m in zip(box,center))
variables=[Dual(box[i],[Interval(int(i==j)) for j in range(3)]) for i in range(3)]
J=[eval_ast(e,variables,Dual.c).d for e in observed['AST']]
assert J==[[Interval(*v) for v in row] for row in observed['J']]
IJ=[[Interval(int(i==j))-sum((C[i][k]*J[k][j] for k in range(3)),Interval(0)) for j in range(3)] for i in range(3)]
q=max(sum(max(abs(v.lo),abs(v.hi)) for v in row) for row in IJ)
assert q==Q(observed['Q']) and 0<=q<Q(27,1000)
values=[eval_ast(e,center,Q) for e in observed['AST']]
shift=[sum(C[i][j]*values[j] for j in range(3)) for i in range(3)]
image=[Interval(m-s-q*radius,m-s+q*radius) for m,s in zip(center,shift)]
assert image==[Interval(*i) for i in observed['IMAGE']]
assert all(X.lo<I.lo and I.hi<X.hi for X,I in zip(box,image))
margin=min(min(I.lo-X.lo,X.hi-I.hi) for X,I in zip(box,image))
assert margin>radius/2 and max(map(abs,shift))<Q(4,10**11)
detC=C[0][0]*(C[1][1]*C[2][2]-C[1][2]*C[2][1])-C[0][1]*(C[1][0]*C[2][2]-C[1][2]*C[2][0])+C[0][2]*(C[1][0]*C[2][1]-C[1][1]*C[2][0])
assert detC==Q(790668616748253,62500000000000000000000000000)==Q(observed['DET'])
assert observed['CHECK'] is True and Q(observed['RADIUS'])==radius and box[0].lo>3

class Poly:
    def __init__(self,data=0):
        self.data={k:Q(v) for k,v in data.items() if v} if isinstance(data,dict) else ({(0,0,0):Q(data)} if data else {})
    @staticmethod
    def cast(x):return x if isinstance(x,Poly) else Poly(x)
    def __add__(self,b):
        d=self.data.copy()
        for k,v in self.cast(b).data.items():d[k]=d.get(k,0)+v
        return Poly(d)
    __radd__=__add__
    def __neg__(self):return Poly({k:-v for k,v in self.data.items()})
    def __sub__(self,b):return self+-self.cast(b)
    def __rsub__(self,b):return self.cast(b)+-self
    def __mul__(self,b):
        d={}
        for a,x in self.data.items():
            for c,y in self.cast(b).data.items():
                k=tuple(u+v for u,v in zip(a,c));d[k]=d.get(k,0)+x*y
        return Poly(d)
    __rmul__=__mul__
    def __pow__(self,n):
        result=Poly(1)
        for _ in range(n):result=result*self
        return result
    def __eq__(self,b):return self.data==self.cast(b).data
    def remainder(self):
        result=Poly()
        for (a,b,c),v in self.data.items():
            k=min(a,c)
            result+=Poly({(a-k,b+2*j,c-k):v*comb(k,j)*3**(k-j) for j in range(k+1)})
        return result
    def at(self,v):return sum(c*v[0]**a*v[1]**b*v[2]**d for (a,b,d),c in self.data.items())

x,y,z=[Poly({tuple(int(i==j) for i in range(3)):1}) for j in range(3)]
S=[[x,y],[y,z]];B=[[Poly(1),Poly(4)],[Poly(4),Poly(17)]]
I=[[Poly(1),Poly(0)],[Poly(0),Poly(1)]]
def mul(A,B):return [[sum(A[i][k]*B[k][j] for k in range(2)) for j in range(2)] for i in range(2)]
def power(A,n):
    result=I
    for _ in range(n):result=mul(result,A)
    return result
def det(A):return A[0][0]*A[1][1]-A[0][1]*A[1][0]
s=x+z;t=s*s
u=s*(t*(t*(t*(t*(t-30)+324)-1512)+2835)-1458)
v=3*(t*(t*(t*(t*(t-27)+252)-945)+1215)-243)
us=[Poly(0),Poly(1)]
for i in range(1,12):us.append(s*us[-1]-3*us[-2])
assert u==us[12] and v==3*us[11]
S12=power(S,12)
assert all((S12[i][j]-u*S[i][j]+v*I[i][j]).remainder()==0 for i in range(2) for j in range(2))
word=mul(mul(mul(mul(S,B),S12),B),S)
wordPoly=mul(mul(mul(mul(S,B),[[u*S[i][j]-v*I[i][j] for j in range(2)] for i in range(2)]),B),S)
system=[eval_ast(e,[x,y,z],Poly) for e in observed['AST']]
assert system[0]==det(S)-3
assert system[1]==wordPoly[0][0]-4783113
assert system[2]==wordPoly[0][1]-6377496
assert (system[1]-(word[0][0]-4783113)).remainder()==0
assert (system[2]-(word[0][1]-6377496)).remainder()==0
assert word[0][1]==word[1][0]
assert det(word)==det(S)**14
P=[[4783113,6377496],[6377496,8503345]]
assert [[entry.at([3,0,1]) for entry in row] for row in word]==P
assert det(P)==3**14 and P[0][0]>0
assert 1*17-4*4==1 and 3*1==3
# Once both known entries and determinants agree, the missing entry is forced.
assert Q(3**14+P[0][1]**2,P[0][0])==P[1][1]
reports=re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",text)
allowed={'propext','Classical.choice','Quot.sound'}
assert len(reports)==11
for name,items in reports:
    axioms=set(i.strip() for i in items.split(',') if i.strip())
    if name.endswith('not_wordUniquenessConjecture'):assert axioms==allowed|{'sorryAx'}
    else:assert axioms<=allowed,(name,axioms)
assert (E/'Challenge.log').read_text().count('declaration uses `sorry`')==9
assert not (E/'Definitions.log').read_text()
assert 'warning:' not in text and 'error:' not in text
result={'verdict':'PASS: independent statement diagnostics only; no Lean proof certificate',
 'actual_inspector_sha256':hashlib.sha256((E/'Inspect.log').read_bytes()).hexdigest(),
 'actual_ast_and_all_three_variable_rational_data_consumed':True,
 'exact_full_interval_J_and_newton_enclosure_equal_Lean':True,
 'q':str(q),'q_approx':float(q),'detC':str(detC),'radius':str(radius),
 'maximum_center_displacement':str(max(map(abs,shift))),'strict_selfmap_margin':str(margin),
 'generic_polynomial_checks':['CH12 recurrence coefficients','all4 actual matrix-power CH entries modulo det(S)-3','actual AST matches reduced word first2entries','actual word first2entries modulo determinant equation','actual word symmetric','actual word determinant equals det(S)^14','source P and determinant/leadingminor','remaining diagonal entry recovery'],
 'library_and_definition_trust_reports':10,'deliberate_Challenge_admissions':9,
 'no_candidate_source_change':True}
(E/'exact-checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in {'q','maximum_center_displacement','strict_selfmap_margin'}},indent=2))
