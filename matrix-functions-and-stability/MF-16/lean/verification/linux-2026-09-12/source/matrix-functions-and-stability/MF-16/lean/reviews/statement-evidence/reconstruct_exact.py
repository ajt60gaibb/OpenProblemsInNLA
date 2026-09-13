"""MF-16 exact transcription checks on the ACTUAL Lean-emitted polynomial AST.

No theorem implementation: independent Fraction interval arithmetic and full
finite polynomial normal forms supplement the required later kernel proof.
Own interval AST implementation is in explore_certificate.py, which is imported
without running its exploratory search. Every matrix operation below is actual
finite polynomial matrix multiplication, not the proposed matrix recurrence.
"""
from pathlib import Path
from fractions import Fraction as Q
from math import comb
import hashlib,json,re
import explore_certificate as E
P=Path(__file__).resolve().parents[2];D=Path(__file__).resolve().parent
latest=json.loads((D/'latest.json').read_text());attempt=Path(latest['attempt'])
log=(attempt/'reviews-statement-evidence-Inspect.log').read_text()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def line(tag):return next(l[len(tag)+1:] for l in log.splitlines() if l.startswith(tag+'='))
def parse_tokens(s):
    stream=iter(s.split(','))
    def go():
        token=next(stream)
        if token.startswith('c:'):return ('c',Q(token[2:]))
        if token.startswith('v:'):return ('v',int(token[2:]))
        if token=='n':return ('n',go())
        assert token in ('a','m'),token
        return (token,go(),go())
    result=go()
    assert next(stream,None) is None
    return result
F=tuple(parse_tokens(s) for s in line('POLYNOMIAL_AST').split('|'))
assert F==E.system()
selected=json.loads((D/'selected-certificate.json').read_text())
center=list(map(Q,line('CENTER').split(',')))
flat=list(map(Q,line('BOX').split(',')));box=[E.Interval(*flat[i:i+2]) for i in range(0,6,2)]
flat=list(map(Q,line('PRECONDITIONER').split(',')));C=[flat[i:i+3] for i in range(0,9,3)]
radius=Q(selected['radius'])
assert center==list(map(Q,selected['center']))
assert C==[[Q(x) for x in row] for row in selected['preconditioner']]
assert [[str(b.lo),str(b.hi)] for b in box]==selected['box']
assert all(b.lo==center[i]-radius and b.hi==center[i]+radius for i,b in enumerate(box))
assert box[0].lo>3 and box[1].hi<0
check=E.check(F,center,radius,C)
assert check['pass'] and check['contraction']<Q(27,1000)
assert check['contraction']==Q(line('CONTRACTION_BOUND'))==Q(selected['contraction'])
assert check['center_displacement']<Q(4,10**11)
assert check['center_displacement']==Q(selected['center_displacement'])
assert check['margin']>radius/2 and check['margin']==Q(selected['margin'])
assert check['det_preconditioner']==Q(selected['det_preconditioner'])

# Exact multivariate polynomials in independent real coordinates x,y,z.
class Poly(dict):
    @staticmethod
    def C(n):return Poly({(0,0,0):Q(n)}) if n else Poly()
    @staticmethod
    def V(i):return Poly({tuple(int(j==i) for j in range(3)):Q(1)})
    def __add__(self,b):
        b=b if isinstance(b,Poly) else Poly.C(b);r=Poly(self)
        for m,c in b.items():r[m]=r.get(m,Q(0))+c
        return Poly({m:c for m,c in r.items() if c})
    __radd__=__add__
    def __neg__(self):return Poly({m:-c for m,c in self.items()})
    def __sub__(self,b):return self+(-b if isinstance(b,Poly) else -Q(b))
    def __rsub__(self,b):return Poly.C(b)-self
    def __mul__(self,b):
        b=b if isinstance(b,Poly) else Poly.C(b);r=Poly()
        for m,c in self.items():
            for n,d in b.items():
                k=tuple(m[i]+n[i] for i in range(3));r[k]=r.get(k,Q(0))+c*d
        return Poly({m:c for m,c in r.items() if c})
    __rmul__=__mul__
    def __pow__(self,k):
        assert k>=0;r=Poly.C(1)
        for _ in range(k):r=r*self
        return r

def evalp(e):
    if e[0]=='c':return Poly.C(e[1])
    if e[0]=='v':return Poly.V(e[1])
    a=evalp(e[1])
    if e[0]=='n':return -a
    b=evalp(e[2]);return a+b if e[0]=='a' else a*b

def normal(p):
    # Reduce only by the exact determinant relation xz=y²+3.
    r=Poly()
    for (a,b,c),coef in p.items():
        m=min(a,c)
        for j in range(m+1):
            key=(a-m,b+2*j,c-m)
            r[key]=r.get(key,Q(0))+coef*comb(m,j)*3**(m-j)
    return Poly({k:v for k,v in r.items() if v})
def mm(A,B):return [[sum((A[i][k]*B[k][j] for k in range(2)),Poly.C(0)) for j in range(2)] for i in range(2)]
def eye():return [[Poly.C(i==j) for j in range(2)] for i in range(2)]
def mpow(A,n):
    R=eye()
    for _ in range(n):R=mm(R,A)
    return R
def mdet(A):return A[0][0]*A[1][1]-A[0][1]*A[1][0]
def read_matrix(name):
    source=(P/'NLA/MF16/Definitions.lean').read_text()
    s=re.search(r'def '+name+r' : RealMatrix := !!\[([^\]]+)\]',source).group(1)
    return [[Q(c.strip()) for c in row.split(',')] for row in s.split(';')]
def lift(A):return [[Poly.C(c) for c in row] for row in A]
x,y,z=[Poly.V(i) for i in range(3)]
S=[[x,y],[y,z]];b=read_matrix('realB');p=read_matrix('realP');x0=read_matrix('realX0')
assert b==[[1,4],[4,17]] and p==[[4783113,6377496],[6377496,8503345]] and x0==[[3,0],[0,1]]
B=lift(b);Pmatrix=lift(p);X0=lift(x0)
word=['X','B']+['X']*12+['B','X']
assert word==word[::-1] and len(word)==16 and word.count('X')==14 and word.count('B')==2
def actual_word(X):
    R=eye()
    for letter in word:R=mm(R,X if letter=='X' else B)
    return R
assert actual_word(X0)==Pmatrix
assert mdet(B)==Poly.C(1) and mdet(X0)==Poly.C(3) and mdet(Pmatrix)==Poly.C(3**14)==Poly.C(4782969)
for A in [b,p,x0]:assert A[0][0]>0 and A[0][0]*A[1][1]-A[0][1]*A[1][0]>0 and A[0][1]==A[1][0]
s=x+z;t=s*s
u=s*(t*(t*(t*(t*(t-30)+324)-1512)+2835)-1458)
v=3*(t*(t*(t*(t*(t-27)+252)-945)+1215)-243)
assert evalp(F[1][1][1][1])==u
assert evalp(F[1][1][2][1][1])==v
S12=mpow(S,12)
assert all(not normal(S12[i][j]-(u*S[i][j]-v*int(i==j))) for i in range(2) for j in range(2))
actual=actual_word(S)
g=[evalp(e) for e in F]
assert g[0]==mdet(S)-3
assert not normal(g[1]-(actual[0][0]-4783113))
assert not normal(g[2]-(actual[0][1]-6377496))
assert actual[0][1]==actual[1][0]
assert mdet(actual)==mdet(S)**14 # det B=1; no assumed word recurrence.
assert not normal(mdet(actual)-3**14)
# Exact algebraic recovery of the last entry uses positive P11 and equal det.
assert p[0][0]!=0 and (Q(3**14)+p[0][1]**2)/p[0][0]==p[1][1]
result={'verdict':'PASS exact diagnostic; not a Lean proof','actual_Lean_AST_equals_independently_written_polynomial_system':True,
 'actual_Lean_AST_sha256':hashlib.sha256(line('POLYNOMIAL_AST').encode()).hexdigest(),
 'actual_Lean_center_box_preconditioner_match_selected_exact_data':True,
 'actual_Lean_contractionBound_equals_independent_Fraction_interval_AD':True,
 'rational_interval_certificate':E.json_value(check),
 'source_matrix_data':{'B':E.json_value(b),'P':E.json_value(p),'X0':E.json_value(x0),'detB':'1','detP':'4782969','detX0':'3'},
 'literal_word':word,'polynomial_matrix_checks':{'method':'Actual list-ordered polynomial matrix multiplication. Coefficient-normal-form reduction modulo x*z-y*y-3 for CH/entry implications; no matrix recurrence used to build actual powers.','S12_entries_term_counts':[[len(q) for q in row] for row in S12], 'word_entries_term_counts':[[len(q) for q in row] for row in actual],'all_four_CH_entries_reduced_to_zero':True,'both_actual_word_entry_bridges_reduced_to_zero':True,'actual_word_symmetry':True,'actual_word_det_equals_detS_pow14':True,'remaining_diagonal_recovered_from_nonzero_P11':True},
 'later_formal_obligations':'Actual complex PD, Expr semantic equivalence and Krawczyk soundness/root existence must still be proved in Lean after two independent statement approvals. Machine-evaluated true and symbolic Python identities are diagnostics only.',
 'input_sha256':{str(f.relative_to(P)):sha(f) for f in [P/'NLA/MF16/Definitions.lean',P/'Challenge.lean',P/'NUMERICAL_TARGETS.md',P/'SourceCorrespondence.md',D/'Inspect.lean',D/'explore_certificate.py',D/'selected-certificate.json',attempt/'reviews-statement-evidence-Inspect.log']}}
(D/'exact-reconstruction.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS actual Lean AST/data matched, exact interval contraction matched, all generic coefficient-level CH/word/determinant identities, source data and one-box margins verified. No theorem implemented.')
