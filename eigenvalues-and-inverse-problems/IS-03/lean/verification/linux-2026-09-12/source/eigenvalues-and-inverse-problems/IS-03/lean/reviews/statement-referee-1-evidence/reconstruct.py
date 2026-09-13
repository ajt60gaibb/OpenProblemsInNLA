"""Independent IS03 statement referee exact diagnostics.

Uses only Fraction, sparse polynomial arithmetic and ordinary finite matrices.
No imports of the source submission's or statement author's checker.
This is a statement diagnostic, never a substitute for the arbitrary-B proof.
"""
from fractions import Fraction as F
from pathlib import Path
import hashlib, json, re, sys

PROJECT = Path(sys.argv[1]).resolve()
OUT = Path(__file__).resolve().parent
SOURCE = PROJECT.parents[2]/'eigenvalues-and-inverse-problems/IS-03/solution.md'
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
definitions = (PROJECT/'NLA/IS03/Definitions.lean').read_text()
source = SOURCE.read_text()

def between(text, start, end):
    return text.split(start,1)[1].split(end,1)[0]

def numbers(text):
    return [F(x.strip()) for x in text.split(',')]

matrix_literal = between(definitions,'def witnessMatrix : RealMatrix 7 :=','\n\n')
matrix_literal = matrix_literal.split('!![',1)[1].rsplit(']',1)[0]
A = [numbers(row) for row in matrix_literal.split(';')]
assert len(A)==7 and all(len(row)==7 for row in A)
assert all(x>=0 for row in A for x in row)
assert sum(A[i][i] for i in range(7))==F(1,2)
source_matrix = between(source,r'\begin{pmatrix}',r'\end{pmatrix}').replace(r'\frac12','1/2')
rows = [row.strip() for row in source_matrix.split('\\\\') if row.strip()]
source_A = [numbers(row.replace('&',',')) for row in rows]
assert source_A==A

# Polynomials are sparse maps from natural exponents to exact rationals.
def add(p,q):
    out=dict(p)
    for k,c in q.items(): out[k]=out.get(k,F(0))+c
    return {k:c for k,c in out.items() if c}
def scale(c,p): return {k:c*a for k,a in p.items() if c*a}
def mul(p,q):
    out={}
    for i,a in p.items():
        for j,b in q.items(): out[i+j]=out.get(i+j,F(0))+a*b
    return {k:c for k,c in out.items() if c}
def constant(c): return {0:F(c)} if c else {}
X={1:F(1)}

det_calls=0
def det(M):
    global det_calls
    det_calls+=1
    if not M:return constant(1)
    # Expand along a sparsest row to avoid all 7! permutations.
    r=min(range(len(M)),key=lambda i:sum(bool(x) for x in M[i]))
    result={}
    for c,entry in enumerate(M[r]):
        if entry:
            minor=[[entry2 for j,entry2 in enumerate(row) if j!=c]
                   for i,row in enumerate(M) if i!=r]
            result=add(result,scale((-1)**(r+c),mul(entry,det(minor))))
    return result

charmatrix=[[add(X if i==j else {},constant(-A[i][j])) for j in range(7)] for i in range(7)]
p=det(charmatrix)
factor_product=mul(mul(add(X,constant(F(-1,2))),{2:F(1),0:F(-1)}),{4:F(1),0:F(-1)})
assert p==factor_product
q={i-1:c*i/F(7) for i,c in p.items() if i}
q={i:c for i,c in q.items() if c}
assert q=={6:F(1),5:F(-3,7),4:F(-5,7),3:F(2,7),2:F(-3,7),1:F(1,7),0:F(1,7)}
assert max(q)==6 and q[6]==1

# Check every numeric coefficient from the actual Lean q expression as well.
lean_q=between(definitions,'def derivativePolynomial : ℝ[X] :=','\n\n')
assert 'X^6' in lean_q
explicit=[(sgn or '+',F(value),int(power) if power else 1)
          for sgn,value,power in re.findall(r'([+-]?)\s*C\s*\((\d+/\d+)\)\s*\*\s*X(?:\^(\d+))?',lean_q)]
q_from_lean={6:F(1)}
for sign,value,power in explicit:q_from_lean[power]=(-1 if sign=='-' else 1)*value
constant_match=re.search(r'\+\s*C\s*\((\d+/\d+)\)\s*$',lean_q.strip())
assert constant_match
q_from_lean[0]=F(constant_match.group(1))
assert q_from_lean==q

moments_literal=between(definitions,'def traceMoments : Fin 7 → ℝ :=','\n\n')
moments=numbers(moments_literal.split('![',1)[1].split(']',1)[0])
assert len(moments)==7
# Newton identities for monic q, without choosing or approximating any roots.
c=[F(1)]+[q.get(6-j,F(0)) for j in range(1,7)]
s=[F(6)]
for k in range(1,8):
    if k<=6:
        s.append(-sum(c[j]*s[k-j] for j in range(1,k))-k*c[k])
    else:
        s.append(-sum(c[j]*s[k-j] for j in range(1,7)))
assert s[1:]==moments
assert moments[-1]==F(-8593,823543)<0
recurrence_terms=[3*s[6],5*s[5],-2*s[4],3*s[3],-s[2],-s[1]]
assert sum(recurrence_terms)==7*s[7]
assert [x*7**6 for x in recurrence_terms]==[659298,182455,-659638,49392,-189679,-50421]

def identity(n):return [[F(int(i==j)) for j in range(n)] for i in range(n)]
def mmul(M,N):
    return [[sum(M[i][k]*N[k][j] for k in range(len(N)))
             for j in range(len(N[0]))] for i in range(len(M))]
def trace(M):return sum((M[i][i] for i in range(len(M))),F(0))
# A genuinely real companion matrix establishes diagnostic nonvacuity of the
# unrestricted hB : B.charpoly=q premise. It is not claimed nonnegative.
B=[[F(0) for j in range(6)] for i in range(6)]
for i in range(1,6):B[i][i-1]=F(1)
for i in range(6):B[i][5]=-q.get(i,F(0))
B_char=det([[add(X if i==j else {},constant(-B[i][j])) for j in range(6)] for i in range(6)])
assert B_char==q
power=identity(6);traces=[]
for k in range(1,8):
    power=mmul(power,B);traces.append(trace(power))
assert traces==moments
assert any(x<0 for row in B for x in row)
assert trace([])==0 and det([])=={0:F(1)}
# Generic zero-power semantics is the actual identity, not entrywise powers.
assert trace(identity(6))==6 and trace(identity(0))==0

jsonable=lambda x:({str(k):jsonable(v) for k,v in x.items()} if isinstance(x,dict)
    else [jsonable(v) for v in x] if isinstance(x,(list,tuple))
    else str(x) if isinstance(x,F) else x)
record={'status':'PASS','definitions_sha256':sha(PROJECT/'NLA/IS03/Definitions.lean'),
    'source_sha256':sha(SOURCE),'actual_source_matrix_matches_Lean':True,
    'matrix':A,'trace':F(1,2),'p':p,'q':q,'monic_degree':6,
    'moments':moments,'companion_matrix':B,'companion_charpoly':B_char,
    'companion_power_traces':traces,'seventh_recurrence_terms':recurrence_terms,
    'common_denominator':7**6,'numerator_sum':-8593,'denominator_final':7**7,
    'empty_dimension_boundary':{'trace':0,'charpoly':1},
    'zero_power_boundary':{'trace_identity6':6,'trace_identity0':0},
    'sparse_determinant_recursive_calls':det_calls,
    'scope':'Independent finite/source diagnostics only. All-real-B trace identities and generic nonnegative powers remain complete Lean theorem obligations.'}
(OUT/'reconstruction.json').write_text(json.dumps(jsonable(record),indent=2)+'\n')
print('PASS: actual 7x7 source matrix and determinant, formal normalized derivative, all seven Newton moments, genuine companion charpoly and powers, and n=0/k=0 boundaries.')
