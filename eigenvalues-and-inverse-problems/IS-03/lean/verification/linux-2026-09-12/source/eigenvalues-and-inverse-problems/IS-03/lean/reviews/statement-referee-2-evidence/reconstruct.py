"""Independent Fraction/polynomial diagnostic of actual frozen IS-03 Lean literals.

No numerical eigensolver, submitted diagnostic import, Lean theorem implementation,
or claim about all realizing matrices is used. The universal bridge remains a proof.
"""
from pathlib import Path
from fractions import Fraction as F
import ast, hashlib, json, re

out=Path(__file__).resolve().parent
project=out.parents[1]
source=project/'NLA/IS03/Definitions.lean'
text=source.read_text()

def trim(p):
    p=list(map(F,p))
    while len(p)>1 and p[-1]==0:p.pop()
    return tuple(p)
def add(p,q):return trim([(p[i] if i<len(p) else 0)+(q[i] if i<len(q) else 0) for i in range(max(len(p),len(q)))])
def scale(a,p):return trim([a*c for c in p])
def sub(p,q):return add(p,scale(-1,q))
def mul(p,q):
    r=[F(0)]*(len(p)+len(q)-1)
    for i,a in enumerate(p):
        for j,b in enumerate(q):r[i+j]+=a*b
    return trim(r)
def power(p,k):
    r=(F(1),)
    while k:
        if k&1:r=mul(r,p)
        p=mul(p,p);k//=2
    return r
zero=(F(0),);one=(F(1),);var=(F(0),F(1))
def parse_polynomial(expression):
    node=ast.parse('('+expression.strip().replace('^','**')+')',mode='eval').body
    def visit(n):
        if isinstance(n,ast.Constant) and type(n.value) is int:return (F(n.value),)
        if isinstance(n,ast.Name):assert n.id=='X';return var
        if isinstance(n,ast.Call):
            assert isinstance(n.func,ast.Name) and n.func.id=='C' and len(n.args)==1 and not n.keywords
            p=visit(n.args[0]);assert len(p)==1;return p
        if isinstance(n,ast.UnaryOp):
            assert isinstance(n.op,ast.USub);return scale(-1,visit(n.operand))
        assert isinstance(n,ast.BinOp)
        if isinstance(n.op,ast.Pow):
            assert isinstance(n.right,ast.Constant) and type(n.right.value) is int and n.right.value>=0
            return power(visit(n.left),n.right.value)
        a,b=visit(n.left),visit(n.right)
        if isinstance(n.op,ast.Add):return add(a,b)
        if isinstance(n.op,ast.Sub):return sub(a,b)
        if isinstance(n.op,ast.Mult):return mul(a,b)
        assert isinstance(n.op,ast.Div) and len(b)==1 and b[0]!=0
        return scale(1/b[0],a)
    return visit(node)
def definition_body(name):
    match=re.search(r'^def '+name+r'\b.*?:=\s*(.*?)(?=\n\n(?:/--|end))',text,re.M|re.S)
    assert match,name
    return match.group(1)
raw_matrix=re.search(r'^def witnessMatrix\b.*?:=\s*!!\[(.*?)\]',text,re.M|re.S).group(1)
A=[[F(v.strip()) for v in row.split(',')] for row in raw_matrix.split(';')]
assert len(A)==7 and all(len(row)==7 for row in A)
expected=[[F(0)]*7 for _ in range(7)]
expected[0][0]=F(1,2)
for offset,size in [(1,2),(3,4)]:
    for i in range(size):expected[offset+i][offset+(i+1)%size]=F(1)
assert A==expected and all(a>=0 for row in A for a in row)
p=parse_polynomial(definition_body('witnessPolynomial'))
q=parse_polynomial(definition_body('derivativePolynomial'))
moments_raw=re.search(r'^def traceMoments\b.*?:=\s*!\[(.*?)\]',text,re.M|re.S).group(1)
declared=[F(x.strip()) for x in moments_raw.split(',')];assert len(declared)==7

def characteristic(M):
    n=len(M)
    rows=[[sub(var,(M[i][j],)) if i==j else (-M[i][j],) for j in range(n)] for i in range(n)]
    total=zero;terms=[]
    def walk(perm,used,product):
        nonlocal total
        i=len(perm)
        if i==n:
            sign=(-1)**sum(perm[a]>perm[b] for a in range(n) for b in range(a+1,n))
            term=scale(sign,product);total=add(total,term);terms.append({'permutation':perm,'signed_coefficients':list(map(str,term))});return
        for j in range(n):
            if j not in used and rows[i][j]!=zero:walk(perm+[j],used|{j},mul(product,rows[i][j]))
    walk([],set(),one)
    return total,terms
actual_p,p_terms=characteristic(A)
assert actual_p==p
normalized=trim([F(i)*p[i]/7 for i in range(1,len(p))])
assert normalized==q and len(q)-1==6 and q[-1]==1
d=len(q)-1
coefficients=[q[d-j] for j in range(d+1)]
computed=[F(d)]
for k in range(1,8):
    if k<=d:
        value=-k*coefficients[k]-sum((coefficients[j]*computed[k-j] for j in range(1,k)),F(0))
    else:
        value=-sum((coefficients[j]*computed[k-j] for j in range(1,d+1)),F(0))
    computed.append(value)
assert computed[1:]==declared
assert declared[-1]==F(-8593,823543) and declared[-1]<0
terms=[3*computed[6],5*computed[5],-2*computed[4],3*computed[3],-computed[2],-computed[1]]
assert sum(terms,F(0))==7*computed[7]
common=[t*7**6 for t in terms]
assert common==list(map(F,[659298,182455,-659638,49392,-189679,-50421]))
assert sum(common)==-8593

def matrix_mul(M,N):
    n=len(M)
    return [[sum((M[i][k]*N[k][j] for k in range(n)),F(0)) for j in range(n)] for i in range(n)]
def identity(n):return [[F(i==j) for j in range(n)] for i in range(n)]
companion=[[F(0)]*d for _ in range(d)]
for i in range(1,d):companion[i][i-1]=F(1)
for i in range(d):companion[i][-1]=-q[i]
companion_q,companion_terms=characteristic(companion);assert companion_q==q
T=identity(d);companion_traces=[]
for k in range(1,8):
    T=matrix_mul(T,companion);companion_traces.append(sum((T[i][i] for i in range(d)),F(0)))
assert companion_traces==declared
T=identity(7);witness_traces=[]
for k in range(8):
    tr=sum((T[i][i] for i in range(7)),F(0))
    assert tr==F(1,2)**k+2*(k%2==0)+4*(k%4==0)
    assert all(t>=0 for row in T for t in row)
    witness_traces.append(tr);T=matrix_mul(T,A)
assert witness_traces[1]==F(1,2)
assert characteristic([])[0]==one and matrix_mul([],[])==[]

def divmod_poly(a,b):
    assert b!=zero
    a=trim(a);quotient=[F(0)]*max(1,len(a)-len(b)+1)
    while a!=zero and len(a)>=len(b):
        k=len(a)-len(b);c=a[-1]/b[-1];quotient[k]+=c
        a=sub(a,(F(0),)*k+scale(c,b))
    return trim(quotient),a
qprime=trim([i*q[i] for i in range(1,len(q))])
a,b=q,qprime;bez_a,bez_b=one,zero;bez_c,bez_d=zero,one
while b!=zero:
    quotient,remainder=divmod_poly(a,b)
    a,b=b,remainder;bez_a,bez_c=bez_c,sub(bez_a,mul(quotient,bez_c));bez_b,bez_d=bez_d,sub(bez_b,mul(quotient,bez_d))
assert len(a)==1 and a[0]!=0
bez_a=scale(1/a[0],bez_a);bez_b=scale(1/a[0],bez_b)
assert add(mul(bez_a,q),mul(bez_b,qprime))==one
quartic,remainder=divmod_poly(q,(-F(1),F(0),F(1)));assert remainder==zero

record={'result':'PASS','scope':'Independent exact diagnostic, not a universal Lean theorem or a certificate oracle.',
 'definitions_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'matrix_entries_from_actual_Lean':[[str(c) for c in row] for row in A],
 'agrees_with_source_1_plus_2_plus_4_blocks':True,'all_49_entries_nonnegative':True,'actual_witness_trace':'1/2',
 'determinant_coefficients_ascending':list(map(str,p)),'supported_witness_determinant_terms':p_terms,
 'normalized_derivative_coefficients_ascending':list(map(str,q)),'monic':True,'degree':6,
 'newton_traces_1_through_7':list(map(str,computed[1:])),'all_seven_match_actual_Lean_literals':True,
 'six_common_denominator_numerators':list(map(str,common)),'seventh_trace':str(declared[-1]),'negative':True,
 'independent_companion_matrix':[[str(c) for c in row] for row in companion],
 'supported_companion_determinant_terms':companion_terms,'companion_charpoly_equals_q':True,
 'actual_companion_power_traces':list(map(str,companion_traces)),
 'witness_power_traces_0_through_7':list(map(str,witness_traces)),
 'empty_matrix_determinant_one_and_trace_zero_diagnostic':True,
 'optional_separability_route_diagnostic_only':{'q_div_X_squared_minus_one':list(map(str,quartic)),
   'bezout_q_coefficients_ascending':list(map(str,bez_a)),'bezout_derivative_coefficients_ascending':list(map(str,bez_b)),
   'exact_bezout_identity_equals_one':True,'limitation':'This optional exact diagnostic could support a later proved separability bridge. It is not an added assumption or an implementation, and does not discharge the all-real-matrix trace contract.'},
 'warning':'Companion traces check one explicit real matrix. They do not prove the universal trace-moment contract; no diagonalizability/real-spectrum restriction may be assumed.'}
(out/'reconstruction.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'result':'PASS','witness_determinant_terms':len(p_terms),'companion_determinant_terms':len(companion_terms),
                  'actual_traces':list(map(str,computed[1:])),'q_coprime_with_derivative_diagnostic':True}))
