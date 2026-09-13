"""Independent exact diagnostic parsed from the frozen IV-06 Lean data.
No supplied checker, floating eigensolver, symbolic package, or target proof is used.
"""
from pathlib import Path
import ast, hashlib, itertools, json, re

out = Path(__file__).resolve().parent
project = out.parents[1]
source = project / 'NLA/IV06/Definitions.lean'
text = source.read_text()
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(source) == '283a31f8e9d100347e5403b8e5688feebd13968d865d487b4962eaa1f861b195'

# Sparse integer polynomials in a, b, lambda; coefficient equality is exhaustive.
zero = {}
one = {(0,0,0): 1}
def const(n):
    return {(0,0,0): n} if n else {}
def add(p,q):
    r = p.copy()
    for e,c in q.items():
        r[e] = r.get(e,0) + c
        if not r[e]: del r[e]
    return r
def scale(c,p): return {e:c*v for e,v in p.items() if c*v}
def sub(p,q): return add(p,scale(-1,q))
def mul(p,q):
    r = {}
    for e,c in p.items():
        for f,d in q.items():
            g = tuple(i+j for i,j in zip(e,f))
            r[g] = r.get(g,0) + c*d
    return {e:c for e,c in r.items() if c}
def det(matrix):
    result = {}
    for perm in itertools.permutations(range(len(matrix))):
        inv = sum(perm[i]>perm[j] for i in range(len(perm)) for j in range(i+1,len(perm)))
        term = const((-1)**inv)
        for i,j in enumerate(perm): term = mul(term,matrix[i][j])
        result = add(result,term)
    return result
def evaluate(poly,a,b,lam):
    return sum(c*a**e[0]*b**e[1]*lam**e[2] for e,c in poly.items())
def table(name):
    raw = re.search(r'^def '+name+r'\b[^\n]*:=\s*(.*?)(?=\n\n|\nend)',text,re.M|re.S).group(1)
    return ast.literal_eval(raw.replace('!',''))

a,b,t = {(1,0,0):1}, {(0,1,0):1}, {(0,0,1):1}
raw = re.search(r'^def family\b[^\n]*:=\s*!!\[(.*?)\]',text,re.M|re.S).group(1)
tokens = [[s.strip() for s in row.split(',')] for row in raw.split(';')]
assert len(tokens)==3 and all(len(row)==3 for row in tokens)
def token_poly(v): return a if v=='a' else b if v=='b' else const(int(v))
family = [[token_poly(v) for v in row] for row in tokens]
char_matrix = [[sub(t if i==j else zero,family[i][j]) for j in range(3)] for i in range(3)]
actual = det(char_matrix)
expected = sub(sub(mul(sub(t,const(25)),sub(mul(t,t),one)),mul(a,sub(t,one))),mul(b,add(t,one)))
assert actual == expected
assert det([]) == one

def bound(name):
    match = re.search(r'^def '+name+r'\b[^\n]*:=\s*family\s+\(?(-?\d+)\)?\s+\(?(-?\d+)\)?',text,re.M)
    assert match
    return tuple(map(int,match.groups()))
low,high = bound('lower'),bound('upper')
lower = [[evaluate(p,*low,0) for p in row] for row in family]
upper = [[evaluate(p,*high,0) for p in row] for row in family]
varying = [(i,j) for i in range(3) for j in range(3) if lower[i][j]!=upper[i][j]]
assert varying == [(0,1),(0,2)]
assert all(lower[i][j]<=upper[i][j] for i in range(3) for j in range(3))

lambdas,as_,bs_,vectors = [table(n) for n in ['includedValue','includedA','includedB','includedVector']]
eigenpairs = []
for i,(lam,aa,bb,v) in enumerate(zip(lambdas,as_,bs_,vectors)):
    assert low[0]<=aa<=high[0] and low[1]<=bb<=high[1]
    assert len(v)==3 and any(v)
    matrix = [[evaluate(p,aa,bb,0) for p in row] for row in family]
    product = [sum(x*y for x,y in zip(row,v)) for row in matrix]
    assert product == [lam*y for y in v]
    assert evaluate(actual,aa,bb,lam)==0
    eigenpairs.append({'i':i,'lambda':lam,'a':aa,'b':bb,'vector':v,'actual_matrix_product':product,'nonzero_vector':True})
assert len(eigenpairs)==4

separators,lower_targets,upper_targets = [table(n) for n in ['separator','determinantLower','determinantUpper']]
estimates = []
for lam,lo,hi in zip(separators,lower_targets,upper_targets):
    affine = {}
    for (ea,eb,et),c in actual.items():
        affine[(ea,eb)] = affine.get((ea,eb),0) + c*lam**et
    affine = {e:c for e,c in affine.items() if c}
    assert set(affine) <= {(0,0),(1,0),(0,1)}
    center,ca,cb = [affine.get(e,0) for e in [(0,0),(1,0),(0,1)]]
    minimum = center+min(ca*low[0],ca*high[0])+min(cb*low[1],cb*high[1])
    maximum = center+max(ca*low[0],ca*high[0])+max(cb*low[1],cb*high[1])
    corners = [{'a':aa,'b':bb,'determinant':evaluate(actual,aa,bb,lam)} for aa in (low[0],high[0]) for bb in (low[1],high[1])]
    assert minimum==lo==min(row['determinant'] for row in corners)
    assert maximum==hi==max(row['determinant'] for row in corners)
    assert hi<=-18<0
    estimates.append({'lambda':lam,'affine_coefficients_constant_a_b':[center,ca,cb],'bounds':[lo,hi],'four_corners':corners,'upper_margin_at_most_minus_18':True})
assert len(estimates)==3

pairs=[]
for i,j in itertools.combinations(range(4),2):
    between = [z for z in separators if lambdas[i]<z<lambdas[j]]
    assert between
    pairs.append({'indices':[i,j],'included_values':[lambdas[i],lambdas[j]],'excluded_separators_between':between})
assert len(pairs)==6
result = {'result':'PASS','scope':'Exact statement diagnostics only; universal real bounds, eigenvector bridge, topology and cardinal injection remain unproved Lean obligations', 'definitions_sha256':sha(source),'parsed_family_entries':tokens,'all_polynomial_coefficients':[{'a_degree':e[0],'b_degree':e[1],'lambda_degree':e[2],'coefficient':c} for e,c in sorted(actual.items())], 'lower_matrix':lower,'upper_matrix':upper,'two_independent_variable_entries':varying,'fixed_entry_count':7,'empty_determinant':1,'four_eigenpairs':eigenpairs,'three_affine_separator_bounds':estimates,'six_pairwise_separations':pairs,'planned_scalar_certificate':{'expression':'(-18 : Real) < 0','truth':True,'domain':'one exact singleton; no subdivision','Lean_proof_exists':False}}
(out/'reconstruction.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS: actual frozen matrix, all determinant coefficients, four nonzero eigenpairs, three affine bounds/twelve corners, six pair separations')
