"""Independent IV06 exact reconstruction, without importing supplied checkers.
Read the actual frozen Lean literals, compare the printed source table, and
compute the determinant by permutations in an integer polynomial ring.
Finite diagnostics supplement the full Lean algebra and topology proof.
"""
from pathlib import Path
from itertools import permutations,product,combinations
import ast,hashlib,json,re
OUT=Path(__file__).resolve().parent
P=OUT.parents[1]
REPO=P.parents[2]
text=(P/'NLA/IV06/Definitions.lean').read_text()

class Poly:
    def __init__(self,value):
        self.d=({(0,0,0):value} if value else {}) if isinstance(value,int) else {k:v for k,v in value.items() if v}
    def __add__(self,b):
        b=coerce(b);d=dict(self.d)
        for k,v in b.d.items():d[k]=d.get(k,0)+v
        return Poly(d)
    __radd__=__add__
    def __neg__(self):return Poly({k:-v for k,v in self.d.items()})
    def __sub__(self,b):return self+-coerce(b)
    def __rsub__(self,b):return coerce(b)+-self
    def __mul__(self,b):
        b=coerce(b);d={}
        for k,v in self.d.items():
            for l,w in b.d.items():
                h=tuple(x+y for x,y in zip(k,l));d[h]=d.get(h,0)+v*w
        return Poly(d)
    __rmul__=__mul__
    def __pow__(self,n):
        ans=Poly(1)
        for _ in range(n):ans=ans*self
        return ans
    def __eq__(self,b):return self.d==coerce(b).d
    def evaluate(self,values):
        total=0
        for exponents,coefficient in self.d.items():
            value=coefficient
            for x,k in zip(values,exponents):value=value*x**k
            total+=value
        return total
    def record(self):return {','.join(map(str,k)):v for k,v in sorted(self.d.items())}
def coerce(x):return x if isinstance(x,Poly) else Poly(x)
lam=Poly({(1,0,0):1});a=Poly({(0,1,0):1});b=Poly({(0,0,1):1})
row_literals=re.search(r'def family\b[\s\S]*?!!\[([^]]+)\]',text).group(1)
rows=[[x.strip() for x in row.split(',')] for row in row_literals.split(';')]
assert rows==[['25','a','b'],['1','-1','0'],['1','0','1']]
def family(x,y):
    return [[{'a':x,'b':y}[entry] if entry in {'a','b'} else int(entry) for entry in row] for row in rows]
def determinant(matrix):
    n=len(matrix);total=0
    for perm in permutations(range(n)):
        term=(-1)**sum(perm[i]>perm[j] for i in range(n) for j in range(i+1,n))
        for i,j in enumerate(perm):term=term*matrix[i][j]
        total+=term
    return total
def char(l,x,y):
    m=family(x,y)
    return determinant([[(l if i==j else 0)-m[i][j] for j in range(3)] for i in range(3)])
actual=char(lam,a,b)
expected=(lam-25)*(lam**2-1)-a*(lam-1)-b*(lam+1)
assert actual==expected
assert actual.evaluate([lam,a-91,b+84])==(lam-25)*(lam**2+6)-a*(lam-1)-b*(lam+1)
assert determinant([])==1

def table(name):
    s=re.search(r'\bdef '+name+r'\b[\s\S]*?:=\s*([\s\S]*?)(?=\n(?:def |/--|end ))',text).group(1)
    return ast.literal_eval(s.strip().replace('!',''))
values=table('includedValue');aa=table('includedA');bb=table('includedB')
vectors=table('includedVector');separators=table('separator')
lows=table('determinantLower');highs=table('determinantUpper')
source=REPO/'references/colbrook-intervals-2026-09-11/manuscripts/IV-06.tex'
source_rows=[list(map(int,row)) for row in re.findall(r'\n\s*(-?\d+)&(-?\d+)&(-?\d+)&(-?\d+)&(-?\d+)&(-?\d+)\\\\',source.read_text())]
assert len(source_rows)==4
assert source_rows==[[values[i],aa[i],bb[i],*vectors[i]] for i in range(4)]

witness=[]
for l,x,y,v in zip(values,aa,bb,vectors):
    assert -166<=x<=-16 and 9<=y<=159 and any(v)
    m=family(x,y);image=[sum(c*z for c,z in zip(row,v)) for row in m]
    assert image==[l*z for z in v] and char(l,x,y)==0
    witness.append({'lambda':l,'a':x,'b':y,'vector':v,'actual_product':image,'nonzero':True})
corner=[]
for l,lo,hi in zip(separators,lows,highs):
    polynomial=actual.evaluate([l,a,b]);c0=polynomial.evaluate([0,0,0])
    ca=polynomial.d.get((0,1,0),0);cb=polynomial.d.get((0,0,1),0)
    assert polynomial==c0+ca*a+cb*b
    entries=[{'a':x,'b':y,'determinant':char(l,x,y)} for x,y in product([-166,-16],[9,159])]
    assert min(x['determinant'] for x in entries)==lo
    assert max(x['determinant'] for x in entries)==hi
    # Exact nonnegative-distance expressions certify continuum extrema, with
    # no dependence between the two independent parameter intervals.
    low_expr=(ca*(a+166) if ca>=0 else (-ca)*(-16-a))+(cb*(b-9) if cb>=0 else (-cb)*(159-b))
    high_expr=(ca*(-16-a) if ca>=0 else (-ca)*(a+166))+(cb*(159-b) if cb>=0 else (-cb)*(b-9))
    assert polynomial-lo==low_expr and hi-polynomial==high_expr
    assert hi<=-18<0
    corner.append({'lambda':l,'affine_coefficients':[c0,ca,cb],'corner_values':entries,
     'exact_minimum':lo,'exact_maximum':hi,
     'lower_distance_polynomial':low_expr.record(),'upper_distance_polynomial':high_expr.record(),
     'distance_terms_have_nonnegative_coefficients_by_sign_selection':True})
pairs=[]
for i,j in combinations(range(4),2):
    ks=[k for k,s in enumerate(separators) if values[i]<s<values[j]]
    assert ks and values[i]<values[j]
    pairs.append({'indices':[i,j],'strictly_intervening_separator_indices':ks})
result={'status':'PASS','scope':'Independent exact transcription/algebra diagnostics and affine distance decomposition; not an alternative Lean topology or cardinal proof.',
 'definitions_sha256':hashlib.sha256((P/'NLA/IV06/Definitions.lean').read_bytes()).hexdigest(),
 'original_manuscript_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
 'polynomial_variable_order':['lambda','a','b'],'actual_determinant':actual.record(),
 'centered_source_identity':True,'empty_determinant':1,'witnesses':witness,
 'separator_bounds':corner,'all_six_pairwise_separations':pairs,
 'universal_reason':'The nonnegative distance decompositions use only the four independent box inequalities. Real interval containment in an actual connected component separates every pair; the Lean proof constructs the corresponding cardinal injection.'}
(OUT/'reconstruction.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS: source table, full determinant polynomial, four nonzero eigenpairs, twelve corners, exact affine distance bounds, six strict separations, empty determinant.')
