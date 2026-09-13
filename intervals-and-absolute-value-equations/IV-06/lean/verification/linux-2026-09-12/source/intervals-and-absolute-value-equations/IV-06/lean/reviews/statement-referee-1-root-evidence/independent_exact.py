"""Independent IV06 exact coefficient/witness diagnostics; not Lean proof."""
from pathlib import Path
from fractions import Fraction as Q
from itertools import permutations,product,combinations
import re,json,hashlib
root=Path(__file__).resolve().parents[2]
s=(root/'NLA/IV06/Definitions.lean').read_text()
def vec(name):
 raw=re.search(r'^def '+name+r'[^\n]*:= !\[([^]]+)\]',s,re.M).group(1)
 assert re.fullmatch(r'[-0-9, ]+',raw)
 return [Q(x.strip()) for x in raw.split(',')]
values,aa,bb,seps,lo,hi=[vec(n) for n in ['includedValue','includedA','includedB','separator','determinantLower','determinantUpper']]
vr=s.split('def includedVector',1)[1].split('def separator',1)[0]
vectors=[[Q(x.strip()) for x in row.split(',')] for row in re.findall(r'!\[([-0-9, ]+)\]',vr)]
assert len(vectors)==4 and all(len(v)==3 for v in vectors)
raw=re.search(r'def family[\s\S]*?:=\s*!!\[([^]]+)\]',s).group(1)
cells=[[x.strip() for x in row.split(',')] for row in raw.split(';')]
assert cells==[['25','a','b'],['1','-1','0'],['1','0','1']]
def family(a,b):return [[a if x=='a' else b if x=='b' else Q(x) for x in row] for row in cells]
assert 'def lower : RealMatrix 3 := family (-166) 9' in s
assert 'def upper : RealMatrix 3 := family (-16) 159' in s
for l,a,b,v in zip(values,aa,bb,vectors):
 assert -166<=a<=-16 and 9<=b<=159 and any(v)
 assert [sum(x*y for x,y in zip(row,v)) for row in family(a,b)]==[l*x for x in v]
def add(a,b):
 d=dict(a)
 for k,v in b.items():d[k]=d.get(k,Q(0))+v
 return {k:v for k,v in d.items() if v}
def neg(a):return {k:-v for k,v in a.items()}
def mul(a,b):
 d={}
 for i,v in a.items():
  for j,w in b.items():d=add(d,{tuple(x+y for x,y in zip(i,j)):v*w})
 return d
def const(x):return {(0,0,0):Q(x)} if x else {}
z,a,b=[{k:Q(1)} for k in [(1,0,0),(0,1,0),(0,0,1)]]
F=[[a if x=='a' else b if x=='b' else const(Q(x)) for x in row] for row in cells]
M=[[add(z if i==j else {},neg(F[i][j])) for j in range(3)] for i in range(3)]
det={}
for perm in permutations(range(3)):
 sign=(-1)**sum(perm[i]>perm[j] for i in range(3) for j in range(i+1,3))
 t=const(sign)
 for i,j in enumerate(perm):t=mul(t,M[i][j])
 det=add(det,t)
expected=add(add(mul(add(z,const(-25)),add(mul(z,z),const(-1))),neg(mul(a,add(z,const(-1))))),neg(mul(b,add(z,const(1)))))
assert det==expected
corners=[]
for z0,L,U in zip(seps,lo,hi):
 outcomes=[(z0-25)*(z0*z0-1)-a0*(z0-1)-b0*(z0+1) for a0,b0 in product([-166,-16],[9,159])]
 assert min(outcomes)==L and max(outcomes)==U and U<=-18<0
 corners.append([int(x) for x in outcomes])
for x,y in combinations(values,2):assert any(x<t<y for t in seps)
record={'status':'PASS exact diagnostics; universal Lean proof remains pending',
 'definitions_sha256':hashlib.sha256(s.encode()).hexdigest(),
 'actual_Lean_data_parsed':True,'coefficient_identity':True,'nonzero_eigenpairs':4,
 'separator_corner_checks':12,'exact_separator_corner_values':corners,
 'all_distinct_pairs_separated':6,'maximum_determinant_upper_bound':-18,
 'zero_dimension_semantics':'No nonzero empty vector; empty determinant1; iff false/false',
 'remaining_Lean_obligations':'Generic determinant/eigenvector and connected-component bridges, exact full-box inequalities, actual cardinal injection and full negation; finite diagnostics are no premise.'}
Path(__file__).with_name('independent-exact.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2))
