"""Independent exact IE23 boundary diagnostics; no universal Lean proof claim."""
from pathlib import Path
from fractions import Fraction as Q
import hashlib,json,re
p=Path(__file__).resolve().parents[2]
s=(p/'NLA/IE23/Definitions.lean').read_text()
def read_matrix(name):
    body=re.search(r'^def '+name+r'[^\n]*:= (.+)$',s,re.M).group(1)
    raw=re.search(r'!!\[([^]]+)\]',body).group(1)
    assert re.fullmatch(r'[0-9,; \-]+',raw)
    scale=Q(1,3) if body.startswith('(1 / 3 : ℂ) • ') else Q(1)
    assert body.startswith('(1 / 3 : ℂ) • !![') or body.startswith('!![')
    return [[scale*Q(x.strip()) for x in row.split(',')] for row in raw.split(';')]
def tr(a):return list(map(list,zip(*a)))
def mul(a,b):return [[sum(x*y for x,y in zip(r,c)) for c in tr(b)] for r in a]
def add(a,b):return [[x+y for x,y in zip(r,t)] for r,t in zip(a,b)]
A,B,X,G,R=[read_matrix(n) for n in ['witnessA','witnessB','witnessX','witnessGram','witnessGramInv']]
I=[[Q(1),Q(0)],[Q(0),Q(1)]]
assert mul(A,tr(A))==G
assert mul(G,R)==I==mul(R,G)
assert mul(tr(A),R)==B
assert mul(A,B)==I==mul(A,X)
assert B!=X and mul(tr(B),B)==R and mul(tr(X),X)==I
assert add(R,[[Q(1,3)]*2 for _ in range(2)])==I
# The last two columns are the identity: exact full row rank, over C as well as R.
assert [[row[1],row[2]] for row in A]==I
z=[[Q(1)],[Q(-1)]]
assert mul(B,z)==mul(X,z)==[[Q(0)],[Q(1)],[Q(-1)]]
# Every complex solution of A*s=z is s=(t,1-t,-1-t).
# The actual complex affine quadratic identity follows from the Hermitian Gram
# of this real coefficient matrix, valid for arbitrary complex t.
U=[[Q(1),Q(0)],[Q(-1),Q(1)],[Q(-1),Q(-1)]]
assert mul(A,U)==[[Q(0),Q(1)],[Q(0),Q(-1)]]
assert mul(tr(U),U)==[[Q(3),Q(0)],[Q(0),Q(2)]]
def plus(a,b):
    d=dict(a)
    for k,v in b.items():d[k]=d.get(k,Q(0))+v
    return {k:v for k,v in d.items() if v}
def times(a,b):
    d={}
    for (i,j),v in a.items():
      for (k,l),w in b.items():d=plus(d,{(i+k,j+l):v*w})
    return d
ap={(2,0):Q(1),(0,2):Q(1)}
am={(2,0):Q(1),(0,2):Q(-1)}
assert plus(times(ap,ap),times(am,am))=={(4,0):Q(2),(0,4):Q(2)}
assert Q(1,2)-Q(1,4)==Q(1,4)
r={'status':'PASS exact transcription/algebra diagnostics; not the Lean proof',
   'source_sha256':hashlib.sha256(s.encode()).hexdigest(),
   'actual_Lean_matrices_parsed':['witnessA','witnessB','witnessX','witnessGram','witnessGramInv'],
   'rational_inverse_both_sides':True,'rank_minor_identity':True,
   'actual_pseudoinverse_formula':True,'distinct_right_inverses':True,
   'all_complex_action_Gram_identity':True,'norming_action_squared_norm':2,
   'all_complex_competitor_affine_Gram':[[3,0],[0,2]],
   'universal_quartic_SOS':True,
   'limitations':'Generic norm positivity, finite supremum, actual analytic norm/real-power bridges and global minimality remain universal Lean proof obligations. No finite test or source theorem is an axiom.'}
Path(__file__).with_name('independent-exact.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r,indent=2))
