"""Independent PR127 audit from the manuscript's printed matrices.
No submitted module is imported or executed. Exact stdlib arithmetic only.
"""
from fractions import Fraction as F
import json
from pathlib import Path

H = [
 [1,-1,-3,-21,-41,-101,-325,63],
 [-1,3,1,17,71,291,1179,31],
 [-1,-1,13,-19,-56,-196,-752,16],
 [-1,-1,-3,189,-28,-98,-376,8],
 [-1,-1,-3,-51,581,-49,-188,4],
 [-1,-1,-3,-51,-213,1507,-94,2],
 [-1,-1,-3,-51,-213,-873,2589,1],
 [-1,1,-5,-55,-183,-683,-2683,1]]
D = [8,16,240,47640,472430,3644970,16148136,5272]
T = [
 [1,-1,-3,-21,-41,-101,-325,63],
 [0,2,-2,-4,30,190,854,94],
 [0,0,8,-44,-67,-107,-223,173],
 [0,0,0,120,-106,-116,-70,338],
 [0,0,0,0,397,-183,48,672],
 [0,0,0,0,0,1190,190,1342],
 [0,0,0,0,0,0,3063,2683],
 [0,0,0,0,0,0,0,5272]]
H0 = [
 [1,-5,-8,-12,-16,-16,0,64],
 [-1,13,-4,-6,-8,-8,0,32],
 [-1,-3,51,-3,-4,-4,0,16],
 [-1,-3,-11,169,-2,-2,0,8],
 [-1,-3,-11,-43,511,-1,0,4],
 [-1,-3,-11,-43,-171,1365,0,2],
 [-1,-3,-11,-43,-171,-683,1,1],
 [-1,-3,-11,-43,-171,-683,-1,1]]
D0 = [8,248,3286,36146,349184,2796544,2,5462]

def dot(a,b): return sum(x*y for x,y in zip(a,b))
def mm(A,B): return [[dot(row,col) for col in zip(*B)] for row in A]
def transpose(A): return list(map(list, zip(*A)))
def lower(changed):
    L=[[1 if i==j else -1 if i>j else 0 for j in range(8)] for i in range(8)]
    if changed: L[7][1]=0
    return L

def check(M,den,changed):
    L=lower(changed)
    assert mm(transpose(M),M)==[[den[i] if i==j else 0 for j in range(8)] for i in range(8)]
    # Independently regenerate positive Gram-Schmidt vectors from L itself.
    # Orthogonal non-normalized vectors must equal each printed column / a positive scalar.
    vecs=[]; scales=[]
    for j in range(8):
        v=[F(L[i][j]) for i in range(8)]
        for u in vecs:
            alpha=dot(v,u)/dot(u,u)
            v=[x-alpha*y for x,y in zip(v,u)]
        assert dot(v,v)>0
        ref=[row[j] for row in M]
        r=next(v[i]/ref[i] for i in range(8) if ref[i])
        assert r>0 and v==[r*x for x in ref]
        assert dot(v,v)==r*r*den[j]
        vecs.append(v); scales.append(r)
    # Solve L U=M with unit-lower forward substitution.
    U=[]
    for i in range(8):
        U.append([F(M[i][j])-sum(L[i][k]*U[k][j] for k in range(i)) for j in range(8)])
    assert all(U[i][j]==0 for i in range(8) for j in range(i))
    assert all(U[i][i]>0 for i in range(8))
    assert mm(L,U)==M
    # Direct successive Schur complements; do not assume the LU formula or pivot path.
    A=[list(map(F,row)) for row in M]
    stages=[];checked=0; multipliers=[]
    for k in range(8):
        m=len(A)
        pivot_magnitude=max(abs(row[0]) for row in A)
        ties=[i for i in range(m) if abs(A[i][0])==pivot_magnitude]
        assert min(ties)==0
        assert A[0][0]>0
        squared=[[A[i][j]**2/den[k+j] for j in range(m)] for i in range(m)]
        value=max(map(max,squared))
        locations=[(k+i+1,k+j+1) for i in range(m) for j in range(m) if squared[i][j]==value]
        # Cross check all active entries against independently reconstructed LU.
        for i in range(m):
            for j in range(m):
                assert A[i][j]==sum(L[k+i][t]*U[t][k+j] for t in range(k,8))
                checked+=1
        stages.append({'k':k+1,'max_squared':value,'locations':locations,'pivot_tie_rows':[k+i+1 for i in ties]})
        for i in range(1,m):
            ratio=A[i][0]/A[0][0]
            assert ratio==L[k+i][k]
            multipliers.append(ratio)
        A=[[A[i][j]-A[i][0]*A[0][j]/A[0][0] for j in range(1,m)] for i in range(1,m)]
    assert checked==204 and len(multipliers)==28
    return {'gram':'exact diagonal','positive_QR':'independently matches Gram-Schmidt',
            'gram_schmidt_column_scales':scales,'U':U,'stages':stages,
            'active_entries_verified':checked,'multipliers':multipliers,
            'growth_squared':max(s['max_squared'] for s in stages)/stages[0]['max_squared']}

w=check(H,D,True); q=check(H0,D0,False)
assert w['U']==T
assert [q['U'][i][i] for i in range(8)]==[1,8,31,106,341,1024,1,5462]
assert [s['max_squared'] for s in w['stages']]==[F(x*x,5272) for x in [63,94,173,338,672,1342,2683,5272]]
assert [s['locations'] for s in w['stages']]==[[(i,8)] for i in range(1,9)]
assert [s['max_squared'] for s in q['stages']]==[F(2601,3286)]+[F(x*x,5462) for x in [96,176,344,684,1366,2731,5462]]
assert w['growth_squared']==F(5272,63)**2
assert q['growth_squared']==F(17948132,2601)
gap=w['growth_squared']-q['growth_squared']
assert gap==F(117335164,1147041)>0
report={'head':'e5ad08c1a301d532ea200df8580224bb893b2240','verdict':'PASS','arithmetic':'integers and fractions.Fraction only','counterexample':w,'candidate':q,'positive_gap':gap}
Path('/private/tmp/nla-review-trace/pr127-exact-check.json').write_text(json.dumps(report,default=str,indent=2)+'\n')
print(json.dumps({'verdict':'PASS','active_entries_verified':408,'multipliers_verified':56,'positive_QR_verifications':2,'counterexample_growth':'5272/63','candidate_growth_squared':str(q['growth_squared']),'positive_squared_gap':str(gap)},indent=2))
