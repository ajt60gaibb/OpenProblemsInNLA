from fractions import Fraction as Q
from math import ceil, log2

def tr(A): return list(map(list, zip(*A)))
def mm(A,B): return [[sum(x*y for x,y in zip(a,b)) for b in tr(B)] for a in A]
def inv(A):
    n=len(A); a=[[Q(v) for v in row]+[Q(i==j) for j in range(n)] for i,row in enumerate(A)]
    for k in range(n):
        p=next(i for i in range(k,n) if a[i][k]); a[k],a[p]=a[p],a[k]
        pivot=a[k][k]; a[k]=[x/pivot for x in a[k]]
        for i in range(n):
            if i!=k:
                t=a[i][k]; a[i]=[x-t*y for x,y in zip(a[i],a[k])]
    return [row[n:] for row in a]
def diag(x): return [[v if i==j else 0 for j in range(len(x))] for i,v in enumerate(x)]
def contract(slices,g): return [[sum(g[j]*slices[j][a][b] for j in range(len(g))) for b in range(len(slices[0]))] for a in range(len(slices[0]))]
A=[[1,2],[3,5],[7,11]]; B=[[2,1],[1,3],[4,7]]; C=[[1,1],[0,2],[3,-1]]
U=[[1,0],[0,1],[1,1]]; V=[[1,0],[0,1],[0,0]]; g=[1,1,0]; h=[0,1,1]
slices=[mm(mm(A,diag(c)),tr(B)) for c in C]
S=[mm(mm(tr(U),t),V) for t in slices]
M0=contract(S,g); M1=contract(S,h)
PA=mm(M1,inv(M0)); PB=mm(tr(M1),inv(tr(M0)))
p=[[1,2]]; q=[[2,3]]
KA=p+mm(p,PA); KB=q+mm(q,PB)
H=[mm(mm(KA,s),tr(KB)) for s in S]
assert all(t[0][1]==t[1][0] for t in H)
Vz=[[1,1,1],[0,1,2]]; W=[[1,1,1],[0,1,2],[0,1,4]]
F=[[t[0][0] for t in H],[t[0][1] for t in H],[t[1][1] for t in H]]
Z=tr(mm(inv(W),F))
LA=mm(mm(contract(slices,g),V),inv(M0)); LB=mm(mm(tr(contract(slices,g)),U),inv(tr(M0)))
X=mm(mm(LA,inv(KA)),Vz); Y=mm(mm(LB,inv(KB)),Vz)
assert [mm(mm(X,diag(z)),tr(Y)) for z in Z]==slices
print('PASS: independently implemented rational sketch/Krylov/interpolation/lifting example (n=3,r=2).')
for r in range(2,129):
    ell=1+2*(r-1).bit_length()
    assert ell<=2*r
    tau=Q(1,64*ell); d=2*tau+tau*tau
    assert d<Q(1,4) and (ell*d/(1-d))**2*(1+d)/(1-d)<Q(1,64)
    assert 32*r+4*r**4/tau**2<=65568*r**6
    for i in range(r):
        for j in range(r):
            if i!=j: assert any(((i>>b)&1)!=((j>>b)&1) for b in range((r-1).bit_length()))
print('PASS: binary pair coverage and exact derivative/smoothing constant inequalities for r=2,...,128.')
for t in [Q(1,7),Q(1,37),Q(1,271)]:
    c=(1-t*t)/(1+t*t); s=2*t/(1+t*t); delta=s*s/(c*c)
    a=[[1,1,0],[0,delta,1],[0,0,0]]
    rot=[[c,0,-s],[0,1,0],[s,0,c]]
    updated=mm(a,[[v*v for v in row] for row in rot])
    assert all(row[0]==c*c*row[1] for row in updated)
    # The cancellation is x1 ⊗ e2 ⊗ q1 - c² x2 ⊗ e2 ⊗ q1.
print('PASS: three independent exact shrinking-neighborhood parameter choices.')
