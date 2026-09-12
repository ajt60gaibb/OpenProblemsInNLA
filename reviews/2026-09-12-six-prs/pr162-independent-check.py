"""New review diagnostics; exact finite examples only, no imported submission code."""
from fractions import Fraction as F
from itertools import product
from collections import defaultdict
from math import comb

atoms = [(1,1,0), (1,-1,0), (0,1,-1), (-1,0,1)]
weights = [F(3,7),F(2,7),F(1,7),F(1,7)]
k,s = 3,2
p = [sum(q for w,q in zip(atoms,weights) if w[i]) for i in range(k)]
sigma = [[sum(q*w[i]*w[j] for w,q in zip(atoms,weights)) for j in range(k)] for i in range(k)]
t = [[sigma[i][j]/p[j] for j in range(k)] for i in range(k)]

def mv(a,v): return tuple(sum(x*y for x,y in zip(row,v)) for row in a)
def mm(a,b): return [list(mv(list(zip(*b)),row)) for row in a]
def norm2(v): return sum(x*x for x in v)
def power(a,j):
    out = [[F(i==h) for h in range(k)] for i in range(k)]
    for _ in range(j): out=mm(out,a)
    return out

# Conditional signed-state probabilities, with first-hit laws enumerated directly.
def kernel(v,actual=False):
    out=defaultdict(F)
    for i in range(k):
        if not v[i]: continue
        if not actual:
            for w,q in zip(atoms,weights):
                if w[i]: out[tuple(v[i]*w[i]*x for x in w)] += q/p[i]/s
        else:
            for indices in product(range(len(atoms)),repeat=2):
                q=F(1,s)
                for ind in indices:q*=weights[ind]
                accepted=next((atoms[ind] for ind in indices if atoms[ind][i]),None)
                if accepted is not None:
                    out[tuple(v[i]*accepted[i]*x for x in accepted)]+=q
    return out

states=set(atoms+ [tuple(-x for x in v) for v in atoms])
for v in states:
    law=kernel(v)
    assert sum(law.values())==1
    assert tuple(sum(q*w[i] for w,q in law.items()) for i in range(k))==tuple(x/s for x in mv(t,v))

# Verify the full noncommuting trace identity exactly, avoiding square roots of D.
bmat=[[F(i==j)-t[i][j]/s for j in range(k)] for i in range(k)]
for length in range(1,10):
    bl=power(bmat,length)
    direct=sum(q*norm2(mv(bl,v)) for v,q in zip(atoms,weights))
    covariance=mm(mm(bl,sigma),list(zip(*bl)))
    assert direct==sum(covariance[i][i] for i in range(k))
    assert direct<=F(s*s,2*length+1)

# Keep full length-two histories: domination is needed for a reconstruction,
# not just for the terminal-state marginal.
minimum_hit=min(1-(1-pi)**2 for pi in p)
histories=0
conditioning_changes=False
for u in atoms:
    ideal={}; actual={}
    for v,q in kernel(u).items():
        for w,z in kernel(v).items():ideal[v,w]=q*z
    for v,q in kernel(u,True).items():
        for w,z in kernel(v,True).items():actual[v,w]=q*z
    total=sum(actual.values())
    for history,q in ideal.items():
        assert actual.get(history,0)>=minimum_hit**2*q
        conditioning_changes |= actual.get(history,0)/total != q
        histories+=1
    # Exact full variance identity for two trajectories sharing their center.
    y=[(tuple(2*v[i]-w[i] for i in range(k)),q) for (v,w),q in ideal.items()]
    mean=tuple(sum(q*v[i] for v,q in y) for i in range(k))
    bias=tuple(u[i]-mean[i] for i in range(k))
    variance=sum(q*norm2(tuple(v[i]-mean[i] for i in range(k))) for v,q in y)
    two_error=sum(q*z*norm2(tuple(F(u[i])-F(v[i]+w[i],2) for i in range(k))) for v,q in y for w,z in y)
    assert two_error==norm2(bias)+variance/2
assert conditioning_changes

# Constant floor/ceiling relationships independent of huge exponential rho.
floors=0
for j0 in range(1,31):
    for r in range(4*j0,4*j0+40):
        m=r//2; ell=(r-m)//j0
        assert ell>=F(r,4*j0) and m>=F(r,3)
        floors+=1
for sparsity,epsilon in product(range(1,7),[F(1,3),F(1),F(5,2),F(100)]):
    ceil=lambda q:-(-q.numerator//q.denominator)
    length=ceil(4*sparsity*sparsity/epsilon**2)
    ss=2**length-1
    replicas=ceil(8*sparsity*ss*ss/epsilon**2)
    assert F(sparsity*sparsity,2*length+1)+F(sparsity*ss*ss,replicas)<=epsilon**2/4
print(f'PASS: {len(states)} signed states; 9 filter powers; {histories} full adaptive histories; shared-center two-trajectory bias/variance; {floors} floor cases; 24 ceiling cases.')
