"""Independent exact diagnostic checks of the reviewed algebra and endpoints.
These supplement the universal Lean proof; they do not replace root geometry.
"""
from fractions import Fraction as F
from itertools import combinations
from math import factorial, prod
from pathlib import Path
import json

def elementary(xs, j):
    return sum((prod(c, start=F(1)) for c in combinations(xs,j)), start=F(0))

def generating(xs):
    out = [F(1)]
    for x in xs:
        new = [F(0)]*(len(out)+1)
        for j,c in enumerate(out):
            new[j] += c
            new[j+1] += x*c
        out = new
    return out

def derivative(p):
    return [j*p[j] for j in range(1,len(p))] or [F(0)]

tuples = [(), (F(2),), (F(1),F(3)), (F(1),)*3,
          (F(1),F(2),F(3)), (F(1,3),F(2),F(7)),
          (F(3,5),F(3,5),F(4),F(9)), (F(5,7),)*5]
records=[]
for xs in tuples:
    n=len(xs)
    e=[elementary(xs,j) for j in range(n+2)]
    assert e[0]==1 and e[n+1]==0 and all(y>0 for y in e[:n+1])
    p=generating(xs)
    assert p==e[:-1]
    q=p[:]
    for d in range(n+1):
        assert len(q)-1==n-d and q[0]==factorial(d)*e[d]>0
        q=derivative(q)
    assert q==[0]
    seq=[(j+1)*e[j+1]/e[j] for j in range(n+1)]
    assert seq[n]==0
    differences=[]
    for j in range(2,n):
        gap=seq[j-1]-2*seq[j]+seq[j+1]
        assert gap>=0
        if len(set(xs))==1:
            assert gap==0
        differences.append({'j':j,'gap':str(gap),'degree_of_Q':n-j+1})
    records.append({'tuple':list(map(str,xs)),'coefficients':list(map(str,p)),
                    'second_differences':differences})

# The smallest non-equal case, lambda=(1,2,3), at its only canonical index j=2.
# Q=P'=6+22t+18t²; infer power sums exactly from its normalized coefficients.
s1,s2,s3=F(11,3),F(67,9),F(440,27)
gap=s1*s3-s2*s2
denom=s1*(s1*s1-s2)
assert gap==F(13,3) and denom==22
assert 2*gap/denom==F(13,33)
assert s1**3-3*s1*s2+2*s3==0  # Actual degree-two third derivative.

mu_cases=[(F(1),F(1)), (F(1,2),F(7)), (F(2),F(2),F(3)), (F(1,4),F(2),F(9),F(5,3))]
for mu in mu_cases:
    s={r:sum(x**r for x in mu) for r in (1,2,3)}
    pair=sum(mu[a]*mu[b]*(mu[a]-mu[b])**2 for a,b in combinations(range(len(mu)),2))
    pair_base=sum(mu[a]*mu[b] for a,b in combinations(range(len(mu)),2))
    assert s[1]*s[3]-s[2]**2==pair>=0
    assert s[1]**2-s[2]==2*pair_base>0
    lhs=s[1]-2*(s[1]**2-s[2])/s[1]+(s[1]**3-3*s[1]*s[2]+2*s[3])/(s[1]**2-s[2])
    assert lhs==2*pair/(s[1]*(s[1]**2-s[2]))

out={'status':'PASS','scope':'Exact supplementary diagnostics, not the universal proof',
     'tuple_cases':records,'mu_certificate_cases':len(mu_cases),
     'smallest_unequal_endpoint':{'lambda':['1','2','3'],'j':2,'gap':'13/33',
                                'pairGap':'13/3','denominator':'22','third_derivative':'0'}}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
