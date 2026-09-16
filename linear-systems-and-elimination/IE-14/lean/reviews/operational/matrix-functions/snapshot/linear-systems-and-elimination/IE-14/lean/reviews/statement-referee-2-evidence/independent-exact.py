"""Independent finite rational IE14 diagnostics; not a proof for all dimensions."""
from fractions import Fraction as F
from pathlib import Path
from itertools import product
import json, hashlib

P=Path(__file__).resolve().parents[2]
def mm(a,b): return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]
fib=[0,1]
for _ in range(35): fib.append(sum(fib[-2:]))
cases=[]
for n in range(4,31):
    lower=[[F(i==j)-F(i!=j and i-j in (1,2)) for j in range(n)] for i in range(n)]
    upper=[[F(fib[n+1]+1 if i==j else fib[i+2]) if j==n-1 else
            F(1,2) if (i==j and i==1) or (i==0 and j==1) else
            F(i==j) for j in range(n)] for i in range(n)]
    c=mm(lower,upper)
    factor_index=[0 if i==0 else 1 if i+1==n else i+1 for i in range(n)]
    assert sorted(factor_index)==list(range(n))
    a=[c[i][:] for i in factor_index]
    assert all(a[i][j]==0 for i in range(n) for j in range(n)
               if abs(i-j)>1 and (i,j) not in [(0,n-1),(n-1,0)])
    assert a[0][-1]==1 and a[-1][0]==-1 and max(map(abs,sum(a,[])))==1
    s=[row[:] for row in a];labels=list(range(n));chosen=[];pivots=[];growth=F(0);sign=1
    for k in range(n):
        growth=max(growth,max(abs(s[i][j]) for i in range(k,n) for j in range(k,n)))
        pivot_position=k if k==0 else n-1
        chosen.append(labels[pivot_position]);v=s[pivot_position][k]
        assert pivot_position>=k and v!=0 and all(abs(s[i][k])<=abs(v) for i in range(k,n))
        labels[k],labels[pivot_position]=labels[pivot_position],labels[k]
        s[k],s[pivot_position]=s[pivot_position],s[k]
        sign*=(-1 if k!=pivot_position else 1);pivots.append(v)
        s=[[s[i][j]-s[i][k]/v*s[k][j] if i>k and j>k else F(0) for j in range(n)] for i in range(n)]
    assert chosen==[0,n-1]+list(range(1,n-1))
    assert pivots==[upper[i][i] for i in range(n)]
    assert growth==fib[n+1]+1 and s==[[0]*n for _ in range(n)]
    det=F(sign)
    for x in pivots:det*=x
    assert det==F((-1)**(n-2)*(fib[n+1]+1),2)
    cases.append({'n':n,'growth':str(growth),'determinant_from_exact_pivots':str(det),'both_corners':[str(a[0][-1]),str(a[-1][0])],'all_current_last_row_pivots_legal':True})

# Exact Gaussian-rational diagnostic of the two-row envelope for every removed
# row and sampled complex multipliers of modulus <=1. No floating-point square root.
def cmul(x,y):return (x[0]*y[0]-x[1]*y[1],x[0]*y[1]+x[1]*y[0])
def csub(x,y):return (x[0]-y[0],x[1]-y[1])
def nsq(x):return x[0]**2+x[1]**2
phases=[(F(1),F(0)),(F(-1),F(0)),(F(0),F(1)),(F(0),F(-1))]
multipliers=[(F(0),F(0))]+phases+[(F(3,5),F(4,5))]
front_checks=0
for a in range(4):
 for b in range(a+1):
  for pa,pb in product(phases,repeat=2):
   for c in [0,1]:
    for pc in phases:
     v=[(a*pa[0],a*pa[1]),(b*pb[0],b*pb[1]),(c*pc[0],c*pc[1])]
     for pivot in range(3):
      others=[i for i in range(3) if i!=pivot]
      for q1,q2 in product(multipliers,repeat=2):
       sq=sorted([nsq(csub(v[i],cmul(q,v[pivot]))) for i,q in zip(others,[q1,q2])],reverse=True)
       if c==0:assert sq[0]<=(a+b)**2 and sq[1]<=a*a
       bound=a+b+c+max(a,b,c);gap=bound*bound-sum(sq)
       assert gap>=0 and gap*gap>=4*sq[0]*sq[1]
       front_checks+=1
out={'scope':'Finite independent exact diagnostics only; no all-size or all-complex proof claimed','witness_cases':cases,'complex_front_sample_checks':front_checks,'certificate_target':{'half_positive':F(0)<F(1,2),'half_le_one':F(1,2)<=1},'definition_sha256':hashlib.sha256((P/'NLA/IE14/Definitions.lean').read_bytes()).hexdigest(),'challenge_sha256':hashlib.sha256((P/'Challenge.lean').read_bytes()).hexdigest()}
print(json.dumps(out,indent=2))
