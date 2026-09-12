"""Exact two-sign Walsh and uniform-subset sanity check, independent of submission."""
from fractions import Fraction as F
from itertools import product, combinations
from pathlib import Path
import json

def trans(A):return list(map(list,zip(*A)))
def mm(A,B):return [[sum(x*y for x,y in zip(row,col)) for col in zip(*B)] for row in A]
def tr(A):return sum(A[i][i] for i in range(len(A)))
def normf2(A):return sum(z*z for row in A for z in row)
H=[[F((-1)**((i&j).bit_count()),2) for j in range(4)] for i in range(4)]
V=[[F(3,5),0],[F(4,5),0],[0,F(5,13)],[0,F(12,13)]]
assert mm(trans(V),V)==[[1,0],[0,1]]
I=[[int(i==j) for j in range(2)] for i in range(2)]
ps=[];errs={k:[] for k in range(1,5)}; conditional_checks=0
for d1 in product((-1,1),repeat=4):
    U=mm(H,[[d1[i]*z for z in row] for i,row in enumerate(V)])
    for d2 in product((-1,1),repeat=4):
        X=mm(H,[[d2[i]*z for z in row] for i,row in enumerate(U)])
        P=mm(X,trans(X));ps.append([4*z for row in P for z in row])
        assert mm(trans(X),X)==I
        for k in range(1,5):
            vals=[]
            for J in combinations(range(4),k):
                Gram=[[F(4,k)*sum(X[t][i]*X[t][j] for t in J) for j in range(2)] for i in range(2)]
                err=[[Gram[i][j]-I[i][j] for j in range(2)] for i in range(2)]
                vals.append(normf2(err))
            actual=sum(vals)/len(vals)
            predicted=F(4-k,k*3)*(4*sum(sum(z*z for z in row)**2 for row in X)-2)
            assert actual==predicted
            conditional_checks+=1;errs[k].append(actual)
mean=[sum(row[j] for row in ps)/len(ps) for j in range(16)]
assert mean==[2*int(i==j) for i in range(4) for j in range(4)]
covchecks=0
for a in range(16):
    for b in range(16):
        i,j=divmod(a,4);u,v=divmod(b,4)
        if i^j^u^v:
            cov=sum(row[a]*row[b] for row in ps)/len(ps)-mean[a]*mean[b]
            assert cov==0;covchecks+=1
moments={k:sum(v)/len(v) for k,v in errs.items()}
for k,value in moments.items():assert value<=F(6,k)
report={'status':'PASS','n':4,'r':2,'independent_sign_draws':len(ps),'conditional_fixed_subset_identity_checks':conditional_checks,'xor_forced_zero_covariance_checks':covchecks,'allwidth_average_Frobenius_squared':{k:str(v) for k,v in moments.items()},'scope':'finite exact sanity check, not a substitute for analytic proof'}
Path('/private/tmp/nla-review-trace/pr141-walsh-check.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
