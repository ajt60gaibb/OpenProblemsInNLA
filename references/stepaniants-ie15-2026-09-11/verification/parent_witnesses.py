from fractions import Fraction as F
from functools import reduce
from operator import mul

def mx(A):return max(abs(x) for r in A for x in r)
def schur(A):
 p=A[0][0]
 return [[A[i][j]-A[i][0]*A[0][j]/p for j in range(1,len(A))] for i in range(1,len(A))]
examples=[[[1,0,-1],[0,1,-1],[1,1,1]],[[1,0,1,1],[0,1,F(1,3),-1],[-F(1,3),-1,1,-1],[-1,1,1,1]]]
for raw,expected in zip(examples,[F(3),F(14,3)]):
 A=[[F(x) for x in r] for r in raw];S=A;piv=[];growth=mx(S)
 while S:
  p=S[0][0];assert p!=0;assert all(abs(x)<=abs(p) for x in S[0]);assert all(abs(r[0])<=abs(p) for r in S)
  print('n',len(A),'active',[[str(x) for x in r] for r in S])
  growth=max(growth,mx(S));piv.append(p);S=schur(S)
 assert reduce(mul,piv)!=0;assert growth/mx(A)==expected
 print('verified growth',growth,'det',reduce(mul,piv))
