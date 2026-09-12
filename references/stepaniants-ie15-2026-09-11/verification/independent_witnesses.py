from fractions import Fraction as F
from functools import reduce
examples=[(3,[[1,0,-1],[0,1,-1],[1,1,1]],F(3)),(4,[[1,0,1,1],[0,1,F(1,3),-1],[F(-1,3),-1,1,-1],[-1,1,1,1]],F(14,3))]
for n,rows,target in examples:
 S=[[F(z) for z in row] for row in rows];norm0=max(abs(z) for row in S for z in row);rho=norm0;det=F(1);piv=[]
 while S:
  p=S[0][0];assert p!=0
  assert all(abs(p)>=abs(v) for v in S[0])
  assert all(abs(p)>=abs(row[0]) for row in S)
  piv.append(p);det*=p;rho=max(rho,max(abs(z) for row in S for z in row))
  print(n,'active',S)
  S=[[S[i][j]-S[i][0]*S[0][j]/p for j in range(1,len(S))] for i in range(1,len(S))]
 assert rho/norm0==target and det!=0
 print(n,'pivots',piv,'determinant',det,'growth',rho/norm0)
print('PASS: both exact witnesses, every rook inequality including ties, every active matrix and determinant')
