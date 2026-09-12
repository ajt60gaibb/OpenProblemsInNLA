"""Exact independent finite checks; no claim to prove CFC or all-unitary lemmas."""
from fractions import Fraction as F
import json

n=3
def mat(rows):return [[F(x) for x in row] for row in rows]
def trans(a):return [list(r) for r in zip(*a)]
def add(a,b):return [[a[i][j]+b[i][j] for j in range(n)] for i in range(n)]
def scale(s,a):return [[s*x for x in r] for r in a]
def mul(a,b):return [[sum(a[i][k]*b[k][j] for k in range(n)) for j in range(n)] for i in range(n)]
def outer(w):return [[F(w[i])*F(w[j]) for j in range(n)] for i in range(n)]
def diag(a,b,c):return mat([[a,0,0],[0,b,0],[0,0,c]])
A=mat([[1,F(3,4),0],[0,0,0],[0,0,0]])
B=mat([[-1,0,0],[0,0,0],[F(-3,4),0,0]])
Z=add(A,B)
R=scale(F(1,20),outer([4,3,0])); L=diag(F(5,4),0,0)
T=scale(F(1,20),outer([4,0,3]))
G=diag(F(3,4),F(3,4),0);H=diag(F(3,4),0,F(3,4))
for x,y in [(A,R),(trans(A),L),(B,L),(trans(B),T),(Z,G),(trans(Z),H)]:
 assert mul(y,y)==mul(trans(x),x)
 assert trans(y)==y
SA=scale(F(1,2),add(R,L));SB=scale(F(1,2),add(L,T));SZ=scale(F(1,2),add(G,H))
assert SA==mat([[F(41,40),F(3,10),0],[F(3,10),F(9,40),0],[0,0,0]])
assert SB==mat([[F(41,40),0,F(3,10)],[0,0,0],[F(3,10),0,F(9,40)]])
assert SZ==diag(F(3,4),F(3,8),F(3,8))
I=diag(1,1,1)
assert SA==add(add(scale(F(1,8),I),scale(F(1,10),outer([3,1,0]))),scale(F(-1,8),diag(0,0,1)))
assert SB==add(add(scale(F(1,8),I),scale(F(1,10),outer([3,0,1]))),scale(F(-1,8),diag(0,1,0)))
assert F(2)<F(9,4) and F(9,4)-2==F(1,4)
print(json.dumps({'status':'PASS','ordered_Gram_square_checks':6,'positive_modulus_certificates':'Two positive outer products and four positive diagonal matrices','symmetricA':SA,'symmetricB':SB,'symmetricSum':SZ,'rank_one_decompositions':2,'minimal_scalar_squared_gap':'1/4','universal_obligations':'CFC root uniqueness, nonzero orthogonal-vector existence for arbitrary complex a,b, PSD quadratic monotonicity and all-unitary bounds remain Lean proof obligations.'},default=str,indent=2))
