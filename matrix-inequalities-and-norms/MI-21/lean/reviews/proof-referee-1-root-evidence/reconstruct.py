"""Independent exact arithmetic check of the completed common-scale certificates.
This supplements the full analytic Lean proof; it is not a proof of CFC identities.
"""
from fractions import Fraction as F
import json

def mul(a,b):
    return [[sum(a[i][k]*b[k][j] for k in range(2)) for j in range(2)] for i in range(2)]
def add(a,b):
    return [[a[i][j]+b[i][j] for j in range(2)] for i in range(2)]
def scale(c,a):
    return [[c*x for x in row] for row in a]
def diag(a,b):
    return [[F(a),F(0)],[F(0),F(b)]]
def conjugate(s,a):
    return mul(mul(s,a),s)
def det(a):
    return a[0][0]*a[1][1]-a[0][1]*a[1][0]
I=diag(1,1)
C=diag(F(12,37),F(21,29))
E=diag(F(35,37),F(20,29))
S=scale(F(1,17),[[15,8],[8,-15]])
assert mul(S,S)==I
assert add(mul(C,C),mul(E,E))==I
assert add(conjugate(S,mul(E,E)),conjugate(S,mul(C,C)))==I
D=conjugate(S,E)
D2=conjugate(S,C)
N=add(D,scale(F(5,3),C))
N2=conjugate(S,N)
assert N==scale(F(1,310097),[[443355,33000],[33000,605715]])
assert N2==scale(F(1,310097),[[506715,-85800],[-85800,542355]])
h=F(61697295,8682716)
assert h>0
assert mul(mul(N,diag(F(37,12),F(29,21))),N)==scale(h,D)
assert mul(mul(N2,diag(F(37,35),F(29,20))),N2)==scale(h,D2)
for a in [C,E,D,D2,N,N2,mul(C,C),mul(E,E),conjugate(S,mul(C,C)),conjugate(S,mul(E,E))]:
    assert a[0][1]==a[1][0] and a[0][0]>0 and det(a)>0
L=scale(1/h,add(mul(N,N),mul(N2,N2)))
assert L==scale(F(1,12158163),[[8216600,-985600],[-985600,11912600]])
v=[1,-4]
lam=F(1351000,1350907)
assert [sum(L[i][k]*v[k] for k in range(2)) for i in range(2)]==[lam*x for x in v]
assert lam-1==F(93,1350907)>0
print(json.dumps({'status':'PASS','common_scale':str(h),'first_numerator':N,'second_numerator':N2,'left_matrix':L,'eigenvalue':str(lam),'gap':str(lam-1),'scope':'Exact rational supplements; actual CFC/norm/quantified proof independently kernel checked.'},default=str,indent=2))
