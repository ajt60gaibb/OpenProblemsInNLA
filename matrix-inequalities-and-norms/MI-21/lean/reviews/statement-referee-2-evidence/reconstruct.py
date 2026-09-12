from fractions import Fraction as F
from pathlib import Path
import json

def mm(a,b):return [[sum(a[i][k]*b[k][j] for k in range(2)) for j in range(2)] for i in range(2)]
def sm(c,a):return [[c*x for x in row] for row in a]
def add(a,b):return [[a[i][j]+b[i][j] for j in range(2)] for i in range(2)]
def tr(a):return a[0][0]+a[1][1]
def det(a):return a[0][0]*a[1][1]-a[0][1]*a[1][0]
def inv(a):return sm(1/det(a),[[a[1][1],-a[0][1]],[-a[1][0],a[0][0]]])
def pd(a):return a[0][1]==a[1][0] and a[0][0]>0 and det(a)>0
def fmt(a):return [[str(x) for x in row] for row in a]
C=[[F(12,37),F(0)],[F(0),F(21,29)]]
E=[[F(35,37),F(0)],[F(0),F(20,29)]]
S=sm(F(1,17),[[F(15),F(8)],[F(8),F(-15)]])
I=[[F(1),F(0)],[F(0),F(1)]]
assert pd(C) and pd(E) and mm(S,S)==I
A=[mm(C,C),mm(E,E)]
B=[mm(mm(S,A[1]),S),mm(mm(S,A[0]),S)]
assert all(pd(x) for x in A+B)
assert add(*A)==I and add(*B)==I
D=mm(mm(S,E),S);D2=mm(mm(S,C),S)
delta=F(5,3);delta2=F(3,5)
assert delta**2==det(D)/det(C) and delta2**2==det(D2)/det(E)
h=tr(mm(inv(C),D))+2*delta
h2=tr(mm(inv(E),D2))+2*delta2
T=add(D,sm(delta,C));T2=add(D2,sm(delta2,E))
assert h==F(61697295,8682716)
assert T==sm(F(1,310097),[[F(443355),F(33000)],[F(33000),F(605715)]])
assert pd(T) and pd(T2) and h>0 and h2>0
assert mm(mm(T,inv(C)),T)==sm(h,D)
assert mm(mm(T2,inv(E)),T2)==sm(h2,D2)
Gsq=sm(1/h,mm(T,T));Hsq=sm(1/h2,mm(T2,T2))
assert Gsq==sm(F(1,12158163),[[F(3516940),F(616000)],[F(616000),F(6547660)]])
assert Hsq==mm(mm(S,Gsq),S)
L=add(Gsq,Hsq)
assert L==sm(F(1,12158163),[[F(8216600),F(-985600)],[F(-985600),F(11912600)]])
w=[F(1),F(-4)];lam=F(1351000,1350907)
assert [sum(L[i][j]*w[j] for j in range(2)) for i in range(2)]==[lam*x for x in w]
assert lam-1==F(93,1350907)>0
result={"method":"Independent exact Fraction reconstruction, including both scaled Riccati identities; this is statement validation, not a Lean proof.","C":fmt(C),"E":fmt(E),"S":fmt(S),"A":[fmt(x) for x in A],"B":[fmt(x) for x in B],"input_leading_minors":[[str(x[0][0]),str(det(x))] for x in A+B],"D":fmt(D),"D2":fmt(D2),"delta":str(delta),"delta2":str(delta2),"h":str(h),"h2":str(h2),"T":fmt(T),"T2":fmt(T2),"both_scaled_Riccati_identities":True,"G_squared":fmt(Gsq),"H_squared":fmt(Hsq),"L":fmt(L),"eigenvector":[str(x) for x in w],"lambda":str(lam),"lambda_minus_one":str(lam-1),"all_assertions_passed":True,"remaining_Lean_obligations":["Actual CFC square-root and geometric-mean identities","Actual Euclidean operator-norm admissibility for all dimensions","Eigenvalue to actual operator-norm bound","Full original conjecture negation"]}
Path(__file__).with_name("numerical-reconstruction.json").write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps(result,indent=2))
