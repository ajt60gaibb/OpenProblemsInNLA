"""Independent exact finite reconstruction of Colbrook's projection witness.
No finite calculation is used to infer universal concavity or CFC identities.
"""
from fractions import Fraction as F
import json

def mul(a,b):return [[sum(a[i][k]*b[k][j] for k in range(2)) for j in range(2)] for i in range(2)]
def add(a,b):return [[a[i][j]+b[i][j] for j in range(2)] for i in range(2)]
def sub(a,b):return [[a[i][j]-b[i][j] for j in range(2)] for i in range(2)]
def scale(c,a):return [[c*x for x in r] for r in a]
P=[[F(1),F(0)],[F(0),F(0)]]
u=[F(3,5),F(4,5)]
Q=[[u[i]*u[j] for j in range(2)] for i in range(2)]
assert sum(x*x for x in u)==1
assert Q==scale(F(1,25),[[9,12],[12,16]])
assert mul(P,P)==P and mul(Q,Q)==Q
T=add(P,Q);T2=mul(T,T);G=sub(T,T2)
assert T==scale(F(1,25),[[34,12],[12,16]])
assert T2==scale(F(1,25),[[52,24],[24,16]])
assert G==scale(F(1,25),[[-18,-12],[-12,0]])
w=[F(1),F(-2)];Gw=[sum(G[i][j]*w[j] for j in range(2)) for i in range(2)]
assert Gw==[F(6,25),F(-12,25)]
quadratic=sum(w[i]*Gw[i] for i in range(2));assert quadratic==F(6,5)>0
f=lambda t:t-t*t
assert f(F(0))==0 and f(F(2))==-2
print(json.dumps({'status':'PASS','P':P,'Q':Q,'sum':T,'sum_squared':T2,'image':G,'image_times_vector':Gw,'quadratic_form':str(quadratic),'positive_Gram_certificate':'P and Q are real orthogonal projections and hence complex PSD; genuine CFC bridge remains a Lean obligation.','universal_concavity_argument':'For f(t)=t−t², the Jensen difference is theta*(1−theta)*(x−y)²; its universal analytic proof is separate from these finite checks.'},default=str,indent=2))
