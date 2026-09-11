"""Independent exact checks for IE-17/18/19. No submitted code is imported."""
from fractions import Fraction as F
from itertools import permutations
from pathlib import Path
import json

def dot(a,b): return sum(x*y for x,y in zip(a,b))
def det(a):
    total=F(0)
    for p in permutations(range(len(a))):
        value=(-1)**sum(p[i]>p[j] for i in range(len(p)) for j in range(i+1,len(p)))
        for i,j in enumerate(p): value*=a[i][j]
        total+=value
    return total
def minors(a): return [det([row[:k] for row in a[:k]]) for k in range(1,len(a)+1)]
def solve(a,b):
    denominator=det(a)
    return [det([[b[i] if j==k else a[i][j] for j in range(len(a))] for i in range(len(a))])/denominator for k in range(len(a))]

diag=[F(1),F(6),F(5)]
b=list(map(F,[11,1,1,1]))
g=list(map(F,[11,6,5]))
h=[a*a for a in diag]
xs=[[F(z,31201) for z in [11231,6126,5105]], [F(z,55219) for z in [87659,7599,16865]]]
data=[]
for k,x in enumerate(xs,1):
    nr=[g[i]-h[i]*x[i] for i in range(3)]
    assert all(dot([h[i]**(j+1)*g[i] for i in range(3)],nr)==0 for j in range(k))
    z=[diag[i]*x[i] for i in range(3)]+[F(0)]
    r=[b[i]-z[i] for i in range(4)]
    s=dot(x,x); rr=dot(r,r)
    D=[[(rr*(i==j)-r[i]*r[j]+z[i]*z[j])/s for j in range(4)] for i in range(4)]
    approx=sum(nr[i]**2/(s*h[i]+rr) for i in range(3))
    data.append((z,r,s,D,approx))
w=list(map(F,[250,-1,1,27])); omega=dot(w,w); kappa=F(1979,2000)
z,r,s,D,t1=data[0]; hz=dot(w,z)
row=sum(diag[i]**2*w[i]**2 for i in range(3))/omega
column=sum(w[i]*D[i][j]*w[j] for i in range(4) for j in range(4))/omega
assert row==F(62561,63231) and column==F(1642993919237,1713779258646)
assert max(row,column)<kappa
c=[r[i]-w[i]*dot(w,r)/omega for i in range(4)]
a=[-diag[j]*w[j]+hz*xs[0][j]/s for j in range(3)]
E=[[-w[i]*w[j]*diag[j]/omega+c[i]*xs[0][j]/s+hz*c[i]*a[j]/(omega*s*kappa-hz**2) for j in range(3)] for i in range(4)]
B=[[(diag[j] if i==j else 0)+E[i][j] for j in range(3)] for i in range(4)]
new_res=[dot(B[i],xs[0])-b[i] for i in range(4)]
assert all(sum(B[i][j]*new_res[i] for i in range(4))==0 for j in range(3))
upper=minors([[kappa*(i==j)-sum(E[k][i]*E[k][j] for k in range(4)) for j in range(3)] for i in range(3)])
assert min(upper)>0
D2=data[1][3]
K=[[F(2407881992100)*(F(5,6)*(h[i] if i==j and i<3 else 0)+D2[i][j]/6-F(99,100)*(i==j)) for j in range(4)] for i in range(4)]
lower=minors(K)
assert lower==list(map(F,[206417059721,17265994657467102998545591,960941324740480331793743845178086291011,65442104145157248520714038046591467785805073713081]))
assert t1==F(69694107852573439503892031925,69323394392991282508138323472)
assert data[1][4]==F(5430772101137459612205263871781350,5387955615790281743396033884265233)
assert t1<F(1006,1000)<F(1007,1000)<data[1][4]

def R(m,v):
    a=[1-x for x in m]
    coefficient=dot(a,[x*x for x in v])/sum(ai*ai*vi*vi for ai,vi in zip(a,v))
    return [mi*(1-coefficient*ai)*vi for mi,ai,vi in zip(m,a,v)]
anderson=[]
for m in [[F(1,10),F(1,2),F(3,5)],[F(0),F(1,2),F(2,3)]]:
    z=R(m,R(m,[F(1)]*3))
    pairs=[(m[i]*m[j]*(m[j]-m[i])/(abs(m[i]*(1-m[i]))+abs(m[j]*(1-m[j]))))**2 for i in range(3) for j in range(i+1,3)]
    square=dot(z,z)/3
    assert square>max(pairs)**2
    anderson.append({"second_residual":list(map(str,z)),"squared_ratio":str(square),"pairwise_bound":str(max(pairs))})
J=[[F(2) if i==j else F(1,2) for j in range(3)] for i in range(3)]
JI=[solve(J,[F(i==j) for i in range(3)]) for j in range(3)]
assert max(sum(abs(v) for v in row) for row in JI)==F(7,9)
result={"status":"PASS","method":"Independent standard-library rational arithmetic; determinants by permutation expansion; no submitted imports","IE17_lower_minors":list(map(str,lower)),"IE17_upper_minors_positive":all(x>0 for x in upper),"IE17_squared_approximations":[str(t1),str(data[1][4])],"IE18":anderson,"IE19_inverse_norm":"7/9"}
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps(result,indent=2))
