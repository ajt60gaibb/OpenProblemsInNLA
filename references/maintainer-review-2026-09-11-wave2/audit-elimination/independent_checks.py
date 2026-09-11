#!/usr/bin/env python3
"""Independent exact/symbolic checks. These supplement the analytic audit, not prove it.
Run: PYTHONPATH=/private/tmp/nla-pr-review-20260911/python-deps python3 -B independent_checks.py
"""
from pathlib import Path
import json
import sympy as s
Q=s.Rational
out={}

def exact_path(A, order=None, rook=False):
    A=s.Matrix(A); n=A.rows; largest=max(abs(v) for v in A); initial=largest
    labels=list(range(n)); pivots=[]
    for k in range(n):
        if order is not None:
            r=labels.index(order[k]);A.row_swap(k,r);labels[k],labels[r]=labels[r],labels[k]
        pivot=A[k,k]
        assert pivot and all(abs(A[i,k])<=abs(pivot) for i in range(k,n))
        if rook:assert all(abs(A[k,j])<=abs(pivot) for j in range(k,n))
        pivots.append(pivot)
        for i in range(k+1,n):
            factor=A[i,k]/pivot
            for j in range(k+1,n):A[i,j]-=factor*A[k,j]
            A[i,k]=0
        largest=max(largest,*[abs(A[i,j]) for i in range(k,n) for j in range(k,n)])
    return pivots,s.cancel(largest/initial)

# Reconstruct band witnesses directly from the displayed factorization.
band=[]
for p,q in [(1,0),(1,8),(2,0),(2,7),(3,1),(4,9),(7,2)]:
    j=p+q+1;n=j+p;L=s.eye(n)
    for i in range(n):
        for k in range(max(0,i-p),i):L[i,k]=-1
    order=[p,*range(p),*range(p+1,n)];A=s.zeros(n)
    for k in range(j-1):
        v=s.zeros(n,1)
        if k<=p:
            v[0]=1
            for i in range(1,k+1):v[i]=2**(i-1)
        else:v[k]=1
        col=L*v/2**p
        for i,r in enumerate(order):A[r,k]=col[i]
    for i in range(p,n):A[i,j-1]=1
    for k in range(j,n):A[k,k]=1
    assert max(abs(v) for v in A)==1
    assert all(A[i,k]==0 for i in range(n) for k in range(n) if i-k>p or k-i>q)
    piv,growth=exact_path(A,order)
    h=[0]
    for k in range(1,p+q+1):h.append(1+sum(h[max(0,k-p):k]))
    assert growth==h[-1]
    band.append({'p':p,'q':q,'growth':str(growth),'determinant_nonzero':A.det()!=0})
out['band']=band

cyclic=[]
for n in [4,5,8,12]:
    L=s.eye(n);U=s.eye(n);U[0,1]=U[1,1]=Q(1,2)
    for i in range(n):
        for k in [i-1,i-2]:
            if k>=0:L[i,k]=-1
        U[i,n-1]=s.fibonacci(i+2)+(i==n-1)
    C=L*U;order=[0,n-1,*range(1,n-1)];A=s.zeros(n)
    for i,r in enumerate(order):A[r,:]=C[i,:]
    assert A[0,n-1] and A[n-1,0]
    assert all(A[i,j]==0 for i in range(n) for j in range(n) if abs(i-j)>1 and (i,j) not in [(0,n-1),(n-1,0)])
    piv,growth=exact_path(A,order);assert growth==s.fibonacci(n+1)+1
    cyclic.append({'n':n,'growth':str(growth)})
out['cyclic']=cyclic

# LSMR: derive iterates from the constrained normal equations, not submitted x values.
A=s.diag(1,6,5).col_join(s.zeros(1,3));b=s.Matrix([11,1,1,1]);H=A.T*A;g=A.T*b;C=A*A.T
xs=[];Ds=[];tildes=[]
for k in [1,2]:
    V=s.Matrix.hstack(*[H**i*g for i in range(k)]);F=H*V;x=V*(F.T*F).inv()*F.T*g
    r=b-A*x;z=A*x;ss=x.dot(x);rr=r.dot(r);D=(rr*s.eye(4)-r*r.T+z*z.T)/ss
    assert F.T*(g-H*x)==s.zeros(k,1)
    xs.append(x);Ds.append(D);tildes.append(s.cancel((r.T*A*(ss*H+rr*s.eye(3)).inv()*A.T*r)[0]))
x=xs[0];r=b-A*x;z=A*x;ss=x.dot(x);w=s.Matrix([250,-1,1,27]);omega=w.dot(w);h=w.dot(z);kap=Q(1979,2000)
c0=r-w*w.dot(r)/omega;a0=-A.T*w+h*x/ss
E=-w*w.T*A/omega+c0*x.T/ss+h*c0*a0.T/(omega*ss*kap-h*h)
assert (A+E).T*((A+E)*x-b)==s.zeros(3,1)
U=kap*s.eye(3)-E.T*E;lower=Q(5,6)*C+Q(1,6)*Ds[1]-Q(99,100)*s.eye(4)
upmin=[s.factor(U[:k,:k].det()) for k in range(1,4)];lomin=[s.factor(lower[:k,:k].det()) for k in range(1,5)]
assert all(v>0 for v in upmin+lomin)
assert tildes[0]<Q(1006,1000)<Q(1007,1000)<tildes[1]
out['lsmr']={'x1':list(map(str,xs[0])),'x2':list(map(str,xs[1])),'upper_squared':str(kap),'strict_lower_squared':'99/100','upper_principal_minors':list(map(str,upmin)),'lower_principal_minors':list(map(str,lomin)),'tilde_squared':list(map(str,tildes))}

# Restarted Anderson exact values and analytic first derivatives.
e=s.symbols('e',real=True)
def R(m,v):
    a=s.eye(3)-m;alpha=s.cancel((v.T*a*v)[0]/(v.T*a*a*v)[0]);return alpha,(m*(v-alpha*a*v)).applyfunc(s.cancel)
v=s.ones(3,1);m=s.diag(Q(1,10),Q(1,2),Q(3,5));alpha,w=R(m,v);beta,z=R(m,w)
ratio=s.cancel(z.dot(z)/3);assert ratio==Q(1920682,21289638243)>Q(1,14641)
m=s.diag(e**2,Q(1,2),Q(1,2)+e);alpha,w=R(m,v);beta,z=R(m,w)
assert s.simplify(alpha.subs(e,0))==Q(4,3) and s.diff(alpha,e).subs(e,0)==Q(2,9)
assert [s.diff(vv,e).subs(e,0) for vv in z]==[0,-Q(1,12),Q(1,12)]
assert beta.subs(e,0)==2 and s.diff(beta,e).subs(e,0)==2
out['anderson']={'exact_squared_ratio':str(ratio),'second_residual_derivative':['0','-1/12','1/12'],'beta_derivative':'2'}

J=s.eye(3)*Q(3,2)+s.ones(3)*Q(1,2);S=s.eye(3)+s.ones(3)
norminf=lambda M:max(sum(abs(M[i,j]) for j in range(M.cols)) for i in range(M.rows))
assert norminf(J.inv())==Q(7,9)<Q(5,4)==norminf(S.inv())
out['inverse_norm']={'J':'7/9','S':'5/4'}
A=s.Matrix([[1,1,0],[1,0,1]]);B=A.T*(A*A.T).inv();X=s.Matrix([[0,0],[1,0],[0,1]])
assert A*X==s.eye(2) and B!=X and (s.eye(2)-B.T*B).eigenvals()=={Q(2,3):1,0:1}
assert B.T*B*s.Matrix([1,-1])==s.Matrix([1,-1]);out['right_inverse']='exact identities PASS; norm range proved analytically'

rook=[]
for A,expected in [(s.Matrix([[1,0,-1],[0,1,-1],[1,1,1]]),3),(s.Matrix([[1,0,1,1],[0,1,Q(1,3),-1],[-Q(1,3),-1,1,-1],[-1,1,1,1]]),Q(14,3)),(s.Matrix([[1,0,-Q(1,3),1,1],[0,1,1,-1,1],[1,-Q(1,3),1,Q(1,6),-1],[-1,1,Q(1,6),1,-1],[-1,-1,1,1,1]]),Q(893,131))]:
    piv,growth=exact_path(A,rook=True);assert growth==expected
    rook.append({'n':A.rows,'pivots':list(map(str,piv)),'growth':str(growth),'determinant':str(A.det())})
out['rook']=rook
c,v=s.symbols('c v');assert s.expand(1+c+v-3*c*v+4+(1+c)*(1+v)-(8-2*(1-c)*(1-v)))==0
out['rook_scalar_hard_case']='symbolic endpoint identity PASS'
Path(__file__).with_name('independent-check-results.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS: independent exact and symbolic checks for every finite witness family; no sampled claim of universal proof.')
