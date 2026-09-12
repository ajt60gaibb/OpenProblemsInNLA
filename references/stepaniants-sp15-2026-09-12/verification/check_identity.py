"""Limited exact diagnostic of the proved determinant identity, not a proof of its quantified form."""
from pathlib import Path
import hashlib
import json


def transpose(a): return [list(v) for v in zip(*a)]
def multiply(a,b): return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]
def determinant(a):
    a=[row[:] for row in a]; n=len(a); previous=1; sign=1
    for k in range(n-1):
        if a[k][k]==0:
            j=next((j for j in range(k+1,n) if a[j][k]), None)
            if j is None: return 0
            a[k],a[j]=a[j],a[k]; sign=-sign
        pivot=a[k][k]
        for i in range(k+1,n):
            for j in range(k+1,n):
                numerator=a[i][j]*pivot-a[i][k]*a[k][j]
                assert numerator%previous==0
                a[i][j]=numerator//previous
        for i in range(k+1,n): a[i][k]=0
        previous=pivot
    return sign*a[-1][-1]

X=[[2,1,0],[1,3,1],[0,1,2]]
Y=[[3,1,1],[1,4,0],[1,0,2]]
r=3; n=9
P=multiply(transpose(X),X); Q=multiply(Y,transpose(Y)); PQ=multiply(P,Q)
A=[[0]*n for _ in range(n)]
for i in range(r):
    for j in range(r): A[i][j+r]=X[i][j]; A[i+r][j+2*r]=Y[i][j]
AtA=multiply(transpose(A),A)
rows=[]
for t,zr,zi in [(1,0,0),(1,1,0),(2,2,0),(3,1,2),(5,-2,3)]:
    h=zr*zr+zi*zi; s=t+h
    # Gram matrix has real part A^T A - zr(A+A^T)+(h+t)I
    # and imaginary part zi(A-A^T).
    real=[[AtA[i][j]-zr*(A[i][j]+A[j][i])+(s if i==j else 0) for j in range(n)] for i in range(n)]
    imag=[[zi*(A[i][j]-A[j][i]) for j in range(n)] for i in range(n)]
    realified=[real[i]+[-v for v in imag[i]] for i in range(n)]+[imag[i]+real[i] for i in range(n)]
    rhs=[[s**3*(i==j)+s*t*(P[i][j]+Q[i][j])+t*PQ[i][j] for j in range(r)] for i in range(r)]
    lhs_real_det=determinant(realified); rhs_det=determinant(rhs)
    assert lhs_real_det==rhs_det**2 and rhs_det>0
    if zi==0: assert determinant(real)==rhs_det
    rows.append(dict(t=t,z_real=zr,z_imag=zi,determinant=rhs_det,realification_determinant=lhs_real_det,exact_pass=True))
out={'scope':'Five exact diagnostic evaluations of the all-parameter identity proved analytically in RESULT.md. These finite checks alone do not prove the theorem or exhibit the constant-rank fiber.', 'X':X,'Y':Y,'P':P,'Q':Q,'cases':rows}
p=Path(__file__).with_name('identity-check.json');p.write_text(json.dumps(out,indent=2)+'\n')
print('Exact integer identity diagnostics PASS:',len(rows),'cases including complex shifts; SHA256',hashlib.sha256(p.read_bytes()).hexdigest())
