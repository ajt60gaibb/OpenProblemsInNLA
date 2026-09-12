"""Supplementary exact polynomial checks; not a substitute for the all-n proof."""
from fractions import Fraction as Q
from functools import reduce
from itertools import permutations
from math import gcd,lcm
from pathlib import Path
import hashlib,json

def trim(a):
    a=list(a)
    while len(a)>1 and a[-1]==0:a.pop()
    return a or [0]
def add(a,b):return trim([(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0) for i in range(max(len(a),len(b)))])
def scale(a,c):return trim([c*x for x in a])
def sub(a,b):return add(a,scale(b,-1))
def mul(a,b):
    out=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):out[i+j]+=x*y
    return trim(out)
def deriv(a):return trim([i*a[i] for i in range(1,len(a))])
def div(a,b):
    a=[Q(x) for x in trim(a)];b=[Q(x) for x in trim(b)];out=[Q(0)]*max(1,len(a)-len(b)+1)
    while a!=[0] and len(a)>=len(b):
        k=len(a)-len(b);v=a[-1]/b[-1];out[k]+=v
        a=sub(a,[0]*k+scale(b,v))
    return trim(out),trim(a)
def exactdiv(a,b):
    q,r=div(a,b);assert r==[0]
    return [int(x) if x.denominator==1 else x for x in q]
def primitive(a):
    a=trim(a)
    den=reduce(lcm,(Q(x).denominator for x in a),1)
    a=[int(x*den) for x in a]
    g=reduce(gcd,(abs(x) for x in a),0)
    return [x//g for x in a] if g else [0]
def rem(a,b):
    a,b=primitive(a),primitive(b)
    while a!=[0] and len(a)>=len(b):
        k=len(a)-len(b)
        a=primitive(sub(scale(a,b[-1]),[0]*k+scale(b,a[-1])))
    return a
def coprime(a,b):
    a,b=primitive(a),primitive(b)
    while b!=[0]:a,b=b,rem(a,b)
    return len(a)==1
def det(matrix):
    n=len(matrix);out=[0]
    for p in permutations(range(n)):
        inv=sum(p[i]>p[j] for i in range(n) for j in range(i+1,n))
        term=[(-1)**inv]
        for i,j in enumerate(p):term=mul(term,matrix[i][j])
        out=add(out,term)
    return out
def sylvester(p,e):
    zero=[0];rows=[]
    for i in range(3):rows.append([zero]*i+p+[zero]*(2-i))
    for i in range(2):rows.append([zero]*i+e+[zero]*(1-i))
    return det(rows)
def specialize(coeffs,z):
    out=[0]
    for c in coeffs:out=add(scale(out,z),c)
    return out

def check(m):
    d=[10*(i+1) for i in range(m)];b=[1]*m;c=[2]*m
    f=[1]
    for x in d:f=mul(f,[-x*x,1])
    fi=[exactdiv(f,[-x*x,1]) for x in d]
    Fb=list(f);Fc=list(f);g=[0]
    for x,y,z,part in zip(d,b,c,fi):
        Fb=sub(Fb,scale(part,y*y));Fc=sub(Fc,scale(part,z*z));g=add(g,scale(part,x*y*z))
    Delta=mul([0,1],mul(Fb,Fc));h=exactdiv(sub(Delta,mul(g,g)),f)
    alpha=sub(add(mul(mul(f,f),sub(deriv(h),f)),scale(mul(mul(f,g),deriv(g)),4)),
              add(mul(mul(f,deriv(f)),h),scale(mul(deriv(f),mul(g,g)),4)))
    beta=add(sub(scale(mul(mul(f,f),g),-1),scale(mul(mul(f,deriv(g)),h),2)),scale(mul(mul(deriv(f),g),h),2))
    numerator=sub(add(mul(h,mul(alpha,alpha)),scale(mul(g,mul(alpha,beta)),2)),mul(f,mul(beta,beta)))
    R=exactdiv(numerator,mul(f,f))
    p=[scale(f,-1),scale(g,-2),h]
    e=[scale(deriv(f),-1),scale(deriv(g),-2),sub(deriv(h),f),scale(g,-1)]
    assert R==sylvester(p,e),'Independent Sylvester determinant disagrees'
    assert len(R)-1==5*m-2
    assert len(alpha)-1<=3*m-2 and len(beta)-1==3*m-1
    assert R[-1]==-sum(d[i]*b[i]*c[i] for i in range(m))**2
    assert coprime(Delta,deriv(Delta)) and coprime(f,g) and coprime(g,h)
    assert coprime(R,f) and R[0]!=0 and coprime(R,deriv(R))
    zstar=sum(Q(b[i]*c[i],d[i]) for i in range(m))
    no_singular=coprime(specialize(p,zstar),specialize(e,zstar))
    assert no_singular if m>=2 else not no_singular
    for z in [0,1,-2]:
        A=[[z]+b]+[[c[i]]+[d[i] if i==j else 0 for j in range(m)] for i in range(m)]
        M=[[sum(A[i][k]*A[j][k] for k in range(m+1)) for j in range(m+1)] for i in range(m+1)]
        char=[[[-M[i][j],1] if i==j else [-M[i][j]] for j in range(m+1)] for i in range(m+1)]
        assert det(char)==specialize(p,z),'Direct characteristic determinant disagrees'
    return {'n':m+1,'eliminant_degree':len(R)-1,'squarefree':True,'no_f_or_zero_root':True,
            'singular_completion_excluded':no_singular,'spectral_identity_directly_checked_at_z':[0,1,-2],
            'independent_sylvester_identity':True,'data':{'d':d,'b':b,'c':c},
            'eliminant_coefficients_ascending':R}

out={'result':'PASS','scope':'Finite exact supplemental checks only; universal proof in reviewed-proof.md',
     'proof_sha256':hashlib.sha256(Path(__file__).with_name('reviewed-proof.md').read_bytes()).hexdigest(),
     'cases':[check(m) for m in range(1,6)]}
Path(__file__).with_name('exact-check.json').write_text(json.dumps(out,indent=2)+'\n')
print([(x['n'],x['eliminant_degree'],x['singular_completion_excluded']) for x in out['cases']])
