"""Exact-rational linear algebra for recovered mathematical certificates."""
from __future__ import annotations
from fractions import Fraction as Q

def mat(rows):
    a=[[Q(v) for v in row] for row in rows]
    if not a or not a[0] or any(len(r)!=len(a[0]) for r in a):
        raise ValueError('Expected a nonempty rectangular matrix')
    return a

def eye(n): return [[Q(i==j) for j in range(n)] for i in range(n)]
def tr(a): return [list(r) for r in zip(*a)]
def dot(a,b):
    if len(a)!=len(b): raise ValueError('Dimension mismatch')
    return sum((x*y for x,y in zip(a,b)),Q(0))
def mv(a,b): return [dot(r,b) for r in a]
def mm(a,b): return [[dot(r,c) for c in tr(b)] for r in a]
def add(a,b):
    if len(a)!=len(b) or len(a[0])!=len(b[0]): raise ValueError('Dimension mismatch')
    return [[x+y for x,y in zip(r,s)] for r,s in zip(a,b)]
def scale(c,a): return [[Q(c)*v for v in r] for r in a]
def outer(a,b): return [[x*y for y in b] for x in a]
def sub(a,b):
    if len(a)!=len(b): raise ValueError('Dimension mismatch')
    return [x-y for x,y in zip(a,b)]
def solve(a,b):
    n=len(a)
    if any(len(r)!=n for r in a) or len(b)!=n: raise ValueError('Expected square system')
    c=[[Q(v) for v in row]+[Q(w)] for row,w in zip(a,b)]
    for k in range(n):
        p=next((i for i in range(k,n) if c[i][k]),None)
        if p is None: raise ValueError('Singular matrix')
        c[k],c[p]=c[p],c[k]; d=c[k][k]; c[k]=[v/d for v in c[k]]
        for i in range(n):
            if i!=k:
                d=c[i][k]; c[i]=[v-d*w for v,w in zip(c[i],c[k])]
    return [r[-1] for r in c]
def inv(a): return tr([solve(a,c) for c in tr(eye(len(a)))])
def det(a):
    n=len(a)
    if any(len(r)!=n for r in a): raise ValueError('Expected square matrix')
    b=mat(a); ans=Q(1)
    for k in range(n):
        p=next((i for i in range(k,n) if b[i][k]),None)
        if p is None: return Q(0)
        if p!=k: b[p],b[k]=b[k],b[p]; ans=-ans
        d=b[k][k]; ans*=d
        for i in range(k+1,n):
            q=b[i][k]/d
            for j in range(k+1,n): b[i][j]-=q*b[k][j]
    return ans
def principal_minors(a): return [det([r[:k] for r in a[:k]]) for k in range(1,len(a)+1)]
def norm_inf(a): return max(sum((abs(v) for v in r),Q(0)) for r in a)
def gepp(a,labels=None,steps=None):
    """GEPP; labels are original row indices. Every selected pivot is checked."""
    n=len(a)
    if any(len(r)!=n for r in a): raise ValueError('Expected square matrix')
    b=mat(a); ids=list(range(n)); maximum=max(abs(v) for r in b for v in r)
    if maximum==0: raise ValueError('Zero matrix')
    growth=maximum; trace=[]
    for k in range(n if steps is None else steps):
        value=max(abs(b[i][k]) for i in range(k,n))
        if not value: raise ValueError('Singular active column')
        p=ids.index(labels[k]) if labels is not None else max(range(k,n),key=lambda i:abs(b[i][k]))
        assert p>=k and abs(b[p][k])==value,(k,p,value)
        ids[k],ids[p]=ids[p],ids[k]; b[k],b[p]=b[p],b[k]
        trace.append({'stage':k+1,'original_row':ids[k]+1,'pivot':b[k][k]})
        for i in range(k+1,n):
            ell=b[i][k]/b[k][k]; assert abs(ell)<=1; b[i][k]=Q(0)
            for j in range(k+1,n):
                b[i][j]-=ell*b[k][j]; growth=max(growth,abs(b[i][j]))
    return growth/maximum,b,trace
def serial(x):
    if isinstance(x,Q): return str(x)
    if isinstance(x,dict): return {str(k):serial(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)): return [serial(v) for v in x]
    return x
