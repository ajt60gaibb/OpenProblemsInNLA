"""Small exact rational linear algebra. Standard library only; no floating point.

This is a certificate checker, not a formal proof-assistant kernel. Matrices are
lists of lists of fractions.Fraction. Intended sizes are at most 12 by 12.
"""
from fractions import Fraction as F
from itertools import combinations
from typing import Sequence

Matrix = list[list[F]]

def mat(rows: Sequence[Sequence]) -> Matrix:
    a = [[F(x) for x in row] for row in rows]
    if not a or not a[0] or any(len(row) != len(a[0]) for row in a):
        raise ValueError("Expected a nonempty rectangular matrix")
    return a

def eye(n: int) -> Matrix:
    return [[F(i == j) for j in range(n)] for i in range(n)]

def diag(values: Sequence) -> Matrix:
    return [[F(values[i]) if i == j else F(0) for j in range(len(values))]
            for i in range(len(values))]

def trans(a: Matrix) -> Matrix:
    return [list(row) for row in zip(*a)]

def add(a: Matrix, b: Matrix) -> Matrix:
    if len(a) != len(b) or len(a[0]) != len(b[0]):
        raise ValueError("Matrix addition dimension mismatch")
    return [[x+y for x,y in zip(ar,br)] for ar,br in zip(a,b)]

def scale(c, a: Matrix) -> Matrix:
    c=F(c)
    return [[c*x for x in row] for row in a]

def sub(a: Matrix, b: Matrix) -> Matrix:
    return add(a,scale(-1,b))

def mul(a: Matrix, b: Matrix) -> Matrix:
    if len(a[0]) != len(b):
        raise ValueError("Matrix multiplication dimension mismatch")
    bt=trans(b)
    return [[sum((x*y for x,y in zip(row,col)),F(0)) for col in bt] for row in a]

def power(a: Matrix, k: int) -> Matrix:
    if not isinstance(k,int) or k<0 or len(a)!=len(a[0]):
        raise ValueError("Nonnegative integer power of a square matrix required")
    r=eye(len(a));b=a
    while k:
        if k&1:r=mul(r,b)
        b=mul(b,b);k//=2
    return r

def det(a: Matrix) -> F:
    if len(a)!=len(a[0]):raise ValueError("Square matrix required")
    a=[row[:] for row in a];n=len(a);result=F(1)
    for j in range(n):
        p=next((i for i in range(j,n) if a[i][j]),None)
        if p is None:return F(0)
        if p!=j:a[j],a[p]=a[p],a[j];result=-result
        pivot=a[j][j];result*=pivot
        for i in range(j+1,n):
            c=a[i][j]/pivot
            for k in range(j+1,n):a[i][k]-=c*a[j][k]
            a[i][j]=F(0)
    return result

def principal(a: Matrix, indices: Sequence[int]) -> Matrix:
    return [[a[i][j] for j in indices] for i in indices]

def leading_minors(a: Matrix) -> list[F]:
    return [det(principal(a,range(k))) for k in range(1,len(a)+1)]

def positive_definite(a: Matrix) -> bool:
    return a==trans(a) and all(d>0 for d in leading_minors(a))

def positive_semidefinite(a: Matrix) -> bool:
    return a==trans(a) and all(det(principal(a,ss))>=0
        for k in range(1,len(a)+1) for ss in combinations(range(len(a)),k))

def frobenius_squared(a: Matrix) -> F:
    return sum((x*x for row in a for x in row),F(0))

def trace(a: Matrix) -> F:
    return sum((a[i][i] for i in range(len(a))),F(0))

def characteristic_coefficients(a: Matrix) -> list[F]:
    """Coefficients of det(x I - a), in descending powers."""
    n=len(a)
    return [F(1)]+[(-1)**k*sum((det(principal(a,ss))
             for ss in combinations(range(n),k)),F(0)) for k in range(1,n+1)]

def polynomial_from_roots(roots: Sequence) -> list[F]:
    p=[F(1)]
    for r in map(F,roots):
        q=[F(0)]*(len(p)+1)
        for i,c in enumerate(p):q[i]+=c;q[i+1]-=r*c
        p=q
    return p
