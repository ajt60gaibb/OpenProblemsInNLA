"""Exact integer cone facets; no numerical or third-party dependencies."""
from fractions import Fraction as F
from functools import reduce
from math import gcd,lcm


def primitive(row):
    """Divide an integer row by the positive gcd, preserving its orientation."""
    row=tuple(int(x) for x in row)
    g=reduce(gcd,row,0)
    return row if not g else tuple(x//g for x in row)


def null_normal(rows):
    """Primitive integer null vector of an m by (m+1) full-rank matrix.

    Bareiss fraction-free elimination with row and column pivoting is followed
    by exact integer back substitution.  Return None if the row rank is < m.
    Every division is checked for zero remainder.
    """
    if not rows or any(len(row)!=len(rows)+1 for row in rows):
        raise ValueError('Expected m rows and m+1 columns')
    original=[list(map(int,row)) for row in rows]
    a=[row[:] for row in original]
    m=len(a);n=m+1
    perm=list(range(n));previous=1
    for k in range(m):
        pivot=next(((i,j) for j in range(k,n) for i in range(k,m) if a[i][j]),None)
        if pivot is None:
            return None
        i,j=pivot
        if i!=k:
            a[k],a[i]=a[i],a[k]
        if j!=k:
            for row in a:
                row[k],row[j]=row[j],row[k]
            perm[k],perm[j]=perm[j],perm[k]
        p=a[k][k]
        if k<m-1:
            for i in range(k+1,m):
                aik=a[i][k]
                for j in range(k+1,n):
                    numerator=p*a[i][j]-aik*a[k][j]
                    quotient,remainder=divmod(numerator,previous)
                    if remainder:
                        raise ArithmeticError('Inexact Bareiss division')
                    a[i][j]=quotient
                a[i][k]=0
            previous=p
    x=[0]*n;x[-1]=a[m-1][m-1]
    for k in range(m-1,-1,-1):
        numerator=-sum(a[k][j]*x[j] for j in range(k+1,n))
        quotient,remainder=divmod(numerator,a[k][k])
        if remainder:
            raise ArithmeticError('Inexact adjugate back substitution')
        x[k]=quotient
    result=[0]*n
    for j,value in enumerate(x):
        result[perm[j]]=value
    result=primitive(result)
    assert any(result)
    assert all(sum(x*y for x,y in zip(row,result))==0 for row in original)
    return result


def integer_columns(d):
    """Positive primitive integer multiples of the rational generator columns."""
    V=[[F(x) for x in row] for row in d['generators']]
    rays=[]
    for col in zip(*V):
        denominator=reduce(lcm,[x.denominator for x in col],1)
        rays.append(primitive([x.numerator*(denominator//x.denominator) for x in col]))
    return rays
