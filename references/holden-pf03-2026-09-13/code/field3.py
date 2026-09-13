"""Exact Q(cuberoot(2)) arithmetic and rational interval sign certificates.

Only Python's standard library is used.  No floating point is used in proofs.
Elements are stored in the basis (1, a, a**2), with a**3 = 2.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as F
from typing import Iterable, Union

if not __debug__:
    raise RuntimeError('Run this certificate checker without Python -O or -OO.')

Scalar = Union[int, F, 'E']

@dataclass(frozen=True)
class E:
    c0: F = F(0)
    c1: F = F(0)
    c2: F = F(0)

    def __post_init__(self):
        for name in ('c0', 'c1', 'c2'):
            object.__setattr__(self, name, F(getattr(self, name)))

    @classmethod
    def coerce(cls, x: Scalar) -> E:
        return x if isinstance(x, cls) else cls(F(x))

    @classmethod
    def decode(cls, x: list[str]) -> E:
        if len(x) != 3:
            raise ValueError('Expected three rational coefficients')
        return cls(*(F(z) for z in x))

    def encode(self) -> list[str]:
        return [str(self.c0), str(self.c1), str(self.c2)]

    def __add__(self, other: Scalar) -> E:
        y = E.coerce(other)
        return E(self.c0+y.c0, self.c1+y.c1, self.c2+y.c2)
    __radd__ = __add__

    def __neg__(self) -> E:
        return E(-self.c0, -self.c1, -self.c2)

    def __sub__(self, other: Scalar) -> E:
        return self + (-E.coerce(other))

    def __rsub__(self, other: Scalar) -> E:
        return E.coerce(other) - self

    def __mul__(self, other: Scalar) -> E:
        y = E.coerce(other)
        a,b,c = self.c0,self.c1,self.c2
        d,e,f = y.c0,y.c1,y.c2
        return E(a*d+2*(b*f+c*e), a*e+b*d+2*c*f, a*f+b*e+c*d)
    __rmul__ = __mul__

    def inverse(self) -> E:
        if self == ZERO:
            raise ZeroDivisionError('Zero field element')
        a,b,c = self.c0,self.c1,self.c2
        # Adjugate of multiplication by this element, first column.
        x = a*a-2*b*c
        y = 2*c*c-a*b
        z = b*b-a*c
        den = a*x+2*c*y+2*b*z
        if den == 0:
            raise ArithmeticError('The defining polynomial must be irreducible')
        return E(x/den,y/den,z/den)

    def __truediv__(self, other: Scalar) -> E:
        return self * E.coerce(other).inverse()

    def __rtruediv__(self, other: Scalar) -> E:
        return E.coerce(other) / self

    def __pow__(self, n: int) -> E:
        if not isinstance(n,int):
            return NotImplemented
        if n < 0:
            return self.inverse() ** (-n)
        result, base = ONE, self
        while n:
            if n & 1:
                result = result * base
            base = base * base
            n >>= 1
        return result

    def rational(self) -> F:
        if self.c1 or self.c2:
            raise ValueError('Not a rational element')
        return self.c0

    def interval(self, isolation: tuple[F,F]) -> tuple[F,F]:
        lo,hi = isolation
        # Horner evaluation, using signed interval multiplication.
        a,b = min(self.c2*lo,self.c2*hi),max(self.c2*lo,self.c2*hi)
        a,b = a+self.c1,b+self.c1
        products = (a*lo,a*hi,b*lo,b*hi)
        return min(products)+self.c0,max(products)+self.c0

ZERO, ONE, ALPHA = E(), E(1), E(0,1,0)

def isolate_alpha(digits: int = 40) -> tuple[F,F]:
    """An exact isolating interval of width 10**(-digits)."""
    if digits < 1:
        raise ValueError('digits must be positive')
    scale = 10**digits
    target = 2*scale**3
    lo,hi = scale,2*scale
    while hi-lo > 1:
        mid = (lo+hi)//2
        if mid**3 < target:
            lo = mid
        else:
            hi = mid
    result = F(lo,scale),F(hi,scale)
    assert result[0]**3 < 2 < result[1]**3
    return result

def positive(x: E, isolation: tuple[F,F]) -> bool:
    return x.interval(isolation)[0] > 0

def mat_decode(a: list) -> list[list[E]]:
    if not a or any(len(r) != len(a[0]) for r in a):
        raise ValueError('Nonempty rectangular matrix required')
    return [[E.decode(x) for x in r] for r in a]

def mat_encode(a: list[list[E]]) -> list:
    return [[x.encode() for x in row] for row in a]

def transpose(a):
    return [list(row) for row in zip(*a)]

def multiply(a,b):
    if len(a[0]) != len(b):
        raise ValueError('Incompatible matrix shapes')
    return [[sum((x*y for x,y in zip(row,col)), ZERO)
             for col in zip(*b)] for row in a]

def add(a,b):
    return [[x+y for x,y in zip(r,s)] for r,s in zip(a,b)]

def subtract(a,b):
    return [[x-y for x,y in zip(r,s)] for r,s in zip(a,b)]

def identity(n):
    return [[ONE if i == j else ZERO for j in range(n)] for i in range(n)]

def rational_rank(a: list[list[F]]) -> int:
    m = [row[:] for row in a]
    rank = 0
    for j in range(len(m[0])):
        pivot = next((i for i in range(rank,len(m)) if m[i][j]),None)
        if pivot is None:
            continue
        m[rank],m[pivot] = m[pivot],m[rank]
        value=m[rank][j]
        m[rank] = [x/value for x in m[rank]]
        for i in range(rank+1,len(m)):
            if m[i][j]:
                t=m[i][j]
                m[i]=[x-t*y for x,y in zip(m[i],m[rank])]
        rank += 1
        if rank == len(m):
            break
    return rank

def field_rref(a: list[list[E]]) -> tuple[list[list[E]],list[int]]:
    """Gauss-Jordan elimination over the exact cubic field."""
    if not a or any(len(r)!=len(a[0]) for r in a):
        raise ValueError('Nonempty rectangular matrix required')
    m=[[E.coerce(x) for x in row] for row in a]
    rank=0;pivots=[]
    for j in range(len(m[0])):
        pivot=next((i for i in range(rank,len(m)) if m[i][j]!=ZERO),None)
        if pivot is None:
            continue
        m[rank],m[pivot]=m[pivot],m[rank]
        inv=m[rank][j].inverse()
        m[rank]=[x*inv for x in m[rank]]
        for i in range(len(m)):
            if i!=rank and m[i][j]!=ZERO:
                t=m[i][j]
                m[i]=[x-t*y for x,y in zip(m[i],m[rank])]
        pivots.append(j);rank+=1
        if rank==len(m):
            break
    return m,pivots

def field_inverse(a: list[list[E]]) -> list[list[E]]:
    n=len(a)
    if not n or any(len(r)!=n for r in a):
        raise ValueError('Nonempty square matrix required')
    I=identity(n)
    rr,pivots=field_rref([row+ir for row,ir in zip(a,I)])
    if pivots!=list(range(n)) or [row[:n] for row in rr]!=I:
        raise ArithmeticError('Singular matrix')
    return [row[n:] for row in rr]
