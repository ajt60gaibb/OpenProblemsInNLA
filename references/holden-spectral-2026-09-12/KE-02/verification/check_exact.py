#!/usr/bin/env python3
"""Exact diagnostic tests; the all-input proof is in ../proof.md."""
from __future__ import annotations
import random, sys
from fractions import Fraction as F
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from algorithm import diagonal_ramp, phase_toeplitz_perturbation

def require(condition, message):
    if not condition:
        raise ArithmeticError(message)

def mul(z,w):
    return (z[0]*w[0]-z[1]*w[1], z[0]*w[1]+z[1]*w[0])
def conj(z):
    return (z[0],-z[1])

def main():
    rng=random.Random(22020912)
    deltas=(F(1,8),F(499,1000),F(1,10**20))
    phases=((F(1),F(0)),(F(0),F(1)),(F(3,5),F(4,5)),(F(-5,13),F(12,13)))
    ramps=branches=gauges=0
    for n in range(2,65):
        for d in deltas:
            for t in ([F(0)]*n,[F(rng.randrange(-30,31),100) for _ in range(n)]):
                D=diagonal_ramp(t,d)
                y=sorted(t[i]+D[i] for i in range(n))
                require(max(map(abs,D))<=d,'ramp norm')
                require(min(y[i+1]-y[i] for i in range(n-1))>=2*d/(n-1),'sorted separation')
                eta=d/(2*(n-1))
                require(min(y[i+1]-y[i] for i in range(n-1))-2*eta>=d/(n-1),'boundary weak-coupling guarantee')
                ramps+=1
            for r in (F(0), d/(8*n), d/(4*n), d/(2*n), F(1,8), F(1,4)):
                upper=tuple((r*phases[j%4][0],r*phases[j%4][1]) for j in range(n-1))
                D,branch=phase_toeplitz_perturbation([F(1,7)]*n,upper,d)
                require(max(map(abs,D))<=d,'Toeplitz perturbation norm')
                require(F(1,7)+2*r<=1,'test matrix normalization by row-sum bound')
                if r<=d/(4*n):
                    require(branch=='weak','threshold equality/weak branch')
                    require(2*d/(n-1)-4*r>=d/n**3,'exact weak lower bound')
                else:
                    require(branch=='strong' and all(x==0 for x in D),'strong branch')
                    require(12*r/(n+1)**2>=d/n**3,'exact rational strong lower bound')
                require(d/n**3>=(d/n)**3,'canonical exponent conversion')
                branches+=1
                if r:
                    w=(F(1),F(0))
                    for b in upper:
                        tmp=mul(conj(b),w);wn=(tmp[0]/r,tmp[1]/r)
                        require(mul(conj(wn),wn)==(F(1),F(0)),'unit-modulus gauge')
                        require(mul(mul(conj(w),b),wn)==(r,F(0)),'gauge off diagonal')
                        gauges+=1;w=wn
    rejected=0
    for diag,up in (([0,1],[(1,0)]),([0,0,0],[(1,0),(2,0)])):
        try:
            phase_toeplitz_perturbation(diag,up,F(1,8))
        except ValueError:
            rejected+=1
    require(rejected==2,'invalid class rejection')
    print(f'PASS: {ramps} exact ramp tests, n=2..64; {branches} exact branch/bound tests including r=0 and threshold equality; {gauges} complex-rational gauge identities; 2 invalid-class rejections.')
    print('These are diagnostics. The universal theorem is the analytical proof, not a finite sample or numerical spectrum computation.')
if __name__=='__main__':main()
