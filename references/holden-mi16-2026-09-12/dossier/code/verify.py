#!/usr/bin/env python3
"""Run exact, reproducible checks of the paper. These checks supplement proofs."""
from __future__ import annotations
from collections import Counter
from fractions import Fraction as Q
from itertools import product
from math import factorial, comb
from pathlib import Path
import json, random, sys, time
import sympy as sp
from critical_values import permanent, critical_polynomial
from one_exceptional import support_value, exceptional_maximum, transition_polynomial, transition_interval
from spectral_moments import (partitions,character,specht_dimension,exact_moment,
                              schur_value,moment_weights)

counts=Counter()
records={}
start=time.monotonic()
def check(condition,label):
    if not condition:
        raise AssertionError(label)
    counts[label]+=1

def compositions(total,parts):
    if parts==1:
        yield (total,)
    else:
        for first in range(total+1):
            for rest in compositions(total-first,parts-1):
                yield (first,)+rest

def simplex_objective(t,x):
    e=[Q(1)]+[Q(0)]*len(t)
    for v in t:
        for j in range(len(t),0,-1):
            e[j]+=v*e[j-1]
    return sum(Q(factorial(j))*(-x)**j*e[j] for j in range(len(e)))

# Gaussian-rational Hermitian matrices; no square-root normalization required.
rng=random.Random(16162026)
for n in range(1,7):
    for trial in range(5):
        v=sp.Matrix([rng.randint(-2,2)+sp.I*rng.randint(-2,2) for _ in range(n)])
        if not any(v):v[0]=1
        norm=sp.expand((sp.conjugate(v).T*v)[0])
        alpha,beta=sp.Rational(rng.randint(0,4),2),sp.Rational(rng.randint(0,4),2)
        h=beta*sp.eye(n)+(alpha-beta)*(v*sp.conjugate(v).T)/norm
        ts=[Q(sp.expand(sp.conjugate(w)*w)/norm) for w in v]
        # Full unnormalized elementary-symmetric expression.
        es=[sp.S.One]+[sp.S.Zero]*n
        for t in ts:
            for j in range(n,0,-1):es[j]+=sp.Rational(t)*es[j-1]
        formula=sum(sp.factorial(j)*beta**(n-j)*(alpha-beta)**j*es[j] for j in range(n+1))
        check(sp.simplify(permanent(h)-formula)==0,'complex_exact_permanent_identity')

# Support reduction checked against all k, including positive perturbations.
for x in [Q(j,20) for j in range(21)]+[Q(-1,4),Q(-1),Q(-3)]:
    vals=[]
    for k in range(1,61):
        # alpha may exceed beta, but remains nonnegative for every listed x.
        vals.append(support_value(k,k,1-x,1))
        if k>=2:
            check(max(vals)==max(vals[1],vals[-1]),'two_or_n_support_comparisons')

# Exact rational simplex grids, including equality classification.
for n,denom in [(3,18),(4,12),(5,10)]:
    for x in [Q(1,4),Q(1,2),Q(2,3),Q(3,4),Q(9,10),Q(1)]:
        optimum=exceptional_maximum(n,1-x,1)
        for nums in compositions(denom,n):
            ts=tuple(Q(v,denom) for v in nums)
            value=simplex_objective(ts,x)
            check(value<=optimum['maximum'],'rational_simplex_grid_upper_checks')
            if value==optimum['maximum']:
                positive=[v for v in ts if v]
                check(len(set(positive))==1 and len(positive) in optimum['supports'],
                      'rational_grid_equality_checks')

x,eps=sp.symbols('x eps')
for k in range(3,21):
    integral_poly=sum(sp.binomial(k-1,j)*(-x/sp.Integer(k))**j*sp.factorial(j+2)
                      for j in range(k))
    for value in [0,sp.Rational(1,3),sp.Rational(2,3),1]:
        check(integral_poly.subs(x,value)>0,'activation_integral_positivity_samples')
    if k<=10:
        path=0
        for j in range(k+2):
            ej=sp.binomial(k,j)*((1-eps)/k)**j
            if j:
                ej+=eps*sp.binomial(k,j-1)*((1-eps)/k)**(j-1)
            path+=sp.factorial(j)*(-x)**j*ej
        check(sp.expand(sp.diff(path,eps).subs(eps,0)-x*x*integral_poly/k)==0,
              'activation_derivative_polynomial_identity')
    moments=[sp.S.One,sp.Integer(k-3)]
    for j in range(1,k):
        moments.append((k-3-j)*moments[j]+k*j*moments[j-1])
    for j,mu in enumerate(moments):
        direct=sum(sp.binomial(j,r)*k**(j-r)*(-1)**r*sp.factorial(r+2)/2
                   for r in range(j+1))
        check(mu==direct,'gamma_moment_recurrence')
    if k>=5:
        rhs=k*(moments[k-4]+k*(k-2)*(k-4)*moments[k-5])
        check(moments[k-1]==rhs,'endpoint_moment_identity')

thresholds=[]
previous=0
for n in range(3,21):
    g=transition_polynomial(n).as_expr()*x*x
    fn=g+1-x+x*x/2
    check(sp.expand(x*x*sp.diff(fn,x)-n*((1+x)*fn-1))==0,'support_ODE_identity')
    check(sp.expand(x*x*sp.diff(g,x)-n*(1+x)*g-sp.Rational(n-2,2)*x*x*(x-1))==0,
          'transition_ODE_identity')
    lo,hi=transition_interval(n,18)
    check(lo>previous,'thresholds_strictly_increasing')
    previous=hi
    thresholds.append({'n':n,'polynomial':str(transition_polynomial(n).as_expr()),
                       'interval':[str(lo),str(hi)],'decimal':str(sp.N((lo+hi)/2,19))})
records['thresholds']=thresholds

# Independent character-table orthogonality and hook-length dimensions.
for m in range(1,9):
    shapes=partitions(m)
    check(sum(specht_dimension(s)**2 for s in shapes)==factorial(m),'Specht_dimension_sum')
    for shape in shapes:
        check(character(shape,(1,)*m)==specht_dimension(shape),'character_at_identity')
    for a in shapes:
        for b in shapes:
            inner=0
            for cycles in shapes:
                multiplicity=Counter(cycles)
                centralizer=sp.prod(length**count*factorial(count) for length,count in multiplicity.items())
                inner+=sp.Rational(character(a,cycles)*character(b,cycles),centralizer)
            check(inner==int(a==b),'character_orthogonality')

moment_cases=[(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(3,3),(4,1),(4,2)]
weights=[]
for n,p in moment_cases:
    ww=moment_weights(n,p)
    weights.append({'n':n,'p':p,'weights':[[list(s),str(w)] for s,w in ww]})
    check(sum(w for s,w in ww)==1 and all(w>=0 for s,w in ww),'moment_projector_weights')
    check(exact_moment([2]*n,p)==2**(n*p),'scalar_spectrum_moments')
    expected=sp.Rational(factorial(n)**p*factorial(n-1)*factorial(p)**n,factorial(n*p+n-1))
    check(exact_moment([1]+[0]*(n-1),p)==expected,'rank_one_Dirichlet_moments')
for a,b in [(0,1),(1,3),(sp.Rational(1,2),sp.Rational(5,3)),(2,2)]:
    maximum=(sp.Rational(a)**2+sp.Rational(b)**2)/2
    gap=(sp.Rational(a)-sp.Rational(b))**2/2
    for p in range(1,5):
        direct=sum(sp.binomial(p,j)*maximum**(p-j)*(-gap)**j/(2*j+1) for j in range(p+1))
        check(exact_moment([a,b],p)==direct,'two_dimensional_direct_moments')
records['moment_weights']=weights
records['mixed_spectrum_moments']=[{'spectrum':[0,1,2], 'p':p,
                                   'value':str(exact_moment([0,1,2],p))} for p in range(1,4)]

elimination=[]
z=sp.Symbol('z')
for lam in [(0,),(2,),(0,0),(1,1),(0,1),(1,3),(sp.Rational(1,2),sp.Rational(5,3)),(0,0,0),(2,2,2)]:
    poly=critical_polynomial(lam)
    if len(set(lam))==1:
        expected=z-lam[0]**len(lam)
    else:
        a,b=lam
        expected=(z-a*b)*(z-(a*a+b*b)/2)
    check(sp.expand(poly.as_expr()-sp.Poly(expected,z).monic().as_expr())==0,'critical_value_elimination')
    elimination.append({'spectrum':list(map(str,lam)),'polynomial':str(poly.as_expr())})
records['elimination_cases']=elimination

# Exact arithmetic underlying the finite moment-order bound.
for n in range(1,9):
    for ratio in [Q(1),Q(2),Q(17,3),Q(100)]: # ratio = B / lower gap
        base=1+16*n*n*ratio
        bits=0
        while 2**bits<base:bits+=1
        h=(4*ratio.numerator+ratio.denominator-1)//ratio.denominator
        p=2*n*n*bits*h
        t=1/(4*ratio)
        # Bernoulli block bound proves the full power comparison without huge powers.
        check(1+h*t>=2 and 2**bits>=base and p>0,'finite_moment_order_arithmetic')

output={'status':'PASS','seed':16162026,'check_counts':dict(counts),
        'total_checks':sum(counts.values()),'elapsed_seconds':round(time.monotonic()-start,3),
        'sympy_version':sp.__version__,**records}
path=Path(__file__).resolve().parents[1]/'verification'/'exact_checks.json'
path.write_text(json.dumps(output,indent=2)+'\n')
print(json.dumps({k:output[k] for k in ['status','total_checks','check_counts','elapsed_seconds','sympy_version']},indent=2))
