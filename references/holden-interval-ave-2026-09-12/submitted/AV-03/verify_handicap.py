#!/usr/bin/env python3
"""Exact rational checks accompanying optimized_handicap.md.
Finite tests are regression checks, not a substitute for its all-x proof.
"""
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import json, random

def products(a,x,d=(Q(1),Q(1),Q(1))):
    return [d[i]*x[i]*(x[i]+a*x[(i+1)%3]) for i in range(3)]

def margin(a,x):
    c=max(Q(1),a*a/4);v=products(a,x)
    return c*sum(w for w in v if w>0)+sum(w for w in v if w<0)

def run():
    rng=random.Random(20260912)
    params=[Q(0),Q(1,10),Q(1),Q(199,100),Q(2),Q(201,100),Q(5,2),Q(3),Q(4),Q(7),Q(64),Q(2**40)]
    count=0
    for a in params:
        for x0 in product(range(-3,4),repeat=3):
            x=list(map(Q,x0));assert margin(a,x)>=0;count+=1
        for _ in range(500):
            x=[Q(rng.randint(-100,100),rng.randint(1,40)) for _ in range(3)]
            assert margin(a,x)>=0;count+=1
        if a>=2:
            x=[Q(1),-2/a,Q(0)]
            assert margin(a,x)==0
        if a>0:
            for _ in range(20):
                d=[Q(rng.randint(1,100),rng.randint(1,100)) for _ in range(3)]
                v=products(a,[Q(1),-2/a,Q(0)],d)
                assert v==[-d[0],4*d[1]/(a*a),Q(0)]
                assert (d[0]/d[1])*(d[1]/d[2])*(d[2]/d[0])==1
    out={'exact_rational_margin_checks':count,'parameters':[str(a) for a in params],
         'sharp_witnesses_verified':True,'row_scaling_witnesses_verified':True,
         'result':'All passed; universal validity rests on optimized_handicap.md'}
    Path(__file__).with_name('handicap_test_results.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
if __name__=='__main__':run()
