#!/usr/bin/env python3
"""Illustrative floating-point evaluation of the row-deletion constants.

Not a proof certificate. Uses only the Python standard library.
"""
from __future__ import annotations
import argparse,json,math
from statistics import NormalDist

def constants(theta:float)->dict:
    if not math.isfinite(theta) or not 0<theta<1:
        raise ValueError('theta must be finite and strictly between zero and one')
    probability=(1+theta)/2
    if probability>=1:
        raise ValueError('theta is too close to one for this floating-point utility')
    a=NormalDist().inv_cdf(probability)
    density=math.exp(-a*a/2)/math.sqrt(2*math.pi)
    h=theta-2*a*density
    if h<=0:
        raise ValueError('Cancellation at this theta prevents a reliable positive value; use higher precision')
    return {'theta':theta,'a_theta':a,'h_theta':h,'c_theta':math.sqrt(h),
            'arithmetic':'floating point; illustrative only'}

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('theta',type=float,nargs='?',default=0.5)
    args=p.parse_args()
    try: print(json.dumps(constants(args.theta),indent=2))
    except ValueError as error: p.error(str(error))
