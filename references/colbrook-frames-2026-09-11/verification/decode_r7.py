#!/usr/bin/env python3
"""A quartic-based decoder for the twelve measurements on R^7.

The exact-arithmetic decoder in the manuscript considers at most four complex
candidates, plus explicit zero-coordinate branches. This implementation uses
floating-point polynomial roots and optional least-squares polishing. It checks
the final measurement residual and raises an error rather than silently claiming
success. It is intended for noiseless/roundoff-level data, not arbitrary noisy
measurements; a uniform floating-point accuracy theorem is not claimed.

Usage:
  python decode_r7.py --self-test --out decoder_verification.json
  python decode_r7.py --measurements '[12 real numbers]'
Requires numpy and scipy. No network access is used.
"""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import numpy as np
from numpy.polynomial import Polynomial as Poly
from scipy.optimize import least_squares

B=5/12


def measurements(x: np.ndarray) -> np.ndarray:
    x=np.asarray(x,dtype=float)
    if x.shape!=(7,) or not np.all(np.isfinite(x)):
        raise ValueError('x must contain seven finite real numbers')
    a0=5*(x[0]+1j*x[1]);a1=12*(x[2]+1j*x[3]);a3=12*(x[4]+1j*x[5])
    a2=(9-2j)*x[6]-(x[0]+1j*x[1])-(x[2]+1j*x[3])
    q=np.array([a0*a0,2*a0*a1+B*a3.conjugate()**2,
                a1*a1+2*a0*a2-a3.conjugate()**2,
                2*(a0*a3+a1*a2),a2*a2+2*a1*a3,2*a2*a3+B*a3*a3])
    return np.column_stack((q.real,q.imag)).ravel()


def coordinates(a0: complex,a1: complex,a2: complex,a3: complex) -> np.ndarray:
    # An exact candidate must satisfy Im((9+2i)L0)=0. Projection to coordinates
    # is used only to prepare a residual-checked floating-point candidate.
    L0=a2+a1/12+a0/5
    return np.array([a0.real/5,a0.imag/5,a1.real/12,a1.imag/12,
                     a3.real/12,a3.imag/12,L0.real/9],dtype=float)


def decode(y: np.ndarray,rtol: float=1e-9,polish: bool=True) -> dict:
    y=np.asarray(y,dtype=float)
    if y.shape!=(12,) or not np.all(np.isfinite(y)):
        raise ValueError('Measurements must contain twelve finite real numbers')
    if not (0<rtol<1): raise ValueError('rtol must lie strictly between zero and one')
    # Scaling by the largest component avoids overflow/underflow in ||y||_2
    # before normalization, even when finite nonzero measurements are tiny.
    scale=float(np.max(np.abs(y)))
    if scale==0:
        return {'x':np.zeros(7),'relative_residual':0.,'branch':'zero','candidates':1}
    # Homogeneity keeps root coefficients and reconstruction magnitudes moderate.
    target=y/scale
    target_norm=float(np.linalg.norm(target))
    q=target[::2]+1j*target[1::2]
    candidates=[]
    if q[0]!=0:
        a0=np.sqrt(q[0]+0j)
        u=Poly([0j,1+0j])
        a1=(Poly([q[1]])-B*u)/(2*a0)
        a2=(Poly([q[2]])+u-a1*a1)/(2*a0)
        a3=(Poly([q[3]])-2*a1*a2)/(2*a0)
        polynomial=a2*a2+2*a1*a3-Poly([q[4]])
        if len(polynomial.coef)!=5 or polynomial.coef[-1]==0:
            raise FloatingPointError('Quartic leading coefficient was lost numerically')
        for root in polynomial.roots():
            vals=(a0,complex(a1(root)),complex(a2(root)),complex(a3(root)))
            x=coordinates(*vals)
            if np.all(np.isfinite(x)): candidates.append(x)
        branch='quartic'
    elif q[1]!=0:
        a3=np.sqrt(q[1].conjugate()/B+0j)
        a2=(q[5]-B*a3*a3)/(2*a3)
        a1=(q[4]-a2*a2)/(2*a3)
        candidates=[coordinates(0j,a1,a2,a3)];branch='a0=0,a3!=0'
    elif q[2]!=0:
        a1=np.sqrt(q[2]+0j);a2=q[3]/(2*a1)
        candidates=[coordinates(0j,a1,a2,0j)];branch='a0=a3=0,a1!=0'
    else:
        a2=np.sqrt(q[4]+0j)
        candidates=[coordinates(0j,0j,a2,0j)];branch='only a2 possibly nonzero'
    best=None
    for x in candidates:
        initial=float(np.linalg.norm(measurements(x)-target)/target_norm)
        if polish and initial>rtol/10:
            res=least_squares(lambda z:measurements(z)-target,x,
                              max_nfev=500,ftol=1e-13,xtol=1e-13,gtol=1e-13)
            x=res.x
        residual=float(np.linalg.norm(measurements(x)-target)/target_norm)
        if best is None or residual<best[0]:best=(residual,x)
    if best is None or best[0]>rtol:
        residual=None if best is None else best[0]
        raise RuntimeError(f'No residual-verified reconstruction; best relative residual={residual}. '
                           'Data may be inconsistent, or higher-precision roots may be required.')
    signal_scale=np.sqrt(scale)
    recovered=best[1]*signal_scale
    if not np.all(np.isfinite(recovered)):
        raise FloatingPointError('Reconstructed signal is not finite')
    # Verify the returned, rescaled signal without squaring its possibly huge
    # coordinates directly. Quadratic homogeneity preserves this residual.
    final_residual=float(np.linalg.norm(measurements(recovered/signal_scale)-target)/target_norm)
    if not np.isfinite(final_residual) or final_residual>rtol:
        raise RuntimeError(f'Rescaled reconstruction failed its relative residual check: {final_residual}')
    return {'x':recovered,'relative_residual':final_residual,
            'branch':branch,'candidates':len(candidates)}


def self_test(seed: int,count: int) -> dict:
    rng=np.random.default_rng(seed);records=[]
    vectors=[rng.normal(size=7) for _ in range(count)]
    for _ in range(20):
        x=rng.normal(size=7);x[:2]=0;vectors.append(x)
        x=rng.normal(size=7);x[[0,1,4,5]]=0;vectors.append(x)
        x=np.zeros(7);x[6]=rng.normal();vectors.append(x)
    vectors.append(np.zeros(7))
    # Scale invariance is tested separately, without changing the exact branch.
    vectors.extend([10.**p*rng.normal(size=7) for p in [-150,-90,-6,-3,3,6,80,150]])
    for power in [-150,-90,80,150]:
        x=np.zeros(7);x[6]=10.**power;vectors.append(x)
    failures=[];max_error=0.;max_residual=0.;branches={}
    for j,x in enumerate(vectors):
        try:
            result=decode(measurements(x))
            z=result['x'];signal_scale=float(np.max(np.abs(x)))
            if signal_scale:
                xs,zs=x/signal_scale,z/signal_scale
                error=float(min(np.linalg.norm(zs-xs),np.linalg.norm(zs+xs))/np.linalg.norm(xs))
            else:
                error=float(np.linalg.norm(z))
            max_error=max(max_error,error);max_residual=max(max_residual,result['relative_residual'])
            branches[result['branch']]=branches.get(result['branch'],0)+1
            if error>1e-6:failures.append({'index':j,'relative_signal_error':error})
        except (RuntimeError,FloatingPointError) as exc:
            failures.append({'index':j,'error':str(exc)})
    return {'utc':datetime.now(timezone.utc).isoformat(),'seed':seed,
            'tested_vectors':len(vectors),'branches':branches,
            'maximum_relative_signal_error':max_error,'maximum_relative_measurement_residual':max_residual,
            'failures':failures,'status':'passed' if not failures else 'finite tests have failures',
            'scope':'Finite floating-point tests only; exact-arithmetic decoding proof in manuscript.'}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--measurements',help='JSON array of twelve real numbers')
    p.add_argument('--self-test',action='store_true')
    p.add_argument('--seed',type=int,default=0)
    p.add_argument('--count',type=int,default=200)
    p.add_argument('--out',type=Path,default=Path(__file__).with_name('decoder_verification.json'))
    args=p.parse_args()
    if args.self_test:
        report=self_test(args.seed,args.count)
        args.out.write_text(json.dumps(report,indent=2)+'\n')
        print(json.dumps(report,indent=2))
        if report['failures']:raise SystemExit(1)
    elif args.measurements is not None:
        result=decode(np.asarray(json.loads(args.measurements),dtype=float))
        result['x']=result['x'].tolist();print(json.dumps(result,indent=2))
    else:p.error('Choose --self-test or --measurements')

if __name__=='__main__':main()
