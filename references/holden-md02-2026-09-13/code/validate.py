from __future__ import annotations
from pathlib import Path
import json, math, traceback
import numpy as np
from fixed_point import *

ROOT = Path(__file__).resolve().parents[1]
RESULTS = ROOT / 'results'; RESULTS.mkdir(exist_ok=True)

def main():
    report = {'status': 'RUNNING', 'exact_proofs_are_in_manuscript': True,
              'floating_point_checks_are_not_proofs': True}
    try:
        masks = 0; moment_rows = []; algebra_error = 0.0
        for n in range(2, 13):
            ss = [signs_from_mask(n, k) for k in range(2**(n//2))]
            masks += len(ss)
            for t in [1.0, float(n), float(n*n)]:
                m1 = m2 = 0.0
                for s in ss:
                    r = np.fft.ifft(s).real
                    algebra_error = max(algebra_error,
                        abs(float(np.sum(r))),
                        abs(float(np.dot(r,r)) - (n-1)/n))
                    u1 = picard(s,t,1); u2 = picard(s,t,2)
                    m1 += u1[0]**2; m2 += u2[0]**2
                m1 /= len(ss); m2 /= len(ss)
                a = 1 - t**-0.5
                assert n*m1 <= 2*a*a + 1e-9
                assert n*m2 <= 68*a*a + 1e-9
                moment_rows.append({'n':n,'t':t,'masks':len(ss),
                                    'n_E_u1_squared':n*m1,'n_E_u2_squared':n*m2})
        rng = np.random.default_rng(20260913)
        endpoint_rows=[]
        for n in list(range(2,9)) + [15,16,17,31,32]:
            samples = ([signs_from_mask(n,k) for k in range(2**(n//2))]
                       if n <= 8 else [sample_signs(n,rng) for _ in range(5)])
            for k,s in enumerate(samples):
                theta = theta_lp(s)
                for t in [float(n),float(n*n)]:
                    sol = numerical_fixed_point(s,t)
                    tol=1e-6*max(1,theta)
                    assert sol['theta_lower'] <= theta+tol
                    assert theta <= sol['theta_upper']+tol
                    p,q=sol['p'],sol['q']
                    assert abs(p.sum()-1)<1e-7 and abs(q.sum()-1)<1e-7
                    assert np.min(p)>0 and np.min(q)>0
                    ep=np.max(np.abs(np.fft.fft(p)[s == -1]), initial=0.)
                    eq=np.max(np.abs(np.fft.fft(q)[s == 1]), initial=0.)
                    assert max(ep,eq)<1e-7
                    sc=n*float(p[0])*float(q[0])
                    assert abs(sc-t/(t+n-1))<1e-7
                    other=numerical_fixed_point(-s,t)
                    complement_error=float(np.max(np.abs(sol['u']+other['u'])))
                    assert complement_error<1e-6
                    endpoint_rows.append({'n':n,'mask_index':k,'t':t,
                        'theta_lp':theta,'lower':sol['theta_lower'],
                        'upper':sol['theta_upper'],'residual':sol['residual'],
                        'complement_error':complement_error})
        mc=[]
        for n in [16,31,64,127]:
            vals=np.array([[math.sqrt(n)*picard(s,n*n,step)[0] for step in [1,2,3]]
                  for s in [sample_signs(n,rng) for _ in range(512)]])
            mc.append({'n':n,'samples':len(vals),'t':n*n,
                       'scaled_root_second_moments':np.mean(vals**2,axis=0).tolist()})
        report.update(status='PASS',enumerated_masks=masks,
            maximum_kernel_algebra_error=algebra_error,
            endpoint_checks=len(endpoint_rows),seed=20260913,
            limitations=['Monte Carlo means are not bounds.',
                         'Floating-point root solves are not interval certificates.',
                         'No test proves the asymptotic estimate for the converged root.'])
        (RESULTS/'enumerated_moments.json').write_text(json.dumps(moment_rows,indent=2))
        (RESULTS/'endpoint_checks.json').write_text(json.dumps(endpoint_rows,indent=2))
        (RESULTS/'monte_carlo.json').write_text(json.dumps(mc,indent=2))
    except Exception as e:
        report.update(status='FAIL',error=str(e),traceback=traceback.format_exc())
    (RESULTS/'validation_summary.json').write_text(json.dumps(report,indent=2))
    print(json.dumps(report,indent=2))
    return report['status']=='PASS'

if __name__=='__main__':
    raise SystemExit(0 if main() else 1)
