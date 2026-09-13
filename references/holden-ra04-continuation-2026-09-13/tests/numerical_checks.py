#!/usr/bin/env python3
"""Optional floating-point graph diagnostics. No asymptotic claim is tested."""
from __future__ import annotations
import argparse,json,math
from pathlib import Path

def main():
    import numpy as np
    p=argparse.ArgumentParser();p.add_argument('--output',default='results/numerical_checks.json');p.add_argument('--seed',type=int,default=20260912);args=p.parse_args()
    rng=np.random.default_rng(args.seed);records=[]
    for b in (2,3,5):
      for t in (3,4,6):
        m=b*t;n=m+8;delta=.1;eta=delta/3;centers=4.**np.arange(t-1,-1,-1);beta=.75
        width_limit=beta*eta**1.5/(64*t*t*b*math.sqrt(m))
        for factor in (.2,1.,1.e4):
          w=width_limit*factor
          lam=np.concatenate([np.sort(c*(1+rng.uniform(-w,w,b)))[::-1] for c in centers])
          tail=np.linspace(.8,.05,n-m);H=rng.standard_normal((m,b));T=rng.standard_normal((n-m,b))
          ds=np.array([np.prod(centers[s]-np.delete(centers,s)) for s in range(t)])
          def basis(x):return np.array([np.prod(x-np.delete(centers,j)) for j in range(t)])
          C=np.vstack([np.kron(basis(x)/ds[i//b],H[i]) for i,x in enumerate(lam)])
          C0=np.zeros((m,m))
          for s in range(t):C0[s*b:(s+1)*b,s*b:(s+1)*b]=H[s*b:(s+1)*b]
          R0=np.linalg.inv(C0); E=C-C0
          R=np.linalg.solve(C,np.eye(m));Dinv=np.diag(np.repeat(1/ds,b))
          Tail=np.vstack([np.kron(basis(x),g) for x,g in zip(tail,T)])
          F=Tail@R@Dinv
          limit=32*b*t**1.5*math.sqrt(n-m)*eta**(-1.5)*((1+w)/beta)**(t-1)
          records.append({'b':b,'t':t,'n':n,'width':w,'width_limit':width_limit,
                          'within_proved_width':factor<=1.,'perturbation_norm':float(np.linalg.norm(E@R0,2)),
                          'head_identity_residual':float(np.linalg.norm(C@R-np.eye(m))),
                          'graph_frobenius':float(np.linalg.norm(F,'fro')),'stated_high_probability_bound':limit})
    out=Path(args.output);out.parent.mkdir(parents=True,exist_ok=True)
    out.write_text(json.dumps({'seed':args.seed,'numpy_version':np.__version__,'records':records,
                              'limits':'Floating-point diagnostics only. Cases outside the width hypothesis do not validate a broader theorem.'},indent=2)+'\n')
    print(json.dumps({'records':len(records),'output':str(out)}))
if __name__=='__main__':main()
