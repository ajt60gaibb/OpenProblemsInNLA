#!/usr/bin/env python3
"""Check examples of the TR-03 k=1 identity, not the full TR-03 problem."""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import numpy as np
import sympy as sp


def zero_diagonal_basis(H: np.ndarray) -> np.ndarray:
    """Numerical implementation of the induction in the mathematical note.

    H must be real symmetric and trace zero to floating-point accuracy.
    Returned columns are approximately orthonormal with zero H-Rayleigh quotient.
    """
    if H.ndim != 2 or H.shape[0] != H.shape[1]:
        raise ValueError('H must be square')
    n = H.shape[0]
    if n == 1:
        return np.ones((1,1))
    eigenvalues,U = np.linalg.eigh(H)
    lo,hi = eigenvalues[0],eigenvalues[-1]
    if max(abs(lo),abs(hi)) < 1e-13:
        return np.eye(n)
    if lo >= 0 or hi <= 0:
        raise ArithmeticError('Trace-zero sign condition lost numerically')
    a = np.sqrt(hi/(hi-lo)); b = np.sqrt(-lo/(hi-lo))
    first = a*U[:,0]+b*U[:,-1]
    complement = np.column_stack((-b*U[:,0]+a*U[:,-1],U[:,1:-1]))
    restriction = complement.T@H@complement
    return np.column_stack((first,complement@zero_diagonal_basis(restriction)))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path(__file__).with_name('TR03_checks.json'))
    args = parser.parse_args()
    V = sp.Matrix([[1/sp.sqrt(2),-1/sp.sqrt(2),0],
                   [1/sp.sqrt(6),1/sp.sqrt(6),-2/sp.sqrt(6)],
                   [1/sp.sqrt(3),1/sp.sqrt(3),1/sp.sqrt(3)]])
    assert sp.simplify(V.T*V) == sp.eye(3)
    Lambda = sp.diag(1,2,4); K = sp.simplify(V.T*Lambda*V)
    errors = [sp.simplify(sp.trace(K)-(K*K)[i,i]/K[i,i]) for i in range(3)]
    assert errors == [4,4,4]
    rng = np.random.default_rng(20260912)
    max_rel_error = 0.0; max_orth_error = 0.0; trials=0
    for n in [3,4,5,8,12,20,30]:
        for _ in range(12):
            lam = np.exp(rng.uniform(-3,3,size=n))
            S1 = sum(lam); c = np.dot(lam,lam)/S1
            h = lam*lam-c*lam
            H = np.diag(h/max(abs(h)))
            W = zero_diagonal_basis(H)
            Knum = (W.T*lam)@W
            residual = S1-np.sum(Knum*Knum,axis=0)/np.diag(Knum)
            expected = S1-c
            rel_error = float(max(abs(residual-expected))/S1)
            orth_error = float(np.linalg.norm(W.T@W-np.eye(n),2))
            max_rel_error=max(max_rel_error,rel_error)
            max_orth_error=max(max_orth_error,orth_error)
            assert rel_error < 1e-10 and orth_error < 1e-10
            randomW,_ = np.linalg.qr(rng.normal(size=(n,n)))
            randomK = (randomW.T*lam)@randomW
            random_residual = S1-np.sum(randomK*randomK,axis=0)/np.diag(randomK)
            assert min(random_residual) <= expected+1e-11*S1
            trials += 1
    report={'status':'PASS','scope':'Special case k=1 only; numerical tests are not proof certificates.',
            'exact_spectrum':[1,2,4],'exact_column_errors':[str(e) for e in errors],
            'seed':20260912,'numerical_spectra':trials,
            'maximum_relative_equalization_error':max_rel_error,
            'maximum_orthogonality_error':max_orth_error}
    args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__ == '__main__':
    main()
