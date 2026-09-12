# Discovery code (not the proof checker)

Python, NumPy and SciPy are used for numerical discovery; the exact accepted-certificate verifier in the parent directory is standard-library-only.

Typical reconstruction from this directory:

```sh
OPENBLAS_NUM_THREADS=1 python mi15_facial.py --n 8 --K 6 --margin .01 --maxiter 3000
OPENBLAS_NUM_THREADS=1 python mi15_certify.py 8
```

The first command may warm-start from an existing NPZ file. Remove or rename that file to reproduce a zero-start run. L-BFGS trajectories may differ across libraries; identical discovery output is not needed because the archived rational certificates are verified exactly.

`mi15_gram.py` and `mi15_inspect.py` preserve the initial, unsuccessful unconstrained-face search. Its near-zero/negative eigenvalues are not proof data. `mi15_facial.py` solves the imposed kernel constraints exactly with Fraction arithmetic before numerical optimization. `mi15_certify.py` rationalizes independent parameters and constructs an integer-checkable positive-definiteness certificate.

A failed attempt to install an SDP modeling package was not used in obtaining these results; the actual search uses SciPy's L-BFGS-B optimizer and a negative-eigenvalue penalty.
