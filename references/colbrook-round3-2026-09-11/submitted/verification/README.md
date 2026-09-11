# Reproducing the supporting checks

Python 3.10 or later is required. The recorded run used Python 3.13.5, NumPy 2.3.5, SciPy 1.17.0, SymPy 1.14.0, and mpmath 1.3.0. These are observed execution-environment versions, not a claim that they are the latest releases.

From the package root:

```bash
python -m pip install -r verification/requirements.txt
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python verification/check_round3.py --output verification/check_results-rerun.json
python verification/stress_ie10.py --output verification/stress_ie10-rerun.json
python verification/odd_family.py --prime 1009 --kernel-output prime_1009_kernel.npy
```

On shells without the inline environment-variable syntax, set the variables separately or omit them. They control numerical-library parallelism, not the mathematics.

## Files and scope

`check_round3.py` checks the exact 3-by-3 cyclic-model pencil, a root-locus polynomial, the rational sign-family threshold, eigenpair identities, finite-difference derivatives, sampled root paths, finite-field integer identities, FFT formulas, and several small dense singular-value decompositions. Random seeds are fixed in the script.

`stress_ie10.py` uses 140 decimal digits for deterministic cases with highly uneven weights, closely clustered nodes, and nearly defective cyclic compressions. It also recomputes perturbed compressions to check derivatives by finite differences. These are high-precision floating-point diagnostics, not interval certificates.

`odd_family.py` is a reusable deterministic kernel generator. The p-by-p kernel specifies an order-p-squared matrix by A[g,h] = kernel[g-h] on the two-dimensional additive group. The full matrix is intentionally not formed for large p. A memory guard rejects excessively large kernel diagnostics, and a separate guard protects dense construction. The default example p = 1009 has matrix order 1,018,081, but stores only 1,018,081 kernel entries.

The family is a theorem for primes p >= 13, with the stated quantitative bound below square root two for primes p >= 361. Some smaller-prime examples are ill-conditioned or singular; the code includes them to check identities, not to assert an all-prime condition-number bound.

## What a passing run does not establish

It is not independent peer review, formal proof verification, a certified probability computation, or a floating-point eigenbasis algorithm with the manuscript's probability guarantee. A sampled polygonal root path can miss curvature or collisions and is not a proof of the continuous length bound. The uniform character-sum bound is an imported classical theorem, not a consequence of a finite FFT sweep.

The exact portions use symbolic algebra or finite-field integer calculations. All other reported eigenvalue, singular-value, derivative, and FFT errors are numerical diagnostics. Small differences between library versions are normal; a failing assertion should be investigated rather than silently relaxed.
