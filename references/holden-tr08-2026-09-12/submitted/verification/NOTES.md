# Verification record

## Recorded environment and commands

Python 3.13.5, NumPy 2.3.5, SciPy 1.17.0, SymPy 1.14.0; Linux.
The random seed is 20260912. Commands, from the archive root:

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 \
  python code/verify.py --output verification/checks.json
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 \
  python code/experiment.py --sizes 2000 10000 50000 \
  --sparsities 1 2 4 8 16 --repetitions 3 \
  --output verification/experiments.csv
```

## Algebraic and exact-enumeration checks

All assertions passed. The record in `checks.json` includes symbolic checks of
the tree Rayleigh quotient and the bulk bound; 328 exact hypergeometric
moment-generating-function comparisons; three exact row-tail covariance
computations; and an exhaustive nonbacktracking moment comparison.

The moment comparison enumerates 144 fixed-support signed matrices and all
729 iid ternary matrices at dimensions 3 by 2 and column sparsity 2. Integer
path sums are converted into exact rational expectations. For powers 1 to 5,
the fixed-support expectations are `6, 7/3, 1, 1/3, 1/8`; the pruned expectations
are `16/3, 19/9, 5/6, 5/18, 1/8`; the iid expectations are
`6, 8/3, 4/3, 16/27, 34/81`.

## Numerical checks

Sixty cancellation-tree examples with independently chosen signs and sixty
block-triangular examples passed their tests. The largest tree-quotient error
was approximately `4.45e-16`. A finite Ihara–Bass determinant test had error
approximately `2.01e-16`. These are floating-point residuals, not rigorous
interval enclosures.

## Finite random-matrix experiments

The CSV has 45 rows: three independent replicates at each pair of matrix size
`k in {2000, 10000, 50000}` and sparsity `d in {1, 2, 4, 8, 16}`. The number of
columns is always `k/100`. Each column is sampled with exactly `d` distinct
uniformly located entries and independent signs. This is not a Bernoulli-support
approximation.

The smallest singular value is estimated from the smallest Gram eigenvalue.
The unmodified eigenvalue and eigenpair residual are recorded. Tiny negative
eigenvalues caused by roundoff are clipped only when taking a square root;
the raw value remains in the CSV. An exact zero can also appear as a small
positive estimate, often of order `1e-8`, because the square root amplifies
roundoff near zero. These computations are not rank certificates.

For instance, the displayed sparse examples with `d=2` can have a comfortably
positive least singular value at every tested size even though fixed `d=2` is
asymptotically subthreshold. This is expected: the witness probability in the
necessity proof can have an extremely small constant, depending on the target
singular-value level. Practical finite dimensions do not certify the limiting
threshold. The experiments are supplied for model reproducibility and numerical
exploration, not as evidence replacing any proof step.
